//!  The cache is able to hold up to 2^32 elements.
//!
//! # Safety
//!  ## Read Operations:
//! - contains(*, false)
//!
//!  ## Read+Erase Operations:
//! - contains(*, true)
//!
//!  ## Erase Operations:
//! - allow_erase()
//!
//!  ## Write Operations:
//! - setup()
//! - setup_bytes()
//! - insert()
//! - please_keep()
//!
//!  ## Synchronization Free Operations:
//! - compute_indexes()
//!
//! ## User Must Guarantee:
//!
//! 1) Write Requires synchronized access (e.g., a lock)
//! 2) Read Requires no concurrent Write, synchronized with the last insert.
//! 3) Erase requires no concurrent Write, synchronized with last insert.
//! 4) An Erase caller must release all memory before allowing a new Writer.
//!
//!
//! # Note on function names:
//!   - The name "allow_erase" is used because the real discard happens later.
//!   - The name "please_keep" is used because elements may be erased anyways on insert.
//!
//! # Generic Types
//! * `Element` should be a movable and copyable type
//! * `Hash` should be a function/callable which takes a template parameter
//! hash_select and an Element and extracts a hash from it. Should return
//! high-entropy uint32_t hashes for `Hash h; h<0>(e) ... h<7>(e)`.
use super::bitpacked;
use super::bitpacked::{AtomicFlagsT, FlagsT};
/// Trait
pub trait SaltedHasher<Element> {
    fn new() -> Self;
    /// Should return 8 DoS resistant hash values
    /// hashes *should* be unique, but may also be non-unique with low probability
    fn hashes(&self, e: &Element) -> [u32; 8];
}

use std::marker::PhantomData;
pub struct Cache<Element, H>
where
    H: SaltedHasher<Element>,
{
    /// table stores all the elements
    table: Vec<[u32; 8]>,
    /// The bit_packed_atomic_flags array is marked mutable because we want
    /// garbage collection to be allowed to occur from const methods
    collection_flags: bitpacked::atomic::Flags,

    /// epoch_flags tracks how recently an element was inserted into
    /// the cache. true denotes recent, false denotes not-recent. See insert()
    /// method for full semantics.
    epoch_flags: bitpacked::non_atomic::Flags,

    /// epoch_heuristic_counter is used to determine when an epoch might be aged
    /// and an expensive scan should be done.  epoch_heuristic_counter is
    /// decremented on insert and reset to the new number of inserts which would
    /// cause the epoch to reach epoch_size when it reaches zero.
    epoch_heuristic_counter: usize,

    /// epoch_size is set to be the number of elements supposed to be in a
    /// epoch. When the number of non-erased elements in an epoch
    /// exceeds epoch_size, a new epoch should be started and all
    /// current entries demoted. epoch_size is set to be 45% of size because
    /// we want to keep load around 90%, and we support 3 epochs at once --
    /// one "dead" which has been erased, one "dying" which has been marked to be
    /// erased next, and one "living" which new inserts add to.
    epoch_size: usize,

    /// depth_limit determines how many elements insert should try to replace.
    /// Should be set to log2(n)*/
    depth_limit: u8,

    /// hash_function is a const instance of the hash function. It cannot be
    /// static or initialized at call time as it may have internal state (such as
    /// a nonce).
    hasher: H,
    pd: PhantomData<Element>,
}

impl<Element, HasherInstance> Cache<Element, HasherInstance>
where
    HasherInstance: SaltedHasher<Element>,
{
    /// returns a [usize, 8] of deterministic hashes derived from e
    ///
    /// compute_indexes is convenience for not having to write out this
    /// expression everywhere we use the hash values of an Element.
    ///
    /// # Arguments
    /// * `e` the element whose hashes will be returned
    /// # Notes
    /// We need to map the 32-bit input hash onto a hash bucket in a range [0, size) in a
    ///  manner which preserves as much of the hash's uniformity as possible.  Ideally
    ///  this would be done by bitmasking but the size is usually not a power of two.
    ///
    /// The naive approach would be to use a mod -- which isn't perfectly uniform but so
    ///  long as the hash is much larger than size it is not that bad.  Unfortunately,
    ///  mod/division is fairly slow on ordinary microprocessors (e.g. 90-ish cycles on
    ///  haswell, ARM doesn't even have an instruction for it.); when the divisor is a
    ///  constant the compiler will do clever tricks to turn it into a multiply+add+shift,
    ///  but size is a run-time value so the compiler can't do that here.
    ///
    /// One option would be to implement the same trick the compiler uses and compute the
    ///  constants for exact division based on the size, as described in "{N}-bit Unsigned
    ///  Division via {N}-bit Multiply-Add" by Arch D. Robison in 2005. But that code is
    ///  somewhat complicated and the result is still slower than other options:
    ///
    /// Instead we treat the 32-bit random number as a Q32 fixed-point number in the range
    ///  [0,1) and simply multiply it by the size.  Then we just shift the result down by
    ///  32-bits to get our bucket number.  The result has non-uniformity the same as a
    ///  mod, but it is much faster to compute. More about this technique can be found at
    ///  http://lemire.me/blog/2016/06/27/a-fast-alternative-to-the-modulo-reduction/
    ///
    /// The resulting non-uniformity is also more equally distributed which would be
    ///  advantageous for something like linear probing, though it shouldn't matter
    ///  one way or the other for a cuckoo table.
    ///
    /// The primary disadvantage of this approach is increased intermediate precision is
    ///  required but for a 32-bit random number we only need the high 32 bits of a
    ///  32*32->64 multiply, which means the operation is reasonably fast even on a
    ///  typical 32-bit processor.
    ///
    #[inline]
    fn compute_indexes(&self, es: &[u32; 8]) -> [usize; 8] {
        let mut hs = [0usize; 8];
        for (h, e) in hs.iter_mut().zip(es.iter()) {
            *h =
                (((((*e) as u64 & 0x00ffffffffu64) * (self.table.len() as u64)) >> 32u64) as u32) as usize;
        }
        // locations *should* be unique, but may also be non-unique with low probability
        // TODO: Analyze if it's OK to do something to guarantee they are unique (e.g.,
        // resampling?).
        hs
    }

    /// allow_erase marks the element at index n as discardable.

    /// # Safety
    /// Threadsafe
    /// without any concurrent insert.
    /// # Arguments
    /// * `n` the index to allow erasure of
    pub fn allow_erase(&self, n: usize) {
        self.collection_flags.bit_set(n);
    }

    /// please_keep marks the element at index n as an entry that should be kept.
    /// # Safety
    /// Threadsafe without any concurrent insert.
    /// # Arguments
    /// * `n` the index to prioritize keeping
    pub fn please_keep(&self, n: usize) {
        self.collection_flags.bit_unset(n);
    }

    ///  epoch_check handles the changing of epochs for elements stored in the
    ///  cache. epoch_check should be run before every insert.
    ///
    ///  First, epoch_check decrements and checks the cheap heuristic, and then does
    ///  a more expensive scan if the cheap heuristic runs out. If the expensive
    ///  scan succeeds, the epochs are aged and old elements are allow_erased. The
    ///  cheap heuristic is reset to retrigger after the worst case growth of the
    ///  current epoch's elements would exceed the epoch_size.
    fn epoch_check(&mut self) {
        if self.epoch_heuristic_counter != 0 {
            self.epoch_heuristic_counter -= 1;
            return;
        }
        // count the number of elements from the latest epoch which
        // have not been erased.
        let mut epoch_unused_count = 0;
        for i in 0..self.table.len() {
            epoch_unused_count +=
                (self.epoch_flags.bit_is_set(i) && !self.collection_flags.bit_is_set(i)) as usize;
        }
        // If there are more non-deleted entries in the current epoch than the
        // epoch size, then allow_erase on all elements in the old epoch (marked
        // false) and move all elements in the current epoch to the old epoch
        // but do not call allow_erase on their indices.
        if epoch_unused_count >= self.epoch_size {
            for i in 0..self.table.len() {
                if self.epoch_flags.bit_is_set(i) {
                    self.epoch_flags.bit_unset(i);
                } else {
                    self.allow_erase(i);
                }
            }
            self.epoch_heuristic_counter = self.epoch_size;
        } else {
            // reset the epoch_heuristic_counter to next do a scan when worst
            // case behavior (no intermittent erases) would exceed epoch size,
            // with a reasonable minimum scan size.
            // Ordinarily, we would have to sanity check std::min(epoch_size,
            // epoch_unused_count), but we already know that `epoch_unused_count
            // < epoch_size` in this branch
            self.epoch_heuristic_counter = std::cmp::max(
                1usize,
                std::cmp::max(
                    self.epoch_size / 16usize,
                    self.epoch_size - epoch_unused_count,
                ),
            );
        }
    }

    /// You must always construct a cache with some elements via a subsequent
    /// call to setup or setup_bytes, otherwise operations may segfault.
    pub fn empty() -> Self
    where
        HasherInstance: std::default::Default,
    {
        Cache {
            table: Vec::new(),
            collection_flags: bitpacked::atomic::Flags::new(0),
            epoch_flags: bitpacked::non_atomic::Flags::new(0),
            epoch_heuristic_counter: 0,
            epoch_size: 0,
            depth_limit: 0,
            hasher: std::default::Default::default(),
            pd: PhantomData,
        }
    }

    /// setup initializes the container to store no more than new_size
    /// elements.
    /// Returns the maximum number of elements storable
    ///
    /// # Safety
    /// setup should only be called once.
    ///
    /// # Arguments
    /// * `new_size` the desired number of elements to store. It can be any u32
    pub fn setup(&mut self, new_size: u32) -> usize
    where
        Element: std::default::Default + Clone,
    {
        // depth_limit must be at least one otherwise errors can occur.
        self.depth_limit = f64::log2(std::cmp::max(2, new_size) as f64) as u8;
        let size = std::cmp::max(2, new_size as usize);
        self.table
            .resize(size, std::default::Default::default());
        self.collection_flags.setup(size);
        self.epoch_flags.setup(size);
        // Set to 45% as described above
        self.epoch_size = std::cmp::max(1, (45 * size) / 100);
        // Initially set to wait for a whole epoch
        self.epoch_heuristic_counter = self.epoch_size;
        return size;
    }

    /// insert loops at most depth_limit times trying to insert a hash
    /// at various locations in the table via a variant of the Cuckoo Algorithm
    /// with eight hash locations.
    ///
    /// It drops the last tried element if it runs out of depth before
    /// encountering an open slot.
    ///
    /// Thus
    /// ```rust, ignore
    ///     let x = 1;
    ///     let mut c = cache::Cache::empty();
    ///     c.setup(100_000);
    ///     c.insert(x);
    ///     c.contains(x, false);
    /// ```
    /// is not guaranteed to return true.
    /// # Arguments
    /// * `e` the element to insert
    /// # Posconditions
    /// one of the following:
    ///   - All previously inserted elements and e are now in the table
    ///   - one previously inserted element is evicted from the table
    ///   -the entry attempted to be inserted is evicted.
    ///
    pub fn insert(&mut self, e: &Element) {
        self.epoch_check();
        let hs = self.hasher.hashes(e);
        let idxs = self.compute_indexes(&hs);
        // Make sure we have not already inserted this element
        // If we have, make sure that it does not get deleted
        for idx in idxs.iter() {
            if self.table[*idx] == hs {
                self.please_keep(*idx);
                self.epoch_flags.bit_set(*idx);
                return;
            }
        }
        self.insert_inner(hs, idxs[7], true, self.depth_limit);
    }
    fn insert_inner(&mut self, mut e: [u32; 8], last_idx: usize, last_epoch: bool, depth: u8) {
        if depth == 0 {
            return;
        }
        let idxs = self.compute_indexes(&e);
        // First try to insert to an empty slot, if one exists
        for loc in idxs.iter() {
            if !self.collection_flags.bit_is_set(*loc) {
                continue;
            }
            self.table[*loc] = e;
            self.please_keep(*loc);
            self.epoch_flags.bit_set_to(*loc, last_epoch);
            return;
        }
        /* Swap with the element at the location that was
         * not the last one looked at. Example:
         *
         * 1) On first call, last_idx = idxs[7], find returns last, so
         *    last_idx defaults to idxs[0].
         * 2) On further iterations, where last_idx == idxs[k], last_idx will
         *    go to idxs[k+1 % 8], i.e., next of the 8 indices wrapping around
         *    to 0 if needed.
         *
         * This prevents moving the element we just put in.
         *
         * The swap is not a move -- we must switch onto the evicted element
         * for the next iteration.
         */
        let mut idxs_iter = idxs.iter().cycle();
        idxs_iter.position(|el| *el == last_idx);
        let next_loc = *idxs_iter.next().expect("Critical Invariant Broken");
        std::mem::swap(&mut self.table[next_loc], &mut e);
        // Can't std::swap a std::vector<bool>::reference and a bool&.
        let next_epoch = self.epoch_flags.bit_is_set(next_loc);
        self.epoch_flags.bit_set_to(next_loc, last_epoch);
        self.insert_inner(e, next_loc, next_epoch, depth - 1);
    }

    /// contains iterates through the hash locations for a given element
    /// and checks to see if it is present.
    /// Returns true if the element is found, false otherwise
    ///
    /// contains does not check garbage collected state (in other words,
    /// garbage is only collected when the space is needed), so:
    ///
    /// ```rust, ignore
    ///     let mut c = cache::Cache::empty();
    ///     c.setup(100_000);
    ///     let x = 1;
    ///     c.insert(x);
    ///     if c.contains(x, true) {
    ///         c.contains(x, false)
    ///     } else {
    ///         /// with low probability, insert failed
    ///         true
    ///     }
    /// ```
    ///
    /// executed on a single thread will always return true!
    ///
    /// This is a great property for re-org performance for example.
    ///
    /// contains returns a bool set true if the element was found.
    /// # Arguments
    /// * `e` the element to check
    /// * `erase`
    ///
    /// # Postconditions
    /// if erase is true and the element is found, then the garbage collect
    /// flag is set
    pub fn contains(&mut self, e: &Element, erase: bool) -> bool
    where
        Element: Eq,
    {
        let hs = self.hasher.hashes(e);
        let locs = self.compute_indexes(&hs);
        for loc in locs.iter() {
            if self.table[*loc] == hs {
                if erase {
                    self.allow_erase(*loc);
                }
                return true;
            }
        }
        return false;
    }
}
