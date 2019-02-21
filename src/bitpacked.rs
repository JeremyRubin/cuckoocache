use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

pub trait FlagsT {
    const DEFAULT: bool;
    ///  constructor creates memory to sufficiently
    /// keep track of garbage collection information for size entries.
    ///
    /// # Arguments
    /// * `size` the number of elements to allocate space for
    ///
    /// # Postconditions
    /// * bit_set, bit_unset, and bit_is_set function properly forall x. x <
    /// size.
    /// * All calls to bit_is_set (without subsequent bit_unset) will return
    /// `Self::DEFAULT`.
    fn new(size: usize) -> Self;

    /// setup marks all entries and ensures that bit_packed_atomic_flags can store
    /// at least size entries
    ///
    /// # Arguments
    /// * `b` the number of elements to allocate space for
    /// # Postconditions
    /// * bit_set, bit_unset, and bit_is_set function properly forall x. x <
    /// b
    /// * All calls to bit_is_set (without subsequent bit_unset) will return
    /// `Self::DEFAULT`.
    fn setup(&mut self, b: usize);

    /// bit_set sets an entry as discardable.
    ///
    /// # Arguments
    /// * `s` the index of the entry to bit_set
    /// # Postconditions
    /// * immediately subsequent call (assuming proper external memory
    /// ordering) to bit_is_set(s) == true.
    fn bit_set(&mut self, s: usize);

    ///  bit_unset marks an entry as something that should not be overwritten
    ///
    /// # Arguments
    /// * `s` the index of the entry to bit_unset
    /// # Postconditions
    /// * immediately subsequent call (assuming proper external memory
    /// ordering) to bit_is_set(s) == false.
    fn bit_unset(&mut self, s: usize);

    /// bit_set_to sets an entry as specified.
    /// # Arguments
    /// * `s` the index of the entry to modify
    /// * `discardable` true does unset, false does set
    /// # Postconditions
    /// * immediately subsequent call (assuming proper external memory
    /// ordering) to bit_is_set(s) == true.
    fn bit_set_to(&mut self, s: usize, discardable: bool);

    fn bit_is_set(&self, s: usize) -> bool;
}

pub trait AtomicFlagsT: FlagsT {
    /// bit_set sets an entry as discardable.
    ///
    /// # Arguments
    /// * `s` the index of the entry to bit_set
    /// # Postconditions
    /// * immediately subsequent call (assuming proper external memory
    /// ordering) to bit_is_set(s) == true.
    fn bit_set(&self, s: usize);

    ///  bit_unset marks an entry as something that should not be overwritten
    ///
    /// # Arguments
    /// * `s` the index of the entry to bit_unset
    /// # Postconditions
    /// * immediately subsequent call (assuming proper external memory
    /// ordering) to bit_is_set(s) == false.
    fn bit_unset(&self, s: usize);
}

pub mod non_atomic {
    use super::*;
    type FlagType = u64;
    const WIDTH: usize = 8 * std::mem::size_of::<FlagType>();
    const NBITS: usize = (WIDTH).trailing_zeros() as usize;
    const MASK: usize = WIDTH - 1;
    pub struct Flags {
        mem: Vec<FlagType>,
    }
    impl FlagsT for Flags {
        const DEFAULT: bool = false;
        fn new(size: usize) -> Self {
            // pad out the size if needed
            let size = (size + MASK) / WIDTH;
            let mut s = Flags {
                mem: Vec::with_capacity(size),
            };
            s.mem.resize(size, 0);
            s
        }

        fn setup(&mut self, b: usize) {
            std::mem::swap(&mut self.mem, &mut Flags::new(b).mem);
        }

        fn bit_set(&mut self, s: usize) {
            self.mem[s >> NBITS] |= 1 << (s & MASK);
        }

        fn bit_unset(&mut self, s: usize) {
            self.mem[s >> NBITS] &= !(1 << (s & MASK));
        }

        fn bit_set_to(&mut self, s: usize, discardable: bool) {
            // clear the bit
            self.mem[s >> NBITS] &= !(1 << (s & MASK));
            // then set iff discardable
            self.mem[s >> NBITS] |= (1 << (s & MASK)) * (discardable as u64);
        }
        fn bit_is_set(&self, s: usize) -> bool {
            return ((1 << (s & MASK)) & self.mem[s >> NBITS]) != 0;
        }
    }
}

pub mod atomic {
    use super::*;
    type FlagType = AtomicUsize;
    const WIDTH: usize = 8 * std::mem::size_of::<FlagType>();
    const NBITS: usize = (WIDTH).trailing_zeros() as usize;
    const MASK: usize = WIDTH - 1;
    pub struct Flags {
        mem: Vec<FlagType>,
    }
    impl FlagsT for Flags {
        const DEFAULT: bool = true;
        fn new(size: usize) -> Self {
            // pad out the size if needed
            let size = (size + MASK) / WIDTH;
            let mut s = Flags {
                mem: Vec::with_capacity(size),
            };
            for _ in 0..size {
                s.mem.push(std::usize::MAX.into());
            }
            s
        }

        fn setup(&mut self, b: usize) {
            std::mem::swap(&mut self.mem, &mut Flags::new(b).mem);
        }

        fn bit_set(&mut self, s: usize) {
            self.mem[s >> NBITS].fetch_or(1 << (s & MASK), Ordering::Relaxed);
        }
        fn bit_unset(&mut self, s: usize) {
            self.mem[s >> NBITS].fetch_and(!(1 << (s & MASK)), Ordering::Relaxed);
        }
        fn bit_set_to(&mut self, s: usize, discardable: bool) {
            // clear the bit
            self.mem[s >> NBITS].fetch_and(!(1 << (s & MASK)), Ordering::Relaxed);
            // then set iff discardable
            self.mem[s >> NBITS].fetch_or(
                (1 << (s & MASK)) * (discardable as usize),
                Ordering::Relaxed,
            );
        }
        fn bit_is_set(&self, s: usize) -> bool {
            return ((1 << (s & MASK)) & self.mem[s >> NBITS].load(Ordering::Relaxed)) != 0;
        }
    }
    impl AtomicFlagsT for Flags {
        /// bit_set sets an entry as discardable.
        ///
        /// # Arguments
        /// * `s` the index of the entry to bit_set
        /// @post immediately subsequent call (assuming proper external memory
        /// ordering) to bit_is_set(s) == true.
        fn bit_set(&self, s: usize) {
            self.mem[s >> NBITS].fetch_or(1 << (s & MASK), Ordering::Relaxed);
        }

        ///  bit_unset marks an entry as something that should not be overwritten
        ///
        /// # Arguments
        /// * `s` the index of the entry to bit_unset
        /// @post immediately subsequent call (assuming proper external memory
        /// ordering) to bit_is_set(s) == false.
        fn bit_unset(&self, s: usize) {
            self.mem[s >> NBITS].fetch_and(!(1 << (s & MASK)), Ordering::Relaxed);
        }
    }
}
