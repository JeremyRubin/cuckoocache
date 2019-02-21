// Copyright (c) 2016 Jeremy Rubin
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

//! CuckooCache crate provides a high performance cache primitive
//!
//! Summary:
//!
//! 1) bitpacked is bit-packed atomic flags for garbage collection
//! 2) cache is a cache which is performant in memory usage and lookup speed. It
//! is lockfree for erase operations. Elements are lazily erased on the next
//! insert.
//!
//! bit_packed::atomic::Flags implements a container for garbage collection flags
//! that is only thread unsafe on calls to setup. This class bit-packs collection
//! flags for memory efficiency.
//!
//! All operations are `Ordering::Relaxed` so external mechanisms must
//! ensure that writes and reads are properly synchronized.
//!
//! On Cache::setup(n), all bits up to n are marked as collected.
//!
//! Under the hood, because it is an 8-bit type, it makes sense to use a multiple
//! of 8 for setup, but it will be safe if that is not the case as well.

#[cfg(test)]
extern crate rand;
#[cfg(test)]
extern crate sha2;

/// Exports bitpacked atomic/non-atomic interfaces
pub mod bitpacked;

/// cache implements a cache with properties similar to a cuckoo-set
pub mod cache;
#[cfg(test)]
mod tests {
    use rand::prelude::*;
    use sha2::*;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    struct USizeHasher {
        salt: [u32; 8],
    }
    impl cache::SaltedHasher<usize> for USizeHasher {
        fn new() -> Self {
            USizeHasher {
                salt: [0, 1, 2, 3, 4, 5, 6, 7],
            }
        }
        fn hashes(&self, e: &usize) -> [u32; 8] {
            let mut r = self.salt;
            for l in r.iter_mut() {
                let mut h = DefaultHasher::new();
                l.hash(&mut h);
                e.hash(&mut h);
                *l = h.finish() as u32;
            }
            r
        }
    }
    impl Default for USizeHasher {
        fn default() -> Self {
            USizeHasher {
                salt: [0, 1, 2, 3, 4, 5, 6, 7],
            }
        }
    }

    struct TestHasher {
        salt: [u32; 8],
    }
    impl cache::SaltedHasher<[u32; 8]> for TestHasher {
        fn new() -> Self {
            Self { salt: random() }
        }
        fn hashes(&self, e: &[u32; 8]) -> [u32; 8] {
            let mut hasher = Sha256::new();
            hasher.input(unsafe { std::mem::transmute::<[u32; 8], [u8; 32]>(self.salt) });
            hasher.input(unsafe { std::mem::transmute::<[u32; 8], [u8; 32]>(*e) });
            let mut output = [0u32; 8];
            let u: &mut [u8; 32] = unsafe { std::mem::transmute(&mut output) };
            u[0..32].copy_from_slice(&hasher.result().as_slice());
            output
        }
    }
    impl Default for TestHasher {
        fn default() -> Self {
            TestHasher {
                salt: [0, 1, 2, 3, 4, 5, 6, 7],
            }
        }
    }
    use super::*;
    use cache::Cache;
    /// Unless something very unlikely happens here, this test passes
    #[test]
    fn basic_cache_works() {
        let mut c = cache::Cache::<usize, USizeHasher>::empty();
        c.setup(2);
        c.insert(&10);
        assert!(c.contains(&10usize, true));
        assert!(c.contains(&10usize, true));
        assert!(c.contains(&10usize, false));
        assert!(!c.contains(&11usize, false));
        c.insert(&11);
        assert!(c.contains(&11usize, false));
        c.insert(&12);
        assert!(c.contains(&11usize, false));
        assert!(!c.contains(&10usize, false));
        assert!(c.contains(&12usize, false));
        c.contains(&11, true);
        c.insert(&13);
        assert!(!c.contains(&11, false));
    }
    use std::sync::RwLock;

    /** Test Suite for CuckooCache
     *
     *  1) All tests should have a deterministic result (using insecure rand
     *  with deterministic seeds)
     *  2) Some test methods are templated to allow for easier testing
     *  against new versions / comparing
     *  3) Results should be treated as a regression test, i.e., did the behavior
     *  change significantly from what was expected. This can be OK, depending on
     *  the nature of the change, but requires updating the tests to reflect the new
     *  expected behavior. For example improving the hit rate may cause some tests
     *  using BOOST_CHECK_CLOSE to fail.
     *
     */

    /** insecure_GetRandHash fills in a uint256 from insecure_rand
     */
    fn insecure_GetRandHash() -> [u32; 8] {
        random()
    }

    /* Test that no values not inserted into the cache are read out of it.
     *
     * There are no repeats in the first 200000 insecure_GetRandHash calls
     */
    #[test]
    fn test_cuckoocache_no_fakes() {
        let mut cc = cache::Cache::<[u32; 8], TestHasher>::empty();
        let megabytes = 4;
        cc.setup_bytes(megabytes << 20);
        for i in 0..100000 {
            let v = random();
            assert!(!cc.contains(&v, false));
            cc.insert(&v);
        }
        for _ in 0..100000 {
            let v = random();
            assert!(!cc.contains(&v, false));
        }
    }

    /** This helper returns the hit rate when megabytes*load worth of entries are
     * inserted into a megabytes sized cache
     */
    fn test_cache(megabytes: usize, load: f64) -> f64 {
        let mut hashes = vec![];
        let mut set = Cache::<[u32; 8], TestHasher>::empty();
        let bytes = megabytes * (1 << 20);
        set.setup_bytes(bytes);
        let n_insert = (load * (bytes / std::mem::size_of::<[u32; 8]>()) as f64) as usize;
        for i in 0..n_insert {
            hashes.push(random())
        }
        /** Do the insert */
        hashes.iter().for_each(|h| set.insert(h));
        /** Count the hits */
        let count: usize = hashes.iter().map(|h| set.contains(h, false) as usize).sum();
        (count as f64) / (n_insert as f64)
    }

    /** The normalized hit rate for a given load.
     *
     * The semantics are a little confusing, so please see the below
     * explanation.
     *
     * Examples:
     *
     * 1) at load 0.5, we expect a perfect hit rate, so we multiply by
     * 1.0
     * 2) at load 2.0, we expect to see half the entries, so a perfect hit rate
     * would be 0.5. Therefore, if we see a hit rate of 0.4, 0.4*2.0 = 0.8 is the
     * normalized hit rate.
     *
     * This is basically the right semantics, but has a bit of a glitch depending on
     * how you measure around load 1.0 as after load 1.0 your normalized hit rate
     * becomes effectively perfect, ignoring freshness.
     */
    fn normalize_hit_rate(hits: f64, load: f64) -> f64 {
        hits * load.max(1.0)
    }

    /** Check the hit rate on loads ranging from 0.1 to 2.0 */
    #[test]
    fn cuckoocache_hit_rate_ok() {
        /** Arbitrarily selected Hit Rate threshold that happens to work for this test
         * as a lower bound on performance.
         */
        let hit_rate_thresh = 0.98;
        let megabytes = 4;
        for load in (0..)
            .map(|i| 0.1 * ((1 << i) as f64))
            .take_while(|&i| i < 2.0)
        {
            let hits = test_cache(megabytes, load);
            assert!(normalize_hit_rate(hits, load) > hit_rate_thresh);
        }
    }

    /** This helper checks that erased elements are preferentially inserted onto and
     * that the hit rate of "fresher" keys is reasonable*/
    fn test_cache_erase(megabytes: usize) {
        let load = 1.0;
        let mut hashes = vec![];
        let mut set = Cache::<[u32; 8], TestHasher>::empty();
        let bytes = megabytes * (1 << 20);
        set.setup_bytes(bytes);
        let n_insert = (load * (bytes / std::mem::size_of::<[u32; 8]>()) as f64) as usize;
        for i in 0..n_insert {
            hashes.push(random())
        }

        /** Insert the first half */
        hashes[0..(n_insert / 2)].iter().for_each(|h| set.insert(h));
        /** Erase the first quarter */
        hashes[0..(n_insert / 4)].iter().for_each(|h| {
            set.contains(h, true);
        });
        /** Insert the second half */
        hashes[(n_insert / 2)..].iter().for_each(|h| set.insert(h));

        /** elements that we marked erased but that are still there */
        let count_erased_but_contained: usize = hashes[..(n_insert / 4)]
            .iter()
            .map(|h| set.contains(h, false) as usize)
            .sum();
        /** elements that we did not erase but are older */
        let count_stale: usize = hashes[(n_insert / 4)..(n_insert / 2)]
            .iter()
            .map(|h| set.contains(h, false) as usize)
            .sum();
        /** elements that were most recently inserted */
        let count_fresh: usize = hashes[(n_insert / 2)..]
            .iter()
            .map(|h| set.contains(h, false) as usize)
            .sum();

        let hit_rate_erased_but_contained =
            (count_erased_but_contained as f64) / ((n_insert as f64) / 4.0);
        let hit_rate_stale = (count_stale as f64) / ((n_insert as f64) / 4.0);
        let hit_rate_fresh = (count_fresh as f64) / ((n_insert as f64) / 2.0);

        // Check that our hit_rate_fresh is perfect
        assert_eq!(hit_rate_fresh, 1.0);
        // Check that we have a more than 2x better hit rate on stale elements than
        // erased elements.
        assert!(hit_rate_stale > 2.0 * hit_rate_erased_but_contained);
    }

    #[test]
    fn cuckoocache_erase_ok() {
        let megabytes = 4;
        test_cache_erase(megabytes);
    }
    fn test_cache_erase_parallel(megabytes: usize) {
        let load = 1;
        let mut hashes = vec![];
        let mut set = Cache::<[u32; 8], TestHasher>::empty();
        let bytes = megabytes * (1 << 20);
        set.setup_bytes(bytes);
        let n_insert = load * (bytes / std::mem::size_of::<[u32; 8]>());
        for _ in 0..n_insert {
            hashes.push(random())
        }

        /** Insert the first half */
        for hash in hashes.iter().take(n_insert / 2) {
            set.insert(hash);
        }

        /** Spin up 3 threads to run contains with erase.
         */
        use std::sync::Arc;
        let hashes = Arc::new(hashes);
        let mut set = Arc::new(set);
        let threads: Vec<_> = (0..3)
            .map(|x| {
                let hashes = hashes.clone();
                let set = set.clone();
                std::thread::spawn(move || {
                    /** Erase the first quarter */
                    let ntodo = (n_insert / 4) / 3;
                    let start = ntodo * x;
                    let end = ntodo * (x + 1);
                    for h in hashes[start..end].iter() {
                        set.contains(h, true);
                    }
                })
            })
            .collect();
        for thread in threads {
            thread.join();
        }

        /** Wait for all threads to finish
         */
        /** Grab lock to make sure we observe erases */
        /** Insert the second half */
        for hash in hashes.iter().skip(n_insert / 2) {
            Arc::get_mut(&mut set).map(|m| m.insert(hash));
        }

        /** elements that we marked erased but that are still there */
        let count_erased_but_contained: usize = hashes[..(n_insert / 4)]
            .iter()
            .map(|h| set.contains(h, false) as usize)
            .sum();
        /** elements that we did not erase but are older */
        let count_stale: usize = hashes[(n_insert / 4)..(n_insert / 2)]
            .iter()
            .map(|h| set.contains(h, false) as usize)
            .sum();
        /** elements that were most recently inserted */
        let count_fresh: usize = hashes[(n_insert / 2)..]
            .iter()
            .map(|h| set.contains(h, false) as usize)
            .sum();

        let hit_rate_erased_but_contained =
            (count_erased_but_contained as f64) / ((n_insert as f64) / 4.0);
        let hit_rate_stale = (count_stale as f64) / ((n_insert as f64) / 4.0);
        let hit_rate_fresh = (count_fresh as f64) / ((n_insert as f64) / 2.0);

        // Check that our hit_rate_fresh is perfect
        assert_eq!(hit_rate_fresh, 1.0);
        // Check that we have a more than 2x better hit rate on stale elements than
        // erased elements.
        assert!(hit_rate_stale > 2.0 * hit_rate_erased_but_contained);
    }
    #[test]
    fn cuckoocache_erase_parallel_ok() {
        let megabytes = 4;
        test_cache_erase_parallel(megabytes);
    }

    // block_activity models a chunk of network activity. n_insert elements are
    // adde to the cache. The first and last n/4 are stored for removal later
    // and the middle n/2 are not stored. This models a network which uses half
    // the signatures of recently (since the last block) added transactions
    // immediately and never uses the other half.
    struct block_activity {
        reads: Vec<[u32; 8]>,
    }
    impl block_activity {
        fn new(n_insert: usize, c: &mut Cache<[u32; 8], TestHasher>) -> block_activity {
            let mut reads = Vec::with_capacity(n_insert / 2);
            for i in 0..n_insert / 4 {
                reads.push(random());
                c.insert(reads.last().unwrap());
            }
            for i in 0..n_insert / 2 {
                c.insert(&random());
            }
            for i in 0..n_insert / 4 {
                reads.push(random());
                c.insert(reads.last().unwrap());
            }
            Self { reads }
        }
    }

    #[test]
    fn test_cache_generations() {
        // This test checks that for a simulation of network activity, the fresh hit
        // rate is never below 99%, and the number of times that it is worse than
        // 99.9% are less than 1% of the time.
        let min_hit_rate = 0.99;
        let tight_hit_rate = 0.999;
        let max_rate_less_than_tight_hit_rate = 0.01;
        // A cache that meets this specification is therefore shown to have a hit
        // rate of at least tight_hit_rate * (1 - max_rate_less_than_tight_hit_rate) +
        // min_hit_rate*max_rate_less_than_tight_hit_rate = 0.999*99%+0.99*1% == 99.89%
        // hit rate with low variance.

        let BLOCK_SIZE = 1000;
        // We expect window size 60 to perform reasonably given that each epoch
        // stores 45% of the cache size (~472k).
        let WINDOW_SIZE = 60;
        let POP_AMOUNT = (BLOCK_SIZE / WINDOW_SIZE) / 2;
        let load = 10;
        let megabytes = 4;
        let bytes = megabytes * (1 << 20);
        let n_insert = load * (bytes / std::mem::size_of::<[u32; 8]>());

        let mut set = cache::Cache::<[u32; 8], TestHasher>::empty();
        set.setup_bytes(bytes);
        let mut last_few = std::collections::VecDeque::<block_activity>::new();
        let mut out_of_tight_tolerance = 0;
        let total = n_insert / BLOCK_SIZE;
        // we use the deque last_few to model a sliding window of blocks. at each
        // step, each of the last WINDOW_SIZE block_activities checks the cache for
        // POP_AMOUNT of the hashes that they inserted, and marks these erased.
        for i in 0..total {
            if (last_few.len() == WINDOW_SIZE) {
                last_few.pop_front();
            }
            last_few.push_back(block_activity::new(BLOCK_SIZE, &mut set));
            let mut count = 0;
            for act in last_few.iter_mut() {
                for _ in 0..POP_AMOUNT {
                    count += set.contains(&act.reads.pop().unwrap(), true) as usize;
                }
            }
            // We use last_few.size() rather than WINDOW_SIZE for the correct
            // behavior on the first WINDOW_SIZE iterations where the deque is not
            // full yet.
            let hit = (count as f64) / ((last_few.len() * POP_AMOUNT) as f64);
            // Loose Check that hit rate is above min_hit_rate
            assert!(hit > min_hit_rate);
            // Tighter check, count number of times we are less than tight_hit_rate
            // (and implicitly, greater than min_hit_rate)
            out_of_tight_tolerance += (hit < tight_hit_rate) as usize;
        }
        // Check that being out of tolerance happens less than
        // max_rate_less_than_tight_hit_rate of the time
        assert!(
            (out_of_tight_tolerance as f64) / (total as f64) < max_rate_less_than_tight_hit_rate
        );
    }

}
