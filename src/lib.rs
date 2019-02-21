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

/// Exports bitpacked atomic/non-atomic interfaces
pub mod bitpacked;

/// cache implements a cache with properties similar to a cuckoo-set
pub mod cache;
#[cfg(test)]
mod tests {
    struct USizeHasher {
        salt: [u32; 8],
    }
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
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
    use super::*;
    /// Unless something very unlikely happens here, this test passes
    #[test]
    fn it_works() {
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

}
