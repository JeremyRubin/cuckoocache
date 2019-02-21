# cuckoocache
This Library provides a cuckoocache data structure in rust, similar to the one used in Bitcoin.

Cuckoocache is a great candidate for a signature cache store.

 Summary:

 1) bitpacked is bit-packed atomic flags for garbage collection
 2) cache is a cache which is performant in memory usage and lookup speed. It
 is lockfree for erase operations. Elements are lazily erased on the next
 insert.

 bit_packed::atomic::Flags implements a container for garbage collection flags
 that is only thread unsafe on calls to setup. This class bit-packs collection
 flags for memory efficiency.

 All operations are `Ordering::Relaxed` so external mechanisms must
 ensure that writes and reads are properly synchronized.

 On Cache::setup(n), all bits up to n are marked as collected.

 Under the hood, because it is an 8-bit type, it makes sense to use a multiple
 of 8 for setup, but it will be safe if that is not the case as well.
