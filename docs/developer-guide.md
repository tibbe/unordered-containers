# Developer Guide

This guide is meant as an entry point for developer. It both gives the
philisophy behind the design of this package and some concrete details, such as
invariants.

## Why does this package exist?

This package exists to offer a different performance/functionality
trade-off vis-a-vis ordered container packages
(e.g. [containers](http://hackage.haskell.org/package/containers)). Hashing-based
data structures tend to be faster than comparison-based ones, at the cost of not
providing operations the rely on the data being ordered.

This means that this package must be faster than ordered containers, or there
would be no reason for it to exist, given that its functionality is a strict
subset of ordered containers. This might seem obvious, but the author has
rejected several proposals in the past (e.g. to switch to higher quality but
slower hash functions) that would have made unordered-containers too slow to
motivate its existance.

## A note on hash functions

While the [hashable](http://hackage.haskell.org/package/hashable) package is a
separate package, it was co-designed with this package. Its main role is to
support this package and not to provide good general purpose hash functions
(e.g. to use when fingerprinting a text file).

The hash functions used (by default) were picked to make data structures
fast. The actual functions used oftens surprise developers who have learned
about hashing during their studies but haven't looked at which functions are
actually used in practice.

For example, integers are hashed to themselves. This might seemed contrary to
what you might have learned about hashing (e.g. that you need avalanche
behavior; changing one bit of input changes half of the bits in the output). It
turns out that this isn't what typically is done in practice (take a little tour
of the various programming languages standard libraries to see this for
yourself). Hashing integers to themselves is both faster (i.e. free) and the
improved locality can be helpful given common input patterns.

Another interesting example of hashing is string hashing, where
[FNV](https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function)
is used. FNV is a decent hash function, but hash worse properties than say
[MurmurHash](https://en.wikipedia.org/wiki/MurmurHash). However, it's much
faster. The fact that it's faster is not obvious given the way hash function
performance is often quoted, namely by giving the average throughput on large
inputs. Most inputs (e.g. keys) aren't large, often no more than 10 characters
long. Hash functions typically have a start-up cost and many functions that have
high throughput (such as MurmurHash) are more expensive for short strings than
FNV.

### Security

There's an uncomfortable trade-off with regards to security threats posed by
e.g. denial of service attacks. Always using more secure hash function, like
[SipHash](https://en.wikipedia.org/wiki/SipHash), would provide security by
default. However, those functions would make the performance of the data
structures no better than that of ordered containers, which defeats the purpose
of this package.

Previous versions of this package tried to switch to SipHash (and a different
hash function for integers). Those changes eventually had to be rolled back
after failing to make a fast enough implementation (using SSE instructions where
possible) that also wasn't crashing on some platforms.

The current, someone frustrating, state is that you have to know which data
structures can be tampered with by users and either use SipHash just for those
or switch to ordered containers that don't have collision problems. This package
uses fast hash functions by default.

## Data structure design

The data structures are based on the
[hash array mapped trie (HAMT)](https://en.wikipedia.org/wiki/Hash_array_mapped_trie)
data structures. There are several persistent implementations of the HAMT,
including in Clojure and Scala.

The actual implementation is as follows:

``` haskell
data HashMap k v
    = Empty
    | BitmapIndexed !Bitmap !(A.Array (HashMap k v))
    | Leaf !Hash !(Leaf k v)
    | Full !(A.Array (HashMap k v))
    | Collision !Hash !(Leaf k v) !(Leaf k v) !(HashMap k v)
```

Here's a quick overview in order of simplicty:

 * `Empty` -- The empty map.
 * `Leaf` -- A key-value pair.
 * `Full` -- An array of *2^B* children. Given a key you can find the child it
   is part of by taking *B* bits of the hash value for the key and indexing into
   the key. Which bits to use depends on the tree level.
 * `BitmapIndexed` -- Similar to above except that the array is implemented as a
   sparse array (to avoid storing `Empty` values). A bitmask and popcount is
   used to convert from the index taken from the hash value, just like above, to
   the actual index in the array. This node gets upgraded to a `Full` node when
   it contains *2^B* elements.
 * `Collision` -- Twe key-value pairs that collide on the given hash, and a
   recursive hashmap where keys are hashed with a different salt.

The number of bits of the hash value to use at each level of the tree, *B*, is a
compiled time constant (i.e. 4). In general a larger *B* improves lookup
performance (shallower tree) but hurts modification (large nodes to copy when
updating the spine of the tree).

`Full` is just an optimized version of `BitmapIndexed` that allows us faster
indexing, faster copying on modification (given that its size is statically
know), and lower memory use.

`Collision` is a special case. The previous version used `Collision !Hash
!(A.Array (HashMap k v))` instead of `Collision !Hash !(Leaf k v) !(Leaf k v)
!(HashMap k v)`. As a result, hash-collisions would cause `O(number of
collisions)` insertion time. Because the currently used hash function is not
collision-resistant, it is cheap to make enough collisions to have this cause a
denial of service exploit. However, we can use the fact that `hashable` supports
salted hashing by default to alleviate at least some of this problem.  In the
current version, insertion time is not `O(number of collisions)` but `O(number
of consequtive levels of collision)`.  While this is not better in case all the
collisions also collide on all subsequent salts, it is likely that a collision
using one salt will not collide again on the next salt, so this approach is
faster in the common case of collisions.

## Why things are fast

Performance is largely dominated by memory layout and allocation. The code has
been carefully tuned by looking at the GHC core output and sometimes the
assembly output. In particular there's no unnecessary allocation in the most
important functions and the memory layout is about as good as we can get using
GHC.

Avoiding allocation is done by making things strict (laziness is the enemy of
predictable performance) and using `INLINABLE` to allow to be specialized at the
call site (so key and value arguments to functions are passed as values rather
than pointers to heap objects).

The main remaining bottlenecks are due to e.g. GHC not allowing us to unpack an
array into a constructor. Two examples: the `Full` constructor is a separate
heap object from the array it contains and the `Leaf` constructor contains
pointers to the key and value instead of unpacking them into the
constructor. There's nothing we can do about this at the moment.

## Backwards compatibility policy

We support the last 3 major GHC releases.
