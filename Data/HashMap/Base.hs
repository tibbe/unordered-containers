{-# LANGUAGE BangPatterns, CPP, DeriveDataTypeable, MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ >= 802
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UnboxedSums #-}
#endif
{-# OPTIONS_GHC -fno-full-laziness -funbox-strict-fields #-}

module Data.HashMap.Base
    (
      HashMap(..)
    , Leaf(..)

      -- * Construction
    , empty
    , singleton

      -- * Basic interface
    , null
    , size
    , equal1
    , equal2
    , cmp1
    , cmp2
    , member
    , lookup
    , lookupDefault
    , (!)
    , insert
    , insertWith
    , unsafeInsert
    , delete
    , adjust
    , update
    , alter
    , alterF

      -- * Combine
      -- ** Union
    , union
    , unionWith
    , unionWithKey
    , unions

      -- * Transformations
    , map
    , mapWithKey
    , traverseWithKey

      -- * Difference and intersection
    , difference
    , differenceWith
    , intersection
    , intersectionWith
    , intersectionWithKey

      -- * Folds
    , foldl'
    , foldlWithKey'
    , foldr
    , foldrWithKey

      -- * Filter
    , mapMaybe
    , mapMaybeWithKey
    , filter
    , filterWithKey

      -- * Conversions
    , keys
    , elems

      -- ** Lists
    , toList
    , fromList
    , fromListWith

      -- Internals used by the strict version or tests
    , Hash
    , Salt
    , Bitmap
    , bitmapIndexedOrFull
    , collision
    , hashWithSalt
    , defaultSalt
    , nextSalt
    , mask
    , index
    , bitsPerSubkey
    , fullNodeMask
    , sparseIndex
    , two
    , unionArrayBy
    , update16
    , update16M
    , update16With'
    , updateOrConcatWith
    , updateOrConcatWithKey
    , filterMapAux
    , equalKeys
    , equalKeys1
    , lookupWithRes
    , LookupRes(..)
    , insert'
    , delete'
    , lookup'
    , insertNewKey
    , insertKeyExists
    , deleteKeyExists
    , insertModifying
    , unconsA
    , UnconsA(..)
    , UnconsHM(..)
    , unconsHM
    , ptrEq
    , adjust#
    , isLeafOrCollision
    ) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>), (<*>), Applicative(pure))
import Data.Monoid (Monoid(mempty, mappend))
import Data.Traversable (Traversable(..))
import Data.Word (Word)
#endif
#if __GLASGOW_HASKELL__ >= 711
import Data.Semigroup (Semigroup((<>)))
#endif
import Control.DeepSeq (NFData(rnf))
import Control.Monad.ST (ST)
import Data.Bits ((.&.), (.|.), complement, popCount)
import Data.Data hiding (Typeable)
import qualified Data.Foldable as Foldable
import qualified Data.List as L
import GHC.Exts ((==#), build, reallyUnsafePtrEquality#)
import Prelude hiding (filter, foldr, lookup, map, null, pred)
import Text.Read hiding (step)

import qualified Data.HashMap.Array as A
import qualified Data.Hashable as H
import Data.Hashable (Hashable)
import Data.HashMap.Unsafe (runST)
import Data.HashMap.UnsafeShift (unsafeShiftL, unsafeShiftR)
import Data.HashMap.List (isPermutationBy, unorderedCompare)
import Data.Typeable (Typeable)

import GHC.Exts (isTrue#)
import qualified GHC.Exts as Exts

#if MIN_VERSION_base(4,9,0)
import Data.Functor.Classes
#endif

#if MIN_VERSION_hashable(1,2,5)
import qualified Data.Hashable.Lifted as H
#endif

#if __GLASGOW_HASKELL__ >= 802
import GHC.Exts (TYPE)
#endif

#if MIN_VERSION_base(4,8,0)
import Data.Functor.Identity (Identity (..))
#endif
import Control.Applicative (Const (..))
import Data.Coerce (coerce)
import Data.Function (on)

-- | A set of values.  A set cannot contain duplicate values.
------------------------------------------------------------------------

-- | Convenience function.  Compute a hash value for the given value with a given salt.
hashWithSalt :: H.Hashable a => Salt -> a -> Hash
hashWithSalt s v = fromIntegral $ H.hashWithSalt s v

data Leaf k v = L !k v
  deriving (Show, Eq)

instance (NFData k, NFData v) => NFData (Leaf k v) where
    rnf (L k v) = rnf k `seq` rnf v

-- Invariant: The length of the 1st argument to 'Full' is
-- 2^bitsPerSubkey

-- | A map from keys to values.  A map cannot contain duplicate keys;
-- each key can map to at most one value.
data HashMap k v
    = Empty
    | BitmapIndexed !Bitmap !(A.Array (HashMap k v))
    | Leaf !Hash !(Leaf k v)
    | Full !(A.Array (HashMap k v))
    | Collision !Hash !(Leaf k v) !(Leaf k v) !(HashMap k v)
      deriving (Typeable)

type role HashMap nominal representational

instance (NFData k, NFData v) => NFData (HashMap k v) where
    rnf Empty                   = ()
    rnf (BitmapIndexed _ ary)   = rnf ary
    rnf (Leaf _ l)              = rnf l
    rnf (Full ary)              = rnf ary
    rnf (Collision _ l1 l2 ary) = rnf l1 `seq` rnf l2 `seq` rnf ary

instance Functor (HashMap k) where
    fmap = map

instance Foldable.Foldable (HashMap k) where
    foldr = Data.HashMap.Base.foldr
    {-# INLINE foldr #-}
    foldl' = Data.HashMap.Base.foldl'
    {-# INLINE foldl' #-}
#if MIN_VERSION_base(4,8,0)
    null = Data.HashMap.Base.null
    {-# INLINE null #-}
    length = Data.HashMap.Base.size
    {-# INLINE length #-}
#endif

#if __GLASGOW_HASKELL__ >= 711
instance (Eq k, Hashable k) => Semigroup (HashMap k v) where
  (<>) = union
  {-# INLINE (<>) #-}
#endif

instance (Eq k, Hashable k) => Monoid (HashMap k v) where
  mempty = empty
  {-# INLINE mempty #-}
#if __GLASGOW_HASKELL__ >= 711
  mappend = (<>)
#else
  mappend = union
#endif
  {-# INLINE mappend #-}

instance (Data k, Data v, Eq k, Hashable k) => Data (HashMap k v) where
    gfoldl f z m   = z fromList `f` toList m
    toConstr _     = fromListConstr
    gunfold k z c  = case constrIndex c of
        1 -> k (z fromList)
        _ -> error "gunfold"
    dataTypeOf _   = hashMapDataType
    dataCast2 f    = gcast2 f

fromListConstr :: Constr
fromListConstr = mkConstr hashMapDataType "fromList" [] Prefix

hashMapDataType :: DataType
hashMapDataType = mkDataType "Data.HashMap.Base.HashMap" [fromListConstr]

type Hash   = Word
type Salt   = Int
type Bitmap = Word
type Shift  = Int

#if MIN_VERSION_base(4,9,0)
instance Show2 HashMap where
    liftShowsPrec2 spk slk spv slv d m =
        showsUnaryWith (liftShowsPrec sp sl) "fromList" d (toList m)
      where
        sp = liftShowsPrec2 spk slk spv slv
        sl = liftShowList2 spk slk spv slv

instance Show k => Show1 (HashMap k) where
    liftShowsPrec = liftShowsPrec2 showsPrec showList

instance (Eq k, Hashable k, Read k) => Read1 (HashMap k) where
    liftReadsPrec rp rl = readsData $
        readsUnaryWith (liftReadsPrec rp' rl') "fromList" fromList
      where
        rp' = liftReadsPrec rp rl
        rl' = liftReadList rp rl
#endif

instance (Eq k, Hashable k, Read k, Read e) => Read (HashMap k e) where
    readPrec = parens $ prec 10 $ do
      Ident "fromList" <- lexP
      xs <- readPrec
      return (fromList xs)

    readListPrec = readListPrecDefault

instance (Show k, Show v) => Show (HashMap k v) where
    showsPrec d m = showParen (d > 10) $
      showString "fromList " . shows (toList m)

instance Traversable (HashMap k) where
    traverse f = traverseWithKey (const f)
    {-# INLINABLE traverse #-}

#if MIN_VERSION_base(4,9,0)
instance Eq2 HashMap where
    liftEq2 = equal2

instance (Eq k, Hashable k) => Eq1 (HashMap k) where
    liftEq = equal1
#endif

instance (Eq k, Hashable k, Eq v) => Eq (HashMap k v) where
    (==) = equal1 (==)

-- We rely on there being no Empty constructors in the tree!
-- This ensures that two equal HashMaps will have the same
-- shape, modulo the order of entries in Collisions.
equal1 :: (Eq k, Hashable k)
       => (v -> v' -> Bool)
       -> HashMap k v -> HashMap k v' -> Bool
equal1 eq = go
  where
    go Empty Empty = True
    go (BitmapIndexed bm1 ary1) (BitmapIndexed bm2 ary2)
      = bm1 == bm2 && A.sameArray1 go ary1 ary2
    go (Leaf h1 l1) (Leaf h2 l2) = h1 == h2 && leafEq l1 l2
    go (Full ary1) (Full ary2) = A.sameArray1 go ary1 ary2
    go t1@(Collision h1 _ _ _) t2@(Collision h2 _ _ _) =
         h1 == h2
         && size t1 == size t2
         && foldrWithKey (\k v r -> maybe False (eq v) (lookup k t2) && r) True t1
    go _ _ = False

    leafEq (L k1 v1) (L k2 v2) = k1 == k2 && eq v1 v2

equal2 :: (k -> k' -> Bool) -> (v -> v' -> Bool)
      -> HashMap k v -> HashMap k' v' -> Bool
equal2 eqk eqv t1 t2 = go (toList' t1 []) (toList' t2 [])
  where
    -- If the two trees are the same, then their lists of 'Leaf's and
    -- 'Collision's read from left to right should be the same (modulo the
    -- order of elements in 'Collision').

    go (Leaf h1 l1 : tl1) (Leaf h2 l2 : tl2)
      | h1 == h2 &&
        leafEq l1 l2
      = go tl1 tl2
    go (Collision h1 (L k11 v11) (L k12 v12) hm1 : tl1) (Collision h2 (L k21 v21) (L k22 v22) hm2 : tl2)
      | h1 == h2 &&
        (size hm1 == size hm2) &&
        isPermutationBy (\(k1, v1) (k2, v2) -> eqk k1 k2 && eqv v1 v2)
          ((k11, v11) : (k12, v12) : toList hm1)
          ((k21, v21) : (k22, v22) : toList hm2)
      = go tl1 tl2
    go [] [] = True
    go _  _  = False

    leafEq (L k v) (L k' v') = eqk k k' && eqv v v'

#if MIN_VERSION_base(4,9,0)
instance Ord2 HashMap where
    liftCompare2 = cmp2

instance (Ord k, Hashable k) => Ord1 (HashMap k) where
    liftCompare = cmp1
#endif

-- | The order is total.
--
-- /Note:/ Because the hash is not guaranteed to be stable across library
-- versions, OSes, or architectures, neither is an actual order of elements in
-- 'HashMap' or an result of `compare`.is stable.
instance (Ord k, Hashable k, Ord v) => Ord (HashMap k v) where
    compare = cmp1 compare

cmp1 :: (Ord k, Hashable k) => (v -> v' -> Ordering)
    -> HashMap k v -> HashMap k v' -> Ordering
cmp1 cmpv t1 t2 = go (toList' t1 []) (toList' t2 [])
  where
    go (Leaf k1 l1 : tl1) (Leaf k2 l2 : tl2)
      = compare k1 k2 `mappend`
        leafCompare l1 l2 `mappend`
        go tl1 tl2
    go (Collision h1 (L k11 v11) (L k12 v12) hm1 : tl1) (Collision h2 (L k21 v21) (L k22 v22) hm2 : tl2)
      = compare h1 h2 `mappend`
        compare (size hm1) (size hm2) `mappend`
        liftCompareList pairCompare
          -- We don't use sortOn because fst is cheap.
          (L.sortBy (compare `on` fst) $
            (k11, v11) : (k12, v12) : toList hm1)
          (L.sortBy (compare `on` fst) $
            (k21, v21) : (k22, v22) : toList hm2) `mappend`
        go tl1 tl2
    go (Leaf _ _ : _) (Collision _ _ _ _ : _) = LT
    go (Collision _ _ _ _ : _) (Leaf _ _ : _) = GT
    go [] [] = EQ
    go [] _  = LT
    go _  [] = GT
    go _ _ = error "cmp2: Should never happen, toList' includes non Leaf / Collision"

    leafCompare (L k v) (L k' v') = compare k k' `mappend` cmpv v v'
    pairCompare (k1, v1) (k2, v2) = (k1 `compare` k2) `mappend` (v1 `cmpv` v2)

-- Our own copy of liftCompare for lists.
liftCompareList :: (a -> b -> Ordering) -> [a] -> [b] -> Ordering
liftCompareList _ [] [] = EQ
liftCompareList _ [] _ = LT
liftCompareList _ _ [] = GT
liftCompareList cmp (x : xs) (y : ys) = cmp x y `mappend` liftCompareList cmp xs ys

cmp2 :: (k -> k' -> Ordering) -> (v -> v' -> Ordering)
    -> HashMap k v -> HashMap k' v' -> Ordering
cmp2 cmpk cmpv t1 t2 = go (toList' t1 []) (toList' t2 [])
  where
    go (Leaf k1 l1 : tl1) (Leaf k2 l2 : tl2)
      = compare k1 k2 `mappend`
        leafCompare l1 l2 `mappend`
        go tl1 tl2
    go (Collision h1 (L k11 v11) (L k12 v12) hm1 : tl1) (Collision h2 (L k21 v21) (L k22 v22) hm2 : tl2)
      = compare h1 h2 `mappend`
        compare (size hm1) (size hm2) `mappend`
        unorderedCompare (\(k1, v1) (k2, v2) -> (k1 `cmpk` k2) `mappend` (v1 `cmpv` v2))
          ((k11, v11) : (k12, v12) : toList hm1)
          ((k21, v21) : (k22, v22) : toList hm2) `mappend`
        go tl1 tl2
    go (Leaf _ _ : _) (Collision _ _ _ _ : _) = LT
    go (Collision _ _ _ _ : _) (Leaf _ _ : _) = GT
    go [] [] = EQ
    go [] _  = LT
    go _  [] = GT
    go _ _ = error "cmp2: Should never happen, toList' includes non Leaf / Collision"

    leafCompare (L k v) (L k' v') = cmpk k k' `mappend` cmpv v v'

-- Same as 'equal' but doesn't compare the values.
equalKeys1 :: (k -> k' -> Bool) -> HashMap k v -> HashMap k' v' -> Bool
equalKeys1 eq t1 t2 = go (toList' t1 []) (toList' t2 [])
  where
    go (Leaf k1 l1 : tl1) (Leaf k2 l2 : tl2)
      | k1 == k2 && leafEq l1 l2
      = go tl1 tl2
    go (Collision h1 (L k11 _) (L k12 _) hm1 : tl1) (Collision h2 (L k21 _) (L k22 _) hm2 : tl2)
      | h1 == h2 &&
        (size hm1 == size hm2) &&
        isPermutationBy eq
          (k11 : k12 : keys hm1)
          (k21 : k22 : keys hm2)
      = go tl1 tl2
    go [] [] = True
    go _  _  = False

    leafEq (L k _) (L k' _) = eq k k'

-- Same as 'equal1' but doesn't compare the values.
equalKeys :: Eq k => HashMap k v -> HashMap k v' -> Bool
equalKeys = go
  where
    go :: Eq k => HashMap k v -> HashMap k v' -> Bool
    go Empty Empty = True
    go (BitmapIndexed bm1 ary1) (BitmapIndexed bm2 ary2)
      = bm1 == bm2 && A.sameArray1 go ary1 ary2
    go (Leaf h1 l1) (Leaf h2 l2) = h1 == h2 && leafEq l1 l2
    go (Full ary1) (Full ary2) = A.sameArray1 go ary1 ary2
    go t1@(Collision h1 _ _ _) t2@(Collision h2 _ _ _)
      = h1 == h2
        && size t1 == size t2
        && L.foldr (\k r -> (k `elem` (keys t2)) && r) True (keys t1)
    go _ _ = False

    leafEq (L k1 _) (L k2 _) = k1 == k2

#if MIN_VERSION_hashable(1,2,5)
instance H.Hashable2 HashMap where
    liftHashWithSalt2 hk hv salt hm = go salt (toList' hm [])
      where
        -- go :: Int -> [HashMap k v] -> Int
        go s [] = s
        go s (Leaf _ l : tl)
          = s `hashLeafWithSalt` l `go` tl
        -- For collisions we hashmix hash value
        -- and then array of values' hashes sorted
        go s (Collision _ l1 l2 hm' : tl)
          = collisionHash l1 l2 hm' s `go` tl
        go s (_ : tl) = s `go` tl

        collisionHash (L k1 v1) (L k2 v2) hm' s
                = L.foldl' H.hashWithSalt s
                $ L.sort . L.map (\(k, v) -> (s `hk` k) `hv` v)
                $ (k1, v1) : (k2, v2) : toList hm'

        -- hashLeafWithSalt :: Int -> Leaf k v -> Int
        hashLeafWithSalt s (L k v) = (s `hk` k) `hv` v

instance (Hashable k) => H.Hashable1 (HashMap k) where
    liftHashWithSalt = H.liftHashWithSalt2 H.hashWithSalt
#endif

instance (Hashable k, Hashable v) => Hashable (HashMap k v) where
    hashWithSalt salt hm = go salt (toList' hm [])
      where
        go :: Int -> [HashMap k v] -> Int
        go s [] = s
        go s (Leaf _ l : tl)
          = s `hashLeafWithSalt` l `go` tl
        -- For collisions we hashmix hash value
        -- and then array of values' hashes sorted
        go s (Collision _ l1 l2 hm' : tl)
          = collisionHash l1 l2 hm' s `go` tl
        go s (_ : tl) = s `go` tl

        collisionHash :: Leaf k v -> Leaf k v -> HashMap k v -> Int -> Int
        collisionHash (L k1 v1) (L k2 v2) hm' s
                = L.foldl' H.hashWithSalt s
                $ L.sort . L.map (H.hashWithSalt s)
                $ (k1, v1) : (k2, v2) : toList hm'

        hashLeafWithSalt :: Int -> Leaf k v -> Int
        hashLeafWithSalt s (L k v) = s `H.hashWithSalt` k `H.hashWithSalt` v

  -- Helper to get 'Leaf's as a list, leave collisions as-is.
toList' :: HashMap k v -> [HashMap k v] -> [HashMap k v]
toList' (BitmapIndexed _ ary)   a = A.foldr toList' a ary
toList' (Full ary)              a = A.foldr toList' a ary
toList' l@(Leaf _ _)            a = l : a
toList' (Collision h l1 l2 hm)  a = Collision h l1 l2 hm : a
toList' Empty                   a = a

-- Helper function to detect 'Leaf's and 'Collision's.
isLeafOrCollision :: HashMap k v -> Bool
isLeafOrCollision (Leaf {})      = True
isLeafOrCollision (Collision {}) = True
isLeafOrCollision _              = False

------------------------------------------------------------------------
-- * Construction

-- | /O(1)/ Construct an empty map.
empty :: HashMap k v
empty = Empty

-- | /O(1)/ Construct a map with a single element.
singleton :: (Hashable k) => k -> v -> HashMap k v
singleton k v = Leaf (hashWithSalt defaultSalt k) (L k v)

------------------------------------------------------------------------
-- * Basic interface

-- | /O(1)/ Return 'True' if this map is empty, 'False' otherwise.
null :: HashMap k v -> Bool
null Empty = True
null _   = False

-- | /O(n)/ Return the number of key-value mappings in this map.
size :: HashMap k v -> Int
size t = go t 0
  where
    go Empty                !n = n
    go (Leaf _ _)            n = n + 1
    go (BitmapIndexed _ ary) n = A.foldl' (flip go) n ary
    go (Full ary)            n = A.foldl' (flip go) n ary
    go (Collision _ _ _ hm)  n = go hm (n + 2)

-- | /O(log n)/ Return 'True' if the specified key is present in the
-- map, 'False' otherwise.
member :: (Eq k, Hashable k) => k -> HashMap k a -> Bool
member k m = case lookup k m of
    Nothing -> False
    Just _  -> True
{-# INLINABLE member #-}

-- | /O(log n)/ Return the value to which the specified key is mapped,
-- or 'Nothing' if this map contains no mapping for the key.
lookup :: (Eq k, Hashable k) => k -> HashMap k v -> Maybe v
#if __GLASGOW_HASKELL__ >= 802
-- GHC does not yet perform a worker-wrapper transformation on
-- unboxed sums automatically. That seems likely to happen at some
-- point (possibly as early as GHC 8.6) but for now we do it manually.
lookup k m = case lookup# k m of
  (# (# #) | #) -> Nothing
  (# | a #) -> Just a
{-# INLINE lookup #-}

lookup# :: (Eq k, Hashable k) => k -> HashMap k v -> (# (# #) | v #)
lookup# k m = lookupCont (\_ -> (# (# #) | #)) (\v -> (# | v #)) (hashWithSalt defaultSalt k) defaultSalt k m
{-# INLINABLE lookup# #-}

#else

lookup k m = lookupCont (\_ -> Nothing) (\v -> Just v) (hashWithSalt defaultSalt k) defaultSalt k m
{-# INLINABLE lookup #-}
#endif

-- | lookup' is a version of lookup that takes the hash separately.
-- It is used to implement alterF.
lookup' :: (Eq k, Hashable k) => Hash -> Salt -> k -> HashMap k v -> Maybe v
#if __GLASGOW_HASKELL__ >= 802
-- GHC does not yet perform a worker-wrapper transformation on
-- unboxed sums automatically. That seems likely to happen at some
-- point (possibly as early as GHC 8.6) but for now we do it manually.
-- lookup' would probably prefer to be implemented in terms of its own
-- lookup'#, but it's not important enough and we don't want too much
-- code.
lookup' h s k m = case lookupWithRes# h s k m of
  (# (# #) | #) -> Nothing
  (# | a #) -> Just a
{-# INLINE lookup' #-}
#else
lookup' h s k m = lookupCont (\_ -> Nothing) (\v -> Just v) h s k m
{-# INLINABLE lookup' #-}
#endif

-- The result of a lookup, keeping track of if a hash collision occured.
-- If a collision did not occur then it will have the Int value (-1).
data LookupRes a = Absent | Present a

-- Internal helper for lookup. This version takes the precomputed hash so
-- that functions that make multiple calls to lookup and related functions
-- (insert, delete) only need to calculate the hash once.
--
-- It is used by 'alterF' so that hash computation and key comparison only needs
-- to be performed once. With this information you can use the more optimized
-- versions of insert ('insertNewKey', 'insertKeyExists') and delete
-- ('deleteKeyExists')
--
-- Outcomes:
--   Key not in map           => Absent
--   Key in map               => Present v
--
-- TODO(syd): We could add some optimisation here where we optimise for the common case
-- where a collision is in the first two elements and not in the recursive HashMap.
-- This could mean turning 'Present a' into 'Present a ColPos' with
-- 'data ColPos = NoCollision | CollisionFirst | CollisionSecond | CollisionRest'
lookupWithRes :: (Eq k, Hashable k) => Hash -> Salt -> k -> HashMap k v -> LookupRes v
#if __GLASGOW_HASKELL__ >= 802
lookupWithRes h s k m = case lookupWithRes# h s k m of
  (# (# #) | #) -> Absent
  (# | a #) -> Present a
{-# INLINE lookupWithRes #-}

lookupWithRes# :: (Eq k, Hashable k) => Hash -> Salt -> k -> HashMap k v -> (# (# #) | v #)
lookupWithRes# h s k m =
    lookupCont (\_ -> (# (# #) | #)) (\v -> (# | v #)) h s k m
-- INLINABLE to specialize to the Eq instance.
{-# INLINABLE lookupWithRes# #-}

#else /* GHC < 8.2 so there are no unboxed sums */

lookupWithRes h s k m = lookupCont (\_ -> Absent) Present h s k m
{-# INLINABLE lookupWithRes #-}
#endif

-- A two-continuation version of lookupWithRes. This lets us
-- share source code between lookup and lookupWithRes without
-- risking any performance degradation.
--
-- The absent continuation has type @((# #) -> r)@ instead of just @r@
-- so we can be representation-polymorphic in the result type. Since
-- this whole thing is always inlined, we don't have to worry about
-- any extra CPS overhead.
lookupCont ::
#if __GLASGOW_HASKELL__ >= 802
  forall rep (r :: TYPE rep) k v.
#else
  forall r k v.
#endif
     (Eq k, Hashable k)
  => ((# #) -> r)    -- Absent continuation
  -> (v -> r) -- Present continuation
  -> Hash -- The hash of the key
  -> Salt -- The salt that was used to obtain that hash
  -> k -> HashMap k v -> r
lookupCont absent present !h0 !s0 !k0 !m0 = go h0 s0 k0 0 m0
  where
    go :: Eq k => Hash -> Salt -> k -> Int -> HashMap k v -> r
    go !_ !_ !_ !_ Empty = absent (# #)
    go h _ k _ (Leaf hx (L kx x))
        | h == hx && k == kx = present x
        | otherwise          = absent (# #)
    go h s k bs (BitmapIndexed b v)
        | b .&. m == 0 = absent (# #)
        | otherwise    =
            go h s k (bs+bitsPerSubkey) (A.index v (sparseIndex b m))
      where m = mask h bs
    go h s k bs (Full v) =
      go h s k (bs+bitsPerSubkey) (A.index v (index h bs))
    go h s k _ (Collision hx (L k1 v1) (L k2 v2) hmx)
        | h == hx   = case () of
          ()    | k == k1   -> present v1
                | k == k2   -> present v2
                | otherwise -> go (hashWithSalt (nextSalt s) k) (nextSalt s) k 0 hmx
        | otherwise = absent (# #)
{-# INLINE lookupCont #-}

-- | /O(log n)/ Return the value to which the specified key is mapped,
-- or the default value if this map contains no mapping for the key.
lookupDefault :: (Eq k, Hashable k)
              => v          -- ^ Default value to return.
              -> k -> HashMap k v -> v
lookupDefault def k t = case lookup k t of
    Just v -> v
    _      -> def
{-# INLINABLE lookupDefault #-}

-- | /O(log n)/ Return the value to which the specified key is mapped.
-- Calls 'error' if this map contains no mapping for the key.
(!) :: (Eq k, Hashable k) => HashMap k v -> k -> v
(!) m k = case lookup k m of
    Just v  -> v
    Nothing -> error "Data.HashMap.Base.(!): key not found"
{-# INLINABLE (!) #-}

infixl 9 !

-- | Create a 'Collision' value with two 'Leaf' values.
collision :: (Eq k, Hashable k) => Hash -> Salt -> Leaf k v -> Leaf k v -> HashMap k v
collision h _ l1 l2 = Collision h l1 l2 Empty
{-# INLINE collision #-}

-- These are taken from wikipedia:
-- https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function#FNV_hash_parameters
defaultSalt :: Int
#if WORD_SIZE_IN_BITS == 64
defaultSalt = 14695981039346656037 -- 0xcbf29ce484222325 in hex
#else
defaultSalt = 2166136261 -- 0x811c9dc5 in hex
#endif

nextSalt :: Salt -> Salt
nextSalt = (+1)

-- | Create a 'BitmapIndexed' or 'Full' node.
bitmapIndexedOrFull :: Bitmap -> A.Array (HashMap k v) -> HashMap k v
bitmapIndexedOrFull b ary
    | b == fullNodeMask = Full ary
    | otherwise         = BitmapIndexed b ary
{-# INLINE bitmapIndexedOrFull #-}

-- | /O(log n)/ Associate the specified value with the specified
-- key in this map.  If this map previously contained a mapping for
-- the key, the old value is replaced.
insert :: (Eq k, Hashable k) => k -> v -> HashMap k v -> HashMap k v
insert k v m = insert' (hashWithSalt defaultSalt k) defaultSalt k v m
{-# INLINABLE insert #-}

insert' :: (Eq k, Hashable k) => Hash -> Salt -> k -> v -> HashMap k v -> HashMap k v
insert' h0 s0 k0 v0 m0 = go h0 s0 k0 v0 0 m0
  where
    go :: (Eq k, Hashable k) => Hash -> Salt -> k -> v -> Int -> HashMap k v -> HashMap k v
    go !h !_ !k x !_ Empty = Leaf h (L k x)
    go h s k x bs t@(Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then if x `ptrEq` y
                         then t
                         else Leaf h (L k x)
                    else collision h s l (L k x)
        | otherwise = runST (two bs h k x hy ky y)
    go h s k x bs t@(BitmapIndexed b ary)
        | b .&. m == 0 =
            let !ary' = A.insert ary i $! Leaf h (L k x)
            in bitmapIndexedOrFull (b .|. m) ary'
        | otherwise =
            let !st  = A.index ary i
                !st' = go h s k x (bs+bitsPerSubkey) st
            in if st' `ptrEq` st
               then t
               else BitmapIndexed b (A.update ary i st')
      where m = mask h bs
            i = sparseIndex b m
    go h s k x bs t@(Full ary) =
        let !st  = A.index ary i
            !st' = go h s k x (bs+bitsPerSubkey) st
        in if st' `ptrEq` st
            then t
            else Full (update16 ary i st')
      where i = index h bs
    go h s k x bs t@(Collision hx l1@(L k1 v1) l2@(L k2 v2) hmx)
        | h == hx   =
          let go'
                | k == k1   = if x `ptrEq` v1 then t else Collision hx (L k x) l2 hmx
                | k == k2   = if x `ptrEq` v2 then t else Collision hx l1 (L k x) hmx
                | otherwise = Collision hx l1 l2 $ go (hashWithSalt (nextSalt s) k) (nextSalt s) k x 0 hmx
          in go'
        | otherwise = go h s k x bs $ BitmapIndexed (mask hx bs) (A.singleton t)
{-# INLINABLE insert' #-}

-- Insert optimized for the case when we know the key is not in the map.
--
-- It is only valid to call this when the key does not exist in the map.
--
-- We can skip:
--  - the key equality check on a Leaf
--  - check for its existence in the array for a hash collision
insertNewKey :: (Eq k, Hashable k) => Hash -> Salt -> k -> v -> HashMap k v -> HashMap k v
insertNewKey !h0 !s0 !k0 x0 !m0 = go h0 s0 k0 x0 0 m0
  where
    go !h _ !k x !_ Empty = Leaf h (L k x)
    go h s k x bs (Leaf hy l@(L ky y))
      | hy == h = collision h s l (L k x)
      | otherwise = runST (two bs h k x hy ky y)
    go h s k x bs (BitmapIndexed b ary)
        | b .&. m == 0 =
            let !ary' = A.insert ary i $! Leaf h (L k x)
            in bitmapIndexedOrFull (b .|. m) ary'
        | otherwise =
            let !st  = A.index ary i
                !st' = go h s k x (bs+bitsPerSubkey) st
            in BitmapIndexed b (A.update ary i st')
      where m = mask h bs
            i = sparseIndex b m
    go h s k x bs (Full ary) =
        let !st  = A.index ary i
            !st' = go h s k x (bs+bitsPerSubkey) st
        in Full (update16 ary i st')
      where i = index h bs
    go h s k x bs t@(Collision hx l1 l2 hmx)
        | h == hx   = Collision hx l1 l2 $ go (hashWithSalt (nextSalt s) k) (nextSalt s) k x 0 hmx
        | otherwise =
            go h s k x bs $ BitmapIndexed (mask hx bs) (A.singleton t)
{-# NOINLINE insertNewKey #-}


-- Insert optimized for the case when we know the key is in the map.
--
-- We can skip the key equality check on a Leaf because we know the leaf must be
-- for this key. We still need to do the equality check in case of collisions.
insertKeyExists :: (Eq k, Hashable k) => Hash -> Salt -> k -> v -> HashMap k v -> HashMap k v
insertKeyExists !h0 !s0 !k0 x0 !m0 = go h0 s0 k0 x0 0 m0
  where
    go !h _ !k x !_s (Leaf _hy _kx)
        = Leaf h (L k x)
    go h s k x bs (BitmapIndexed b ary)
        | b .&. m == 0 =
            let !ary' = A.insert ary i $ Leaf h (L k x)
            in bitmapIndexedOrFull (b .|. m) ary'
        | otherwise =
            let !st  = A.index ary i
                !st' = go h s k x (bs+bitsPerSubkey) st
            in BitmapIndexed b (A.update ary i st')
      where m = mask h bs
            i = sparseIndex b m
    go h s k x bs (Full ary) =
        let !st  = A.index ary i
            !st' = go h s k x (bs+bitsPerSubkey) st
        in Full (update16 ary i st')
      where i = index h bs
    go _ s k x _ t@(Collision hx l1@(L k1 v1) l2@(L k2 v2) hmx)
        | k == k1   = if x `ptrEq` v1 then t else Collision hx (L k x) l2 hmx
        | k == k2   = if x `ptrEq` v2 then t else Collision hx l1 (L k x) hmx
        | otherwise = Collision hx l1 l2 $ go (hashWithSalt (nextSalt s) k) (nextSalt s) k x 0 hmx
    go _ _ _ _ _ Empty = Empty -- error "Internal error: go Empty"

{-# NOINLINE insertKeyExists #-}

-- | In-place update version of insert
unsafeInsert :: (Eq k, Hashable k) => k -> v -> HashMap k v -> HashMap k v
unsafeInsert k0 v0 m0 = runST (go h0 s0 k0 v0 0 m0)
  where
    h0 = hashWithSalt s0 k0
    s0 = defaultSalt
    go !h !_ !k x !_ Empty = return $! Leaf h (L k x)
    go h s k x bs t@(Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then if x `ptrEq` y
                         then return t
                         else return $! Leaf h (L k x)
                    else return $! collision h s l (L k x)
        | otherwise = two bs h k x hy ky y
    go h s k x bs t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insertM ary i $! Leaf h (L k x)
            return $! bitmapIndexedOrFull (b .|. m) ary'
        | otherwise = do
            st <- A.indexM ary i
            st' <- go h s k x (bs+bitsPerSubkey) st
            A.unsafeUpdateM ary i st'
            return t
      where m = mask h bs
            i = sparseIndex b m
    go h s k x bs t@(Full ary) = do
        st <- A.indexM ary i
        st' <- go h s k x (bs+bitsPerSubkey) st
        A.unsafeUpdateM ary i st'
        return t
      where i = index h bs
    go h s k x bs t@(Collision hx l1@(L k1 v1) l2@(L k2 v2) hmx)
        | h == hx   =
          let go'
                | k == k1   = return $! if x `ptrEq` v1 then t else Collision hx (L k x) l2 hmx
                | k == k2   = return $! if x `ptrEq` v2 then t else Collision hx l1 (L k x) hmx
                | otherwise = Collision hx l1 l2 <$> go (hashWithSalt (nextSalt s) k) (nextSalt s) k x 0 hmx
          in go'
        | otherwise = go h s k x bs $ BitmapIndexed (mask hx bs) (A.singleton t)
{-# INLINABLE unsafeInsert #-}

-- | Create a map from two key-value pairs which hashes don't collide.
two :: Shift -> Hash -> k -> v -> Hash -> k -> v -> ST s (HashMap k v)
two = go
  where
    go s h1 k1 v1 h2 k2 v2
        | bp1 == bp2 = do
            st <- go (s+bitsPerSubkey) h1 k1 v1 h2 k2 v2
            ary <- A.singletonM st
            return $! BitmapIndexed bp1 ary
        | otherwise  = do
            mary <- A.new 2 $ Leaf h1 (L k1 v1)
            A.write mary idx2 $ Leaf h2 (L k2 v2)
            ary <- A.unsafeFreeze mary
            return $! BitmapIndexed (bp1 .|. bp2) ary
      where
        bp1  = mask h1 s
        bp2  = mask h2 s
        idx2 | index h1 s < index h2 s = 1
             | otherwise               = 0
{-# INLINE two #-}

-- | /O(log n)/ Associate the value with the key in this map.  If
-- this map previously contained a mapping for the key, the old value
-- is replaced by the result of applying the given function to the new
-- and old value.  Example:
--
-- > insertWith f k v map
-- >   where f new old = new + old
insertWith :: (Eq k, Hashable k) => (v -> v -> v) -> k -> v -> HashMap k v
            -> HashMap k v
-- We're not going to worry about allocating a function closure
-- to pass to insertModifying. See comments at 'adjust'.
insertWith f k new m = insertModifying new (\old -> (# f new old #)) k m
{-# INLINE insertWith #-}

-- | @insertModifying@ is a lot like insertWith; we use it to implement alterF.
-- It takes a value to insert when the key is absent and a function
-- to apply to calculate a new value when the key is present. Thanks
-- to the unboxed unary tuple, we avoid introducing any unnecessary
-- thunks in the tree.
insertModifying :: (Eq k, Hashable k) => v -> (v -> (# v #)) -> k -> HashMap k v
            -> HashMap k v
insertModifying x f k0 m0 = go h0 s0 k0 0 m0
  where
    !h0 = hashWithSalt s0 k0
    !s0 = defaultSalt
    go !h _ !k !_ Empty = Leaf h (L k x)
    go h s k bs t@(Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then case f y of
                      (# v' #) | ptrEq y v' -> t
                               | otherwise -> Leaf h (L k (v'))
                    else collision h s l (L k x)
        | otherwise = runST (two bs h k x hy ky y)
    go h s k bs t@(BitmapIndexed b ary)
        | b .&. m == 0 =
            let ary' = A.insert ary i $! Leaf h (L k x)
            in bitmapIndexedOrFull (b .|. m) ary'
        | otherwise =
            let !st   = A.index ary i
                !st'  = go h s k (bs+bitsPerSubkey) st
                ary'  = A.update ary i $! st'
            in if ptrEq st st'
               then t
               else BitmapIndexed b ary'
      where m = mask h bs
            i = sparseIndex b m
    go h s k bs t@(Full ary) =
        let !st   = A.index ary i
            !st'  = go h s k (bs+bitsPerSubkey) st
            ary' = update16 ary i $! st'
        in if ptrEq st st'
           then t
           else Full ary'
      where i = index h bs
    go h s k bs t@(Collision hx l1@(L k1 v1) l2@(L k2 v2) hmx)
        | h == hx   =
           let go'
                 | k == k1   =
                    case f v1 of
                      (# v' #) | ptrEq v1 v' -> t
                               | otherwise -> Collision hx (L k v') l2 hmx
                 | k == k2   =
                    case f v2 of
                      (# v' #) | ptrEq v2 v' -> t
                               | otherwise -> Collision hx l1 (L k v') hmx
                 | otherwise = Collision hx l1 l2 $ go (hashWithSalt (nextSalt s) k) (nextSalt s) k 0 hmx
           in go'
        | otherwise = go h s k bs $ BitmapIndexed (mask hx bs) (A.singleton t)
{-# INLINABLE insertModifying #-}

-- | In-place update version of insertWith
unsafeInsertWith :: forall k v. (Eq k, Hashable k)
                 => (v -> v -> v) -> k -> v -> HashMap k v
                 -> HashMap k v
unsafeInsertWith f k0 v0 m0 = runST (go h0 s0 k0 v0 0 m0)
  where
    h0 = hashWithSalt s0 k0
    s0 = defaultSalt
    go :: Hash -> Salt -> k -> v -> Shift -> HashMap k v -> ST s (HashMap k v)
    go !h _ !k x !_ Empty = return $! Leaf h (L k x)
    go h s k x bs (Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then return $! Leaf h (L k (f x y))
                    else return $! collision h s l (L k x)
        | otherwise = two bs h k x hy ky y
    go h s k x bs t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insertM ary i $! Leaf h (L k x)
            return $! bitmapIndexedOrFull (b .|. m) ary'
        | otherwise = do
            st <- A.indexM ary i
            st' <- go h s k x (bs+bitsPerSubkey) st
            A.unsafeUpdateM ary i st'
            return t
      where m = mask h bs
            i = sparseIndex b m
    go h s k x bs t@(Full ary) = do
        st <- A.indexM ary i
        st' <- go h s k x (bs+bitsPerSubkey) st
        A.unsafeUpdateM ary i st'
        return t
      where i = index h bs
    go h s k x bs t@(Collision hx l1@(L k1 v1) l2@(L k2 v2) hmx)
        | h == hx   =
          let go'
                | k == k1   = return $! Collision hx (L k (f x v1)) l2 hmx
                | k == k2   = return $! Collision hx l1 (L k (f x v2)) hmx
                | otherwise = Collision hx l1 l2 <$> go (hashWithSalt (nextSalt s) k) (nextSalt s) k x 0 hmx
          in go'
        | otherwise = go h s k x bs $ BitmapIndexed (mask hx bs) (A.singleton t)
{-# INLINABLE unsafeInsertWith #-}

-- | /O(log n)/ Remove the mapping for the specified key from this map
-- if present.
delete :: (Eq k, Hashable k) => k -> HashMap k v -> HashMap k v
delete k m = delete' (hashWithSalt defaultSalt k) defaultSalt k m
{-# INLINABLE delete #-}

delete' :: (Eq k, Hashable k) => Hash -> Salt -> k -> HashMap k v -> HashMap k v
delete' h0 s0 k0 m0 = go h0 s0 k0 0 m0
  where
    go !_ _ !_ !_ Empty = Empty
    go h _ k _ t@(Leaf hy (L ky _))
        | hy == h && ky == k = Empty
        | otherwise          = t
    go h s k bs t@(BitmapIndexed b ary)
        | b .&. m == 0 = t
        | otherwise =
            let !st = A.index ary i
                !st' = go h s k (bs+bitsPerSubkey) st
            in if st' `ptrEq` st
                then t
                else case st' of
                Empty | A.length ary == 1 -> Empty
                      | A.length ary == 2 ->
                          case (i, A.index ary 0, A.index ary 1) of
                          (0, _, l) | isLeafOrCollision l -> l
                          (1, l, _) | isLeafOrCollision l -> l
                          _                               -> bIndexed
                      | otherwise -> bIndexed
                    where
                      bIndexed = BitmapIndexed (b .&. complement m) (A.delete ary i)
                l | isLeafOrCollision l && A.length ary == 1 -> l
                _ -> BitmapIndexed b (A.update ary i st')
      where m = mask h bs
            i = sparseIndex b m
    go h s k bs t@(Full ary) =
        let !st   = A.index ary i
            !st' = go h s k (bs+bitsPerSubkey) st
        in if st' `ptrEq` st
            then t
            else case st' of
            Empty ->
                let ary' = A.delete ary i
                    bm   = fullNodeMask .&. complement (1 `unsafeShiftL` i)
                in BitmapIndexed bm ary'
            _ -> Full (A.update ary i st')
      where i = index h bs
    go h s k _ t@(Collision hx l1@(L k1 _) l2@(L k2 _) hmx)
        | h == hx =
          let go'
                | k == k1 = case unconsHM hmx of
                    UnconsEmptyHM -> Leaf hx l2
                    UnconsedHM l3 hmx' -> Collision hx l2 l3 hmx'
                | k == k2 = case unconsHM hmx of
                    UnconsEmptyHM -> Leaf hx l1
                    UnconsedHM l3 hmx' -> Collision hx l1 l3 hmx'
                | otherwise = Collision hx l1 l2 $ go (hashWithSalt (nextSalt s) k) (nextSalt s) k 0 hmx
          in go'
        | otherwise = t
{-# INLINABLE delete' #-}

-- | Delete optimized for the case when we know the key is in the map.
--
-- We can skip:
--  - the key equality check on the leaf, if we reach a leaf it must be the key
--
-- We still need to do the equality check for collisions.
deleteKeyExists :: (Eq k, Hashable k) => Hash -> Salt -> k -> HashMap k v -> HashMap k v
deleteKeyExists !h0 s0 !k0 !m0 = go h0 s0 k0 0 m0
  where
    go :: (Eq k, Hashable k) => Hash -> Salt -> k -> Int -> HashMap k v -> HashMap k v
    go !_h !_s !_k !_bs (Leaf _ _) = Empty
    go h s k bs (BitmapIndexed b ary) =
            let !st = A.index ary i
                !st' = go h s k (bs+bitsPerSubkey) st
            in case st' of
                Empty | A.length ary == 1 -> Empty
                      | A.length ary == 2 ->
                          case (i, A.index ary 0, A.index ary 1) of
                          (0, _, l) | isLeafOrCollision l -> l
                          (1, l, _) | isLeafOrCollision l -> l
                          _                               -> bIndexed
                      | otherwise -> bIndexed
                    where
                      bIndexed = BitmapIndexed (b .&. complement m) (A.delete ary i)
                l | isLeafOrCollision l && A.length ary == 1 -> l
                _ -> BitmapIndexed b (A.update ary i st')
      where m = mask h bs
            i = sparseIndex b m
    go h s k bs (Full ary) =
        let !st   = A.index ary i
            !st' = go h s k (bs+bitsPerSubkey) st
        in case st' of
            Empty ->
                let ary' = A.delete ary i
                    bm   = fullNodeMask .&. complement (1 `unsafeShiftL` i)
                in BitmapIndexed bm ary'
            _ -> Full (A.update ary i st')
      where i = index h bs
    go h s k _ (Collision hx l1@(L k1 _) l2@(L k2 _) hmx)
        | h == hx =
          let go'
                | k == k1 = case unconsHM hmx of
                    UnconsEmptyHM -> Leaf hx l2
                    UnconsedHM l3 hmx' -> Collision hx l2 l3 hmx'
                | k == k2 = case unconsHM hmx of
                    UnconsEmptyHM -> Leaf hx l1
                    UnconsedHM l3 hmx' -> Collision hx l1 l3 hmx'
                | otherwise = Collision hx l1 l2 $ go (hashWithSalt (nextSalt s) k) (nextSalt s) k 0 hmx
          in go'
        | otherwise = Empty -- error "Internal error: unexpected collision"
    go !_ !_ !_ !_ Empty = Empty -- error "Internal error: deleteKeyExists empty"
{-# NOINLINE deleteKeyExists #-}

-- | /O(log n)/ Adjust the value tied to a given key in this map only
-- if it is present. Otherwise, leave the map alone.
adjust :: (Eq k, Hashable k) => (v -> v) -> k -> HashMap k v -> HashMap k v
-- This operation really likes to leak memory, so using this
-- indirect implementation shouldn't hurt much. Furthermore, it allows
-- GHC to avoid a leak when the function is lazy. In particular,
--
--     adjust (const x) k m
-- ==> adjust# (\v -> (# const x v #)) k m
-- ==> adjust# (\_ -> (# x #)) k m
adjust f k m = adjust# (\v -> (# f v #)) k m
{-# INLINE adjust #-}

-- | Much like 'adjust', but not inherently leaky.
adjust# :: (Eq k, Hashable k) => (v -> (# v #)) -> k -> HashMap k v -> HashMap k v
adjust# f k0 m0 = go h0 s0 k0 0 m0
  where
    h0 = hashWithSalt s0 k0
    s0 = defaultSalt
    go !_ !_ !_ !_ Empty = Empty
    go h _ k _ t@(Leaf hy (L ky y))
        | hy == h && ky == k = case f y of
            (# y' #) | ptrEq y y' -> t
                     | otherwise -> Leaf h (L k y')
        | otherwise          = t
    go h s k bs t@(BitmapIndexed b ary)
        | b .&. m == 0 = t
        | otherwise = let !st   = A.index ary i
                          !st'  = go h s k (bs+bitsPerSubkey) st
                          ary' = A.update ary i $! st'
                      in if ptrEq st st'
                         then t
                         else BitmapIndexed b ary'
      where m = mask h bs
            i = sparseIndex b m
    go h s k bs t@(Full ary) =
        let i    = index h bs
            !st   = A.index ary i
            !st'  = go h s k (bs+bitsPerSubkey) st
            ary' = update16 ary i $! st'
        in if ptrEq st st'
           then t
           else Full ary'
    go h s k _ t@(Collision hx l1@(L k1 v1) l2@(L k2 v2) hmx)
        | h == hx   =
          let go'
                | k == k1 = case f v1 of
                    (# v1' #) | ptrEq v1 v1' -> t
                              | otherwise -> Collision hx (L k v1') l2 hmx
                | k == k2 = case f v2 of
                    (# v2' #) | ptrEq v2 v2' -> t
                              | otherwise -> Collision hx l1 (L k v2') hmx
                | otherwise = Collision hx l1 l2 $ go (hashWithSalt (nextSalt s) k) (nextSalt s) k 0 hmx
          in go'
        | otherwise = t
{-# INLINABLE adjust# #-}

-- | /O(log n)/  The expression (@'update' f k map@) updates the value @x@ at @k@,
-- (if it is in the map). If (f k x) is @'Nothing', the element is deleted.
-- If it is (@'Just' y), the key k is bound to the new value y.
update :: (Eq k, Hashable k) => (a -> Maybe a) -> k -> HashMap k a -> HashMap k a
update f = alter (>>= f)
{-# INLINABLE update #-}


-- | /O(log n)/  The expression (@'alter' f k map@) alters the value @x@ at @k@, or
-- absence thereof. @alter@ can be used to insert, delete, or update a value in a
-- map. In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
alter :: (Eq k, Hashable k) => (Maybe v -> Maybe v) -> k -> HashMap k v -> HashMap k v
-- TODO(m-renaud): Consider using specialized insert and delete for alter.
alter f k m =
  case f (lookup k m) of
    Nothing -> delete k m
    Just v  -> insert k v m
{-# INLINABLE alter #-}

-- | /O(log n)/  The expression (@'alterF' f k map@) alters the value @x@ at
-- @k@, or absence thereof. @alterF@ can be used to insert, delete, or update
-- a value in a map.
--
-- Note: 'alterF' is a flipped version of the 'at' combinator from
-- <https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-At.html#v:at Control.Lens.At>.
--
-- @since 0.2.9
alterF :: (Functor f, Eq k, Hashable k)
       => (Maybe v -> f (Maybe v)) -> k -> HashMap k v -> f (HashMap k v)
-- We only calculate the hash once, but unless this is rewritten
-- by rules we may test for key equality multiple times.
-- We force the value of the map for consistency with the rewritten
-- version; otherwise someone could tell the difference using a lazy
-- @f@ and a functor that is similar to Const but not actually Const.
alterF f = \ !k !m ->
  let
    !h = hashWithSalt s k
    s = defaultSalt
    mv = lookup' h s k m
  in (<$> f mv) $ \fres ->
    case fres of
      Nothing -> delete' h s k m
      Just v' -> insert' h s k v' m

-- We unconditionally rewrite alterF in RULES, but we expose an
-- unfolding just in case it's used in some way that prevents the
-- rule from firing.
{-# INLINABLE [0] alterF #-}

#if MIN_VERSION_base(4,8,0)
-- This is just a bottom value. See the comment on the "alterFWeird"
-- rule.
test_bottom :: a
test_bottom = error "Data.HashMap.alterF internal error: hit test_bottom"

-- We use this as an error result in RULES to ensure we don't get
-- any useless CallStack nonsense.
bogus# :: (# #) -> (# a #)
bogus# _ = error "Data.HashMap.alterF internal error: hit bogus#"

{-# RULES
-- We probe the behavior of @f@ by applying it to Nothing and to
-- Just test_bottom. Based on the results, and how they relate to
-- each other, we choose the best implementation.

"alterFWeird" forall f. alterF f =
   alterFWeird (f Nothing) (f (Just test_bottom)) f

-- This rule covers situations where alterF is used to simply insert or
-- delete in Identity (most likely via Control.Lens.At). We recognize here
-- (through the repeated @x@ on the LHS) that
--
-- @f Nothing = f (Just bottom)@,
--
-- which guarantees that @f@ doesn't care what its argument is, so
-- we don't have to either.
--
-- Why only Identity? A variant of this rule is actually valid regardless of
-- the functor, but for some functors (e.g., []), it can lead to the
-- same keys being compared multiple times, which is bad if they're
-- ugly things like strings. This is unfortunate, since the rule is likely
-- a good idea for almost all realistic uses, but I don't like nasty
-- edge cases.
"alterFconstant" forall (f :: Maybe a -> Identity (Maybe a)) x.
  alterFWeird x x f = \ !k !m ->
    Identity (case runIdentity x of {Nothing -> delete k m; Just a -> insert k a m})

-- This rule handles the case where 'alterF' is used to do 'insertWith'-like
-- things. Whenever possible, GHC will get rid of the Maybe nonsense for us.
-- We delay this rule to stage 1 so alterFconstant has a chance to fire.
"alterFinsertWith" [1] forall (f :: Maybe a -> Identity (Maybe a)) x y.
  alterFWeird (coerce (Just x)) (coerce (Just y)) f =
    coerce (insertModifying x (\mold -> case runIdentity (f (Just mold)) of
                                            Nothing -> bogus# (# #)
                                            Just new -> (# new #)))

-- Handle the case where someone uses 'alterF' instead of 'adjust'. This
-- rule is kind of picky; it will only work if the function doesn't
-- do anything between case matching on the Maybe and producing a result.
"alterFadjust" forall (f :: Maybe a -> Identity (Maybe a)) _y.
  alterFWeird (coerce Nothing) (coerce (Just _y)) f =
    coerce (adjust# (\x -> case runIdentity (f (Just x)) of
                               Just x' -> (# x' #)
                               Nothing -> bogus# (# #)))

-- The simple specialization to Const; in this case we can look up
-- the key without caring what position it's in. This is only a tiny
-- optimization.
"alterFlookup" forall _ign1 _ign2 (f :: Maybe a -> Const r (Maybe a)).
  alterFWeird _ign1 _ign2 f = \ !k !m -> Const (getConst (f (lookup k m)))
 #-}

-- This is a very unsafe version of alterF used for RULES. When calling
-- alterFWeird x y f, the following *must* hold:
--
-- x = f Nothing
-- y = f (Just _|_)
--
-- Failure to abide by these laws will make demons come out of your nose.
alterFWeird
       :: (Functor f, Eq k, Hashable k)
       => f (Maybe v)
       -> f (Maybe v)
       -> (Maybe v -> f (Maybe v)) -> k -> HashMap k v -> f (HashMap k v)
alterFWeird _ _ f = alterFEager f
{-# INLINE [0] alterFWeird #-}

-- | This is the default version of alterF that we use in most non-trivial
-- cases. It's called "eager" because it looks up the given key in the map
-- eagerly, whether or not the given function requires that information.
alterFEager :: (Functor f, Eq k, Hashable k)
       => (Maybe v -> f (Maybe v)) -> k -> HashMap k v -> f (HashMap k v)
alterFEager f !k m = (<$> f mv) $ \fres ->
  case fres of

    ------------------------------
    -- Delete the key from the map.
    Nothing -> case lookupRes of

      -- Key did not exist in the map to begin with, no-op
      Absent -> m

      -- Key did exist
      Present _ -> deleteKeyExists h s k m

    ------------------------------
    -- Update value
    Just v' -> case lookupRes of

      -- Key did not exist before, insert v' under a new key
      Absent -> insertNewKey h s k v' m

      -- Key existed before
      Present v ->
        if v `ptrEq` v'
        -- If the value is identical, no-op
        then m
        -- If the value changed, update the value.
        else insertKeyExists h s k v' m

  where !h = hashWithSalt s k
        !s = defaultSalt
        !lookupRes = lookupWithRes h s k m
        !mv = case lookupRes of
           Absent -> Nothing
           Present v -> Just v
{-# INLINABLE alterFEager #-}
#endif


------------------------------------------------------------------------
-- * Combine

-- | /O(n+m)/ The union of two maps. If a key occurs in both maps, the
-- mapping from the first will be the mapping in the result.
union :: (Eq k, Hashable k) => HashMap k v -> HashMap k v -> HashMap k v
union = unionWith const
{-# INLINABLE union #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
unionWith :: (Eq k, Hashable k) => (v -> v -> v) -> HashMap k v -> HashMap k v
          -> HashMap k v
unionWith f = unionWithKey (const f)
{-# INLINE unionWith #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
unionWithKey :: (Eq k, Hashable k) => (k -> v -> v -> v) -> HashMap k v -> HashMap k v
          -> HashMap k v
unionWithKey f = go 0 s0
  where
    s0 = defaultSalt
    -- empty vs. anything
    go !_ !_ t1 Empty = t1
    go _ _ Empty t2 = t2
    -- leaf vs. leaf
    go bs s t1@(Leaf h1 l1@(L k1 v1)) t2@(Leaf h2 l2@(L k2 v2))
        | h1 == h2  = if k1 == k2
                      then Leaf h1 (L k1 (f k1 v1 v2))
                      else collision h1 s l1 l2
        | otherwise = goDifferentHash bs s h1 h2 t1 t2
    go bs s t1@(Leaf h1 l1@(L k1 v1)) t2@(Collision h2 l21@(L k21 v21) l22@(L k22 v22) hm2)
        | h1 == h2  =
          let go'
                | k1 == k21 = Collision h1 (L k1 (f k1 v1 v21)) l22 hm2
                | k1 == k22 = Collision h1 l21 (L k1 (f k1 v1 v22)) hm2
                | otherwise = Collision h1 l21 l22 $ go 0 (nextSalt s) (Leaf (hashWithSalt (nextSalt s) k1) l1) hm2
          in go'
        | otherwise = goDifferentHash bs s h1 h2 t1 t2
    go bs s t1@(Collision h1 l11@(L k11 v11) l12@(L k12 v12) hm1) t2@(Leaf h2 l2@(L k2 v2))
        | h1 == h2  =
          let go'
                | k2 == k11 = Collision h1 (L k2 (f k2 v11 v2)) l12 hm1
                | k2 == k12 = Collision h1 l11 (L k2 (f k2 v12 v2)) hm1
                | otherwise = Collision h1 l11 l12 $ go 0 (nextSalt s) hm1 (Leaf (hashWithSalt (nextSalt s) k2) l2)
          in go'
        | otherwise = goDifferentHash bs s h1 h2 t1 t2
    go bs s t1@(Collision h1 _ _ _) t2@(Collision h2 _ _ _)
        | h1 == h2  = L.foldl' (\h (k,v) -> go 0 s h (Leaf (hashWithSalt s k) (L k v))) t1 $ toList t2 -- Nothing better we can do, unfortunately.
        | otherwise = goDifferentHash bs s h1 h2 t1 t2
    -- branch vs. branch
    go bs s (BitmapIndexed b1 ary1) (BitmapIndexed b2 ary2) =
        let b'   = b1 .|. b2
            ary' = unionArrayBy (go (bs+bitsPerSubkey) s) b1 b2 ary1 ary2
        in bitmapIndexedOrFull b' ary'
    go bs s (BitmapIndexed b1 ary1) (Full ary2) =
        let ary' = unionArrayBy (go (bs+bitsPerSubkey) s) b1 fullNodeMask ary1 ary2
        in Full ary'
    go bs s (Full ary1) (BitmapIndexed b2 ary2) =
        let ary' = unionArrayBy (go (bs+bitsPerSubkey) s) fullNodeMask b2 ary1 ary2
        in Full ary'
    go bs s (Full ary1) (Full ary2) =
        let ary' = unionArrayBy (go (bs+bitsPerSubkey) s) fullNodeMask fullNodeMask
                   ary1 ary2
        in Full ary'
    -- leaf vs. branch
    go bs s (BitmapIndexed b1 ary1) t2
        | b1 .&. m2 == 0 = let ary' = A.insert ary1 i t2
                               b'   = b1 .|. m2
                           in bitmapIndexedOrFull b' ary'
        | otherwise      = let ary' = A.updateWith' ary1 i $ \st1 ->
                                   go (bs+bitsPerSubkey) s st1 t2
                           in BitmapIndexed b1 ary'
        where
          h2 = leafHashCode t2
          m2 = mask h2 bs
          i = sparseIndex b1 m2
    go bs s t1 (BitmapIndexed b2 ary2)
        | b2 .&. m1 == 0 = let ary' = A.insert ary2 i $! t1
                               b'   = b2 .|. m1
                           in bitmapIndexedOrFull b' ary'
        | otherwise      = let ary' = A.updateWith' ary2 i $ \st2 ->
                                   go (bs+bitsPerSubkey) s t1 st2
                           in BitmapIndexed b2 ary'
      where
        h1 = leafHashCode t1
        m1 = mask h1 bs
        i = sparseIndex b2 m1
    go bs s (Full ary1) t2 =
        let h2   = leafHashCode t2
            i    = index h2 bs
            ary' = update16With' ary1 i $ \st1 -> go (bs+bitsPerSubkey) s st1 t2
        in Full ary'
    go bs s t1 (Full ary2) =
        let h1   = leafHashCode t1
            i    = index h1 bs
            ary' = update16With' ary2 i $ \st2 -> go (bs+bitsPerSubkey) s t1 st2
        in Full ary'

    leafHashCode (Leaf h _) = h
    leafHashCode (Collision h _ _ _) = h
    leafHashCode _ = error "leafHashCode"

    goDifferentHash bs s h1 h2 t1 t2
        | m1 == m2  = BitmapIndexed m1 (A.singleton $! go (bs+bitsPerSubkey) s t1 t2)
        | m1 <  m2  = BitmapIndexed (m1 .|. m2) (A.pair t1 t2)
        | otherwise = BitmapIndexed (m1 .|. m2) (A.pair t2 t1)
      where
        m1 = mask h1 bs
        m2 = mask h2 bs
{-# INLINE unionWithKey #-}

-- | Strict in the result of @f@.
unionArrayBy :: (a -> a -> a) -> Bitmap -> Bitmap -> A.Array a -> A.Array a
             -> A.Array a
unionArrayBy f b1 b2 ary1 ary2 = A.run $ do
    let b' = b1 .|. b2
    mary <- A.new_ (popCount b')
    -- iterate over nonzero bits of b1 .|. b2
    -- it would be nice if we could shift m by more than 1 each time
    let ba = b1 .&. b2
        go !i !i1 !i2 !m
            | m > b'        = return ()
            | b' .&. m == 0 = go i i1 i2 (m `unsafeShiftL` 1)
            | ba .&. m /= 0 = do
                x1 <- A.indexM ary1 i1
                x2 <- A.indexM ary2 i2
                A.write mary i $! f x1 x2
                go (i+1) (i1+1) (i2+1) (m `unsafeShiftL` 1)
            | b1 .&. m /= 0 = do
                A.write mary i =<< A.indexM ary1 i1
                go (i+1) (i1+1) (i2  ) (m `unsafeShiftL` 1)
            | otherwise     = do
                A.write mary i =<< A.indexM ary2 i2
                go (i+1) (i1  ) (i2+1) (m `unsafeShiftL` 1)
    go 0 0 0 (b' .&. negate b') -- XXX: b' must be non-zero
    return mary
    -- TODO: For the case where b1 .&. b2 == b1, i.e. when one is a
    -- subset of the other, we could use a slightly simpler algorithm,
    -- where we copy one array, and then update.
{-# INLINE unionArrayBy #-}

-- TODO: Figure out the time complexity of 'unions'.

-- | Construct a set containing all elements from a list of sets.
unions :: (Eq k, Hashable k) => [HashMap k v] -> HashMap k v
unions = L.foldl' union empty
{-# INLINE unions #-}

------------------------------------------------------------------------
-- * Transformations

-- | /O(n)/ Transform this map by applying a function to every value.
mapWithKey :: (k -> v1 -> v2) -> HashMap k v1 -> HashMap k v2
mapWithKey f = go
  where
    go Empty = Empty
    go (Leaf h (L k v)) = Leaf h $ L k (f k v)
    go (BitmapIndexed b ary) = BitmapIndexed b $ A.map go ary
    go (Full ary) = Full $ A.map go ary
    -- Why map strictly over collision arrays? Because there's no
    -- point suspending the O(1) work this does for each leaf.
    go (Collision h (L k1 v1) (L k2 v2) hm) = Collision h (L k1 (f k2 v1)) (L k2 (f k2 v2)) $ go hm
{-# INLINE mapWithKey #-}

-- | /O(n)/ Transform this map by applying a function to every value.
map :: (v1 -> v2) -> HashMap k v1 -> HashMap k v2
map f = mapWithKey (const f)
{-# INLINE map #-}

-- TODO: We should be able to use mutation to create the new
-- 'HashMap'.

-- | /O(n)/ Perform an 'Applicative' action for each key-value pair
-- in a 'HashMap' and produce a 'HashMap' of all the results.
--
-- Note: the order in which the actions occur is unspecified. In particular,
-- when the map contains hash collisions, the order in which the actions
-- associated with the keys involved will depend in an unspecified way on
-- their insertion order.
traverseWithKey
  :: Applicative f
  => (k -> v1 -> f v2)
  -> HashMap k v1 -> f (HashMap k v2)
traverseWithKey f = go
  where
    go Empty                 = pure Empty
    go (Leaf h (L k v))      = Leaf h . L k <$> f k v
    go (BitmapIndexed b ary) = BitmapIndexed b <$> A.traverse go ary
    go (Full ary)            = Full <$> A.traverse go ary
    go (Collision h (L k1 v1) (L k2 v2) hm)    =
        Collision h <$> (L k1 <$> f k1 v1) <*> (L k2 <$> f k2 v2) <*> go hm
{-# INLINE traverseWithKey #-}

------------------------------------------------------------------------
-- * Difference and intersection

-- | /O(n*log m)/ Difference of two maps. Return elements of the first map
-- not existing in the second.
difference :: (Eq k, Hashable k) => HashMap k v -> HashMap k w -> HashMap k v
difference a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Nothing -> insert k v m
                 _       -> m
{-# INLINABLE difference #-}

-- | /O(n*log m)/ Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the values of these keys.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
differenceWith :: (Eq k, Hashable k) => (v -> w -> Maybe v) -> HashMap k v -> HashMap k w -> HashMap k v
differenceWith f a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Nothing -> insert k v m
                 Just w  -> maybe m (\y -> insert k y m) (f v w)
{-# INLINABLE differenceWith #-}

-- | /O(n*log m)/ Intersection of two maps. Return elements of the first
-- map for keys existing in the second.
intersection :: (Eq k, Hashable k) => HashMap k v -> HashMap k w -> HashMap k v
intersection a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Just _ -> insert k v m
                 _      -> m
{-# INLINABLE intersection #-}

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
intersectionWith :: (Eq k, Hashable k) => (v1 -> v2 -> v3) -> HashMap k v1
                 -> HashMap k v2 -> HashMap k v3
intersectionWith f a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Just w -> insert k (f v w) m
                 _      -> m
{-# INLINABLE intersectionWith #-}

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
intersectionWithKey :: (Eq k, Hashable k) => (k -> v1 -> v2 -> v3)
                    -> HashMap k v1 -> HashMap k v2 -> HashMap k v3
intersectionWithKey f a b = foldlWithKey' go empty a
  where
    go m k v = case lookup k b of
                 Just w -> insert k (f k v w) m
                 _      -> m
{-# INLINABLE intersectionWithKey #-}

------------------------------------------------------------------------
-- * Folds

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before using the result in the next application.
-- This function is strict in the starting value.
foldl' :: (a -> v -> a) -> a -> HashMap k v -> a
foldl' f = foldlWithKey' (\ z _ v -> f z v)
{-# INLINE foldl' #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before using the result in the next application.
-- This function is strict in the starting value.
foldlWithKey' :: (a -> k -> v -> a) -> a -> HashMap k v -> a
foldlWithKey' f = go
  where
    go !z Empty                = z
    go z (Leaf _ (L k v))      = f z k v
    go z (BitmapIndexed _ ary) = A.foldl' go z ary
    go z (Full ary)            = A.foldl' go z ary
    go z (Collision _ (L k1 v1) (L k2 v2) hm) = go (f (f z k1 v1) k2 v2) hm
{-# INLINE foldlWithKey' #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldr :: (v -> a -> a) -> a -> HashMap k v -> a
foldr f = foldrWithKey (const f)
{-# INLINE foldr #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldrWithKey :: (k -> v -> a -> a) -> a -> HashMap k v -> a
foldrWithKey f = go
  where
    go z Empty                 = z
    go z (Leaf _ (L k v))      = f k v z
    go z (BitmapIndexed _ ary) = A.foldr (flip go) z ary
    go z (Full ary)            = A.foldr (flip go) z ary
    go z (Collision _ (L k1 v1) (L k2 v2) hm)    = f k1 v1 (f k2 v2 (go z hm))
{-# INLINE foldrWithKey #-}

------------------------------------------------------------------------
-- * Filter

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only some of them.
mapMaybeWithKey :: (k -> v1 -> Maybe v2) -> HashMap k v1 -> HashMap k v2
mapMaybeWithKey f = filterMapAux onLeaf
  where onLeaf (Leaf h (L k v)) | Just v' <- f k v = Just (Leaf h (L k v'))
        onLeaf _ = Nothing
{-# INLINE mapMaybeWithKey #-}

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only some of them.
mapMaybe :: (v1 -> Maybe v2) -> HashMap k v1 -> HashMap k v2
mapMaybe f = mapMaybeWithKey (const f)
{-# INLINE mapMaybe #-}

-- | /O(n)/ Filter this map by retaining only elements satisfying a
-- predicate.
filterWithKey :: forall k v. (k -> v -> Bool) -> HashMap k v -> HashMap k v
filterWithKey pred = filterMapAux onLeaf
  where onLeaf t@(Leaf _ (L k v)) | pred k v = Just t
        onLeaf _ = Nothing
{-# INLINE filterWithKey #-}


-- | Common implementation for 'filterWithKey' and 'mapMaybeWithKey',
--   allowing the former to former to reuse terms.
filterMapAux :: forall k v1 v2
              . (HashMap k v1 -> Maybe (HashMap k v2))
             -> HashMap k v1
             -> HashMap k v2
filterMapAux onLeaf = go
  where
    go Empty = Empty
    go t@Leaf{}
        | Just t' <- onLeaf t = t'
        | otherwise = Empty
    go (BitmapIndexed b ary) = filterA ary b
    go (Full ary) = filterA ary fullNodeMask
    go (Collision h l1 l2 hm) = case (onLeaf (Leaf h l1), onLeaf (Leaf h l2)) of
      (Just (Leaf _ l1'), Just (Leaf _ l2')) -> Collision h l1' l2' $ go hm
      (Just (Leaf _ l1'), Nothing) -> go1 l1'
      (Nothing, Just (Leaf _ l2')) -> go1 l2'
      (Nothing, Nothing) -> case unconsHM (go hm) of
        UnconsEmptyHM -> Empty
        UnconsedHM l1' hm' -> case unconsHM hm' of
          UnconsEmptyHM -> Leaf h l1'
          UnconsedHM l2' hm'' -> Collision h l1' l2' hm''
      _ -> error "Should not happen, can be fixed with refactoring I think."
      where
        go1 l1' = case unconsHM (go hm) of
          UnconsEmptyHM -> Leaf h l1'
          UnconsedHM l2' hm' -> Collision h l1' l2' hm'

    filterA ary0 b0 =
        let !n = A.length ary0
        in runST $ do
            mary <- A.new_ n
            step ary0 mary b0 0 0 1 n
      where
        step :: A.Array (HashMap k v1) -> A.MArray s (HashMap k v2)
             -> Bitmap -> Int -> Int -> Bitmap -> Int
             -> ST s (HashMap k v2)
        step !ary !mary !b i !j !bi n
            | i >= n = case j of
                0 -> return Empty
                1 -> do
                    ch <- A.read mary 0
                    case ch of
                      t | isLeafOrCollision t -> return t
                      _                       -> BitmapIndexed b <$> A.trim mary 1
                _ -> do
                    ary2 <- A.trim mary j
                    return $! if j == maxChildren
                              then Full ary2
                              else BitmapIndexed b ary2
            | bi .&. b == 0 = step ary mary b i j (bi `unsafeShiftL` 1) n
            | otherwise = case go (A.index ary i) of
                Empty -> step ary mary (b .&. complement bi) (i+1) j
                         (bi `unsafeShiftL` 1) n
                t     -> do A.write mary j t
                            step ary mary b (i+1) (j+1) (bi `unsafeShiftL` 1) n
{-# INLINE filterMapAux #-}

-- | /O(n)/ Filter this map by retaining only elements which values
-- satisfy a predicate.
filter :: (v -> Bool) -> HashMap k v -> HashMap k v
filter p = filterWithKey (\_ v -> p v)
{-# INLINE filter #-}

------------------------------------------------------------------------
-- * Conversions

-- TODO: Improve fusion rules by modelled them after the Prelude ones
-- on lists.

-- | /O(n)/ Return a list of this map's keys.  The list is produced
-- lazily.
keys :: HashMap k v -> [k]
keys = L.map fst . toList
{-# INLINE keys #-}

-- | /O(n)/ Return a list of this map's values.  The list is produced
-- lazily.
elems :: HashMap k v -> [v]
elems = L.map snd . toList
{-# INLINE elems #-}

------------------------------------------------------------------------
-- ** Lists

-- | /O(n)/ Return a list of this map's elements.  The list is
-- produced lazily. The order of its elements is unspecified.
toList :: HashMap k v -> [(k, v)]
toList t = build (\ c z -> foldrWithKey (curry c) z t)
{-# INLINE toList #-}

-- | /O(n)/ Construct a map with the supplied mappings.  If the list
-- contains duplicate mappings, the later mappings take precedence.
fromList :: (Eq k, Hashable k) => [(k, v)] -> HashMap k v
fromList = L.foldl' (\ m (k, v) -> unsafeInsert k v m) empty
{-# INLINABLE fromList #-}

-- | /O(n*log n)/ Construct a map from a list of elements.  Uses
-- the provided function to merge duplicate entries.
fromListWith :: (Eq k, Hashable k) => (v -> v -> v) -> [(k, v)] -> HashMap k v
fromListWith f = L.foldl' (\ m (k, v) -> unsafeInsertWith f k v m) empty
{-# INLINE fromListWith #-}

------------------------------------------------------------------------
-- Array operations

-- | /O(n)/ Lookup the value associated with the given key in this
-- array.  Returns 'Nothing' if the key wasn't found.
indexOf :: Eq k => k -> A.Array (Leaf k v) -> Maybe Int
indexOf k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go !k !ary !i !n
        | i >= n    = Nothing
        | otherwise = case A.index ary i of
            (L kx _)
                | k == kx   -> Just i
                | otherwise -> go k ary (i+1) n
{-# INLINABLE indexOf #-}

updateOrConcatWith :: Eq k => (v -> v -> v) -> A.Array (Leaf k v) -> A.Array (Leaf k v) -> A.Array (Leaf k v)
updateOrConcatWith f = updateOrConcatWithKey (const f)
{-# INLINABLE updateOrConcatWith #-}

updateOrConcatWithKey :: Eq k => (k -> v -> v -> v) -> A.Array (Leaf k v) -> A.Array (Leaf k v) -> A.Array (Leaf k v)
updateOrConcatWithKey f ary1 ary2 = A.run $ do
    -- TODO: instead of mapping and then folding, should we traverse?
    -- We'll have to be careful to avoid allocating pairs or similar.

    -- first: look up the position of each element of ary2 in ary1
    let indices = A.map' (\(L k _) -> indexOf k ary1) ary2
    -- that tells us how large the overlap is:
    -- count number of Nothing constructors
    let nOnly2 = A.foldl' (\n -> maybe (n+1) (const n)) 0 indices
    let n1 = A.length ary1
    let n2 = A.length ary2
    -- copy over all elements from ary1
    mary <- A.new_ (n1 + nOnly2)
    A.copy ary1 0 mary 0 n1
    -- append or update all elements from ary2
    let go !iEnd !i2
          | i2 >= n2 = return ()
          | otherwise = case A.index indices i2 of
               Just i1 -> do -- key occurs in both arrays, store combination in position i1
                             L k v1 <- A.indexM ary1 i1
                             L _ v2 <- A.indexM ary2 i2
                             A.write mary i1 (L k (f k v1 v2))
                             go iEnd (i2+1)
               Nothing -> do -- key is only in ary2, append to end
                             A.write mary iEnd =<< A.indexM ary2 i2
                             go (iEnd+1) (i2+1)
    go n1 0
    return mary
{-# INLINABLE updateOrConcatWithKey #-}

-- Helper functions for very rare cases.

-- Remove (any) one element from a non-empty array
-- of non-empty hashmaps.
unconsA :: A.Array (HashMap k v) -> UnconsA k v
unconsA ary =
  case unconsHM  (A.index ary 0) of
    UnconsEmptyHM ->
      error "Data.HashMap internal error: empty hashmap in array."
    UnconsedHM lf Empty
      | A.length ary == 1 -> NowEmptyA lf
      | otherwise -> RemovedFirstA lf (A.delete ary 0)
    UnconsedHM lf hm' -> UnconsedFromFirstA lf (A.update ary 0 hm')

data UnconsA k v
  = NowEmptyA !(Leaf k v)
    -- Got an entry from the array without changing its length
  | UnconsedFromFirstA
    !(Leaf k v) -- The leaf that was un-consed
    !(A.Array (HashMap k v)) -- The leftover array
    -- Got an entry from the array, shortening it by one element.
  | RemovedFirstA
    !(Leaf k v) -- The leaf that was un-consed
    !(A.Array (HashMap k v)) -- The leftover array
  deriving Show

data UnconsHM k v
  = UnconsEmptyHM
  | UnconsedHM !(Leaf k v) !(HashMap k v)
  deriving Show

-- Remove (any) one element from a hashmap
unconsHM :: HashMap k v -> UnconsHM k v
unconsHM hm = case hm of
  Empty -> UnconsEmptyHM
  Leaf _ l -> UnconsedHM l Empty
  BitmapIndexed bm ary' -> case unconsA ary' of
    NowEmptyA l -> UnconsedHM l Empty
    UnconsedFromFirstA l a' -> UnconsedHM l (collapse_maybe bm a')
    RemovedFirstA l a' -> UnconsedHM l (collapse_maybe (shorten_bm bm) a')
  Full ary' -> case unconsA ary' of
    NowEmptyA l ->
       UnconsedHM l Empty
    UnconsedFromFirstA l a' ->
       UnconsedHM l (Full a')
    RemovedFirstA l a' ->
       UnconsedHM l $ BitmapIndexed (shorten_bm fullNodeMask) a'
  Collision h l1 l2 hm' -> UnconsedHM l1 $ case unconsHM hm' of
    UnconsEmptyHM -> Leaf h l2
    UnconsedHM l3 hm'' -> Collision h l2 l3 hm''
  where
    -- When the array is shortened, we need to delete the
    -- first element (the lowest set bit) from the bitmap.
    shorten_bm bm = bm .&. (bm - 1)

    -- We must never create a BitmapIndexed with exactly
    -- one element whose sole element is a leaf or collision.
    -- In such cases, we instead collapse a level, removing
    -- the BitmapIndexed. This "smart constructor" takes care
    -- of potential collapse.
    --
    -- Note: we *could* arrange to catch this condition earlier,
    -- as delete' does, preventing the allocation of an unnecessary
    -- one-element array. But to reach this code we must be dealing with a
    -- collision bucket that has at least four elements. That puts us
    -- well off the fast path already.
    collapse_maybe bm ar
      | popCount bm == 1  -- The array has exactly one element.
      , let the_elem = A.index ar 0
      , isLeafOrCollision the_elem
      = the_elem
      | otherwise
      = BitmapIndexed bm ar

------------------------------------------------------------------------
-- Manually unrolled loops

-- | /O(n)/ Update the element at the given position in this array.
update16 :: A.Array e -> Int -> e -> A.Array e
update16 ary idx b = runST (update16M ary idx b)
{-# INLINE update16 #-}

-- | /O(n)/ Update the element at the given position in this array.
update16M :: A.Array e -> Int -> e -> ST s (A.Array e)
update16M ary idx b = do
    mary <- clone16 ary
    A.write mary idx b
    A.unsafeFreeze mary
{-# INLINE update16M #-}

-- | /O(n)/ Update the element at the given position in this array, by applying a function to it.
update16With' :: A.Array e -> Int -> (e -> e) -> A.Array e
update16With' ary idx f
  | (# x #) <- A.index# ary idx
  = update16 ary idx $! f x
{-# INLINE update16With' #-}

-- | Unsafely clone an array of 16 elements.  The length of the input
-- array is not checked.
clone16 :: A.Array e -> ST s (A.MArray s e)
clone16 ary =
    A.thaw ary 0 16

------------------------------------------------------------------------
-- Bit twiddling

bitsPerSubkey :: Int
bitsPerSubkey = 4

maxChildren :: Int
maxChildren = fromIntegral $ 1 `unsafeShiftL` bitsPerSubkey

subkeyMask :: Bitmap
subkeyMask = 1 `unsafeShiftL` bitsPerSubkey - 1

sparseIndex :: Bitmap -> Bitmap -> Int
sparseIndex b m = popCount (b .&. (m - 1))

mask :: Word -> Shift -> Bitmap
mask w s = 1 `unsafeShiftL` index w s
{-# INLINE mask #-}

-- | Mask out the 'bitsPerSubkey' bits used for indexing at this level
-- of the tree.
index :: Hash -> Shift -> Int
index w s = fromIntegral $ (unsafeShiftR w s) .&. subkeyMask
{-# INLINE index #-}

-- | A bitmask with the 'bitsPerSubkey' least significant bits set.
fullNodeMask :: Bitmap
fullNodeMask = complement (complement 0 `unsafeShiftL` maxChildren)
{-# INLINE fullNodeMask #-}

-- | Check if two the two arguments are the same value.  N.B. This
-- function might give false negatives (due to GC moving objects.)
ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y ==# 1#)
{-# INLINE ptrEq #-}

------------------------------------------------------------------------
-- IsList instance
instance (Eq k, Hashable k) => Exts.IsList (HashMap k v) where
    type Item (HashMap k v) = (k, v)
    fromList = fromList
    toList   = toList
