{-# LANGUAGE BangPatterns, CPP, PatternGuards, MagicHash, UnboxedTuples #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# OPTIONS_HADDOCK not-home #-}

------------------------------------------------------------------------
-- |
-- Module      :  Data.HashMap.Strict
-- Copyright   :  2010-2012 Johan Tibell
-- License     :  BSD-style
-- Maintainer  :  johan.tibell@gmail.com
-- Portability :  portable
--
-- = WARNING
--
-- This module is considered __internal__.
--
-- The Package Versioning Policy __does not apply__.
--
-- The contents of this module may change __in any way whatsoever__
-- and __without any warning__ between minor versions of this package.
--
-- Authors importing this module are expected to track development
-- closely.
--
-- = Description
--
-- A map from /hashable/ keys to values.  A map cannot contain
-- duplicate keys; each key can map to at most one value.  A 'HashMap'
-- makes no guarantees as to the order of its elements.
--
-- The implementation is based on /hash array mapped tries/.  A
-- 'HashMap' is often faster than other tree-based set types,
-- especially when key comparison is expensive, as in the case of
-- strings.
--
-- Many operations have a average-case complexity of /O(log n)/.  The
-- implementation uses a large base (i.e. 16) so in practice these
-- operations are constant time.
module Data.HashMap.Internal.Strict
    (
      -- * Strictness properties
      -- $strictness

      HashMap

      -- * Construction
    , empty
    , singleton

      -- * Basic interface
    , HM.null
    , size
    , HM.member
    , HM.lookup
    , (HM.!?)
    , HM.findWithDefault
    , lookupDefault
    , (!)
    , insert
    , insertWith
    , delete
    , adjust
    , update
    , alter
    , alterF
    , isSubmapOf
    , isSubmapOfBy

      -- * Combine
      -- ** Union
    , union
    , unionWith
    , unionWithKey
    , unions

    -- ** Compose
    , compose

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
    , foldMapWithKey
    , foldr'
    , foldl'
    , foldrWithKey'
    , foldlWithKey'
    , HM.foldr
    , HM.foldl
    , foldrWithKey
    , foldlWithKey

      -- * Filter
    , HM.filter
    , filterWithKey
    , mapMaybe
    , mapMaybeWithKey

      -- * Conversions
    , keys
    , elems

      -- ** Lists
    , toList
    , fromList
    , fromListWith
    , fromListWithKey
    ) where

import Data.Bits ((.&.), (.|.))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative (..), (<$>))
#endif
import qualified Data.List as L
import Data.Hashable (Hashable)
import Prelude hiding (map, lookup)

import qualified Data.HashMap.Internal.Array as A
import qualified Data.HashMap.Internal as HM
import Data.HashMap.Internal hiding (
    alter, alterF, adjust, fromList, fromListWith, fromListWithKey,
    insert, insertWith,
    differenceWith, intersectionWith, intersectionWithKey, map, mapWithKey,
    mapMaybe, mapMaybeWithKey, singleton, update, unionWith, unionWithKey,
    traverseWithKey)
import Data.HashMap.Internal.Unsafe (runST)
#if MIN_VERSION_base(4,8,0)
import Data.Functor.Identity
#endif
import Control.Applicative (Const (..))
import Data.Coerce

-- $strictness
--
-- This module satisfies the following strictness properties:
--
-- 1. Key arguments are evaluated to WHNF;
--
-- 2. Keys and values are evaluated to WHNF before they are stored in
--    the map.

------------------------------------------------------------------------
-- * Construction

-- | /O(1)/ Construct a map with a single element.
singleton :: (Hashable k) => k -> v -> HashMap k v
singleton k !v = HM.singleton k v

------------------------------------------------------------------------
-- * Basic interface

-- | /O(log n)/ Associate the specified value with the specified
-- key in this map.  If this map previously contained a mapping for
-- the key, the old value is replaced.
insert :: (Eq k, Hashable k) => k -> v -> HashMap k v -> HashMap k v
insert k !v = HM.insert k v
{-# INLINABLE insert #-}

-- | /O(log n)/ Associate the value with the key in this map.  If
-- this map previously contained a mapping for the key, the old value
-- is replaced by the result of applying the given function to the new
-- and old value.  Example:
--
-- > insertWith f k v map
-- >   where f new old = new + old
insertWith :: (Eq k, Hashable k) => (v -> v -> v) -> k -> v -> HashMap k v
            -> HashMap k v
insertWith f k0 v0 (HashMap sz m0) =
    let A.Sized diff m0' = insertWithInternal f k0 v0 m0
    in HashMap (diff + sz) m0'
{-# INLINABLE insertWith #-}

-- | /O(log n)/ Associate the value with the key in this map.  If
-- this map previously contained a mapping for the key, the old value
-- is replaced by the result of applying the given function to the new
-- and old value.
-- Returns a tuple where the first component is the
-- difference in size between the old and new hashmaps, and the second
-- is the new hashmap.
-- Example:
-- > insertWith f k v map
-- >   where f new old = new + old
insertWithInternal :: (Eq k, Hashable k) => (v -> v -> v) -> k -> v -> Tree k v
           -> A.Sized (Tree k v)
insertWithInternal f k0 v0 m0 = go h0 k0 v0 0 m0
  where
    h0 = hash k0
    go !h !k x !_ Empty = A.Sized 1 (leaf h k x)
    go h k x s t@(Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then A.Sized 0 (leaf h k (f x y))
                    else A.Sized 1 (x `seq` (collision h l (L k x)))
        | otherwise = A.Sized 1 (x `seq` runST (two s h k x hy t))
    go h k x s (BitmapIndexed b ary)
        | b .&. m == 0 =
            let ary' = A.insert ary i $! leaf h k x
            in A.Sized 1 (bitmapIndexedOrFull (b .|. m) ary')
        | otherwise =
            let st           = A.index ary i
                A.Sized sz st' = go h k x (s+bitsPerSubkey) st
                ary'         = A.update ary i $! st'
            in A.Sized sz (BitmapIndexed b ary')
      where m = mask h s
            i = sparseIndex b m
    go h k x s (Full ary) =
        let st           = A.index ary i
            A.Sized sz st' = go h k x (s+bitsPerSubkey) st
            ary'         = update16 ary i $! st'
        in A.Sized sz (Full ary')
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   =
            let !start = A.length v
                !newV  = updateOrSnocWith f k x v
                !end   = A.length newV
            in A.Sized (A.Size (end - start)) (Collision h newV)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE insertWithInternal #-}

-- | In-place update version of insertWith
unsafeInsertWith :: forall k v . (Eq k, Hashable k)
                 => (v -> v -> v) -> k -> v -> HashMap k v
                 -> HashMap k v
unsafeInsertWith f k0 v0 (HashMap sz m0) =
    let A.Sized diff m0' = unsafeInsertWithKey (const f) k0 v0 m0
    in HashMap (diff + sz) m0'
{-# INLINABLE unsafeInsertWith #-}

unsafeInsertWithKey :: (Eq k, Hashable k) => (k -> v -> v -> v) -> k -> v -> Tree k v
                    -> A.Sized (Tree k v)
unsafeInsertWithKey f k0 v0 m0 = runST (go h0 k0 v0 0 m0)
  where
    h0 = hash k0
    go !h !k x !_ Empty = return $! A.Sized 1 (leaf h k x)
    go h k x s t@(Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then return $! A.Sized 0 (leaf h k (f k x y))
                    else do
                        let l' = x `seq` (L k x)
                        return $! A.Sized 1 (collision h l l')
        | otherwise = do
              twoHM <- x `seq` two s h k x hy t
              return $! A.Sized 1 twoHM
    go h k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insertM ary i $! leaf h k x
            return . A.Sized 1 $! bitmapIndexedOrFull (b .|. m) ary'
        | otherwise = do
            st <- A.indexM ary i
            A.Sized sz st' <- go h k x (s+bitsPerSubkey) st
            A.unsafeUpdateM ary i $! st'
            return . A.Sized sz $! t
      where m = mask h s
            i = sparseIndex b m
    go h k x s t@(Full ary) = do
        st <- A.indexM ary i
        A.Sized sz st' <- go h k x (s+bitsPerSubkey) st
        A.unsafeUpdateM ary i $! st'
        return . A.Sized sz $! t
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   =
            let !start = A.length v
                !newV = updateOrSnocWithKey f k x v
                !end = A.length newV
            in return . A.Sized (A.Size (end - start)) $! Collision h newV
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE unsafeInsertWithKey #-}

-- | /O(log n)/ Adjust the value tied to a given key in this map only
-- if it is present. Otherwise, leave the map alone.
adjust :: (Eq k, Hashable k) => (v -> v) -> k -> HashMap k v -> HashMap k v
adjust f k0 (HashMap sz m0) = HashMap sz (go h0 k0 0 m0)
  where
    h0 = hash k0
    go !_ !_ !_ Empty = Empty
    go h k _ t@(Leaf hy (L ky y))
        | hy == h && ky == k = leaf h k (f y)
        | otherwise          = t
    go h k s t@(BitmapIndexed b ary)
        | b .&. m == 0 = t
        | otherwise = let st   = A.index ary i
                          st'  = go h k (s+bitsPerSubkey) st
                          ary' = A.update ary i $! st'
                      in BitmapIndexed b ary'
      where m = mask h s
            i = sparseIndex b m
    go h k s (Full ary) =
        let i    = index h s
            st   = A.index ary i
            st'  = go h k (s+bitsPerSubkey) st
            ary' = update16 ary i $! st'
        in Full ary'
    go h k _ t@(Collision hy v)
        | h == hy   = Collision h (updateWith f k v)
        | otherwise = t
{-# INLINABLE adjust #-}

-- | /O(log n)/  The expression @('update' f k map)@ updates the value @x@ at @k@
-- (if it is in the map). If @(f x)@ is 'Nothing', the element is deleted.
-- If it is @('Just' y)@, the key @k@ is bound to the new value @y@.
update :: (Eq k, Hashable k) => (a -> Maybe a) -> k -> HashMap k a -> HashMap k a
update f = alter (>>= f)
{-# INLINABLE update #-}

-- | /O(log n)/  The expression @('alter' f k map)@ alters the value @x@ at @k@, or
-- absence thereof.
--
-- 'alter' can be used to insert, delete, or update a value in a map. In short:
--
-- @
-- 'lookup' k ('alter' f k m) = f ('lookup' k m)
-- @
alter :: (Eq k, Hashable k) => (Maybe v -> Maybe v) -> k -> HashMap k v -> HashMap k v
alter f k m =
  case f (HM.lookup k m) of
    Nothing -> delete k m
    Just v  -> insert k v m
{-# INLINABLE alter #-}

-- | /O(log n)/  The expression (@'alterF' f k map@) alters the value @x@ at
-- @k@, or absence thereof.
--
-- 'alterF' can be used to insert, delete, or update a value in a map.
--
-- Note: 'alterF' is a flipped version of the 'at' combinator from
-- <https://hackage.haskell.org/package/lens/docs/Control-Lens-At.html#v:at Control.Lens.At>.
--
-- @since 0.2.10
alterF :: (Functor f, Eq k, Hashable k)
       => (Maybe v -> f (Maybe v)) -> k -> HashMap k v -> f (HashMap k v)
-- Special care is taken to only calculate the hash once. When we rewrite
-- with RULES, we also ensure that we only compare the key for equality
-- once. We force the value of the map for consistency with the rewritten
-- version; otherwise someone could tell the difference using a lazy
-- @f@ and a functor that is similar to Const but not actually Const.
alterF f = \ !k !m ->
  let !h = hash k
      mv = lookup' h k m
  in (<$> f mv) $ \fres ->
    case fres of
      Nothing -> maybe m (const (delete' h k m)) mv
      Just !v' -> insert' h k v' m

-- We rewrite this function unconditionally in RULES, but we expose
-- an unfolding just in case it's used in a context where the rules
-- don't fire.
{-# INLINABLE [0] alterF #-}

#if MIN_VERSION_base(4,8,0)
-- See notes in Data.HashMap.Internal
test_bottom :: a
test_bottom = error "Data.HashMap.alterF internal error: hit test_bottom"

bogus# :: (# #) -> (# a #)
bogus# _ = error "Data.HashMap.alterF internal error: hit bogus#"

impossibleAdjust :: a
impossibleAdjust = error "Data.HashMap.alterF internal error: impossible adjust"

{-# RULES

-- See detailed notes on alterF rules in Data.HashMap.Internal.

"alterFWeird" forall f. alterF f =
    alterFWeird (f Nothing) (f (Just test_bottom)) f

"alterFconstant" forall (f :: Maybe a -> Identity (Maybe a)) x.
  alterFWeird x x f = \ !k !m ->
    Identity (case runIdentity x of {Nothing -> delete k m; Just a -> insert k a m})

"alterFinsertWith" [1] forall (f :: Maybe a -> Identity (Maybe a)) x y.
  alterFWeird (coerce (Just x)) (coerce (Just y)) f =
    coerce (insertModifying x (\mold -> case runIdentity (f (Just mold)) of
                                            Nothing -> bogus# (# #)
                                            Just !new -> (# new #)))

-- This rule is written a bit differently than the one for lazy
-- maps because the adjust here is strict. We could write it the
-- same general way anyway, but this seems simpler.
"alterFadjust" forall (f :: Maybe a -> Identity (Maybe a)) x.
  alterFWeird (coerce Nothing) (coerce (Just x)) f =
    coerce (adjust (\a -> case runIdentity (f (Just a)) of
                               Just a' -> a'
                               Nothing -> impossibleAdjust))

"alterFlookup" forall _ign1 _ign2 (f :: Maybe a -> Const r (Maybe a)) .
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
alterFEager f !k !hm@(HashMap sz m) = (<$> f mv) $ \fres ->
  case fres of

    ------------------------------
    -- Delete the key from the map.
    Nothing -> case lookupRes of

      -- Key did not exist in the map to begin with, no-op
      Absent -> hm

      -- Key did exist, no collision
      Present _ collPos -> HashMap (sz - 1) (deleteKeyExists collPos h k m)

    ------------------------------
    -- Update value
    Just v' -> case lookupRes of

      -- Key did not exist before, insert v' under a new key
      Absent -> HashMap (sz + 1) (insertNewKey h k v' m)

      -- Key existed before, no hash collision
      Present v collPos -> v' `seq`
        if v `ptrEq` v'
        -- If the value is identical, no-op
        then hm
        -- If the value changed, update the value.
        else HashMap sz (insertKeyExists collPos h k v' m)

  where !h = hash k
        !lookupRes = lookupRecordCollision h k m
        !mv = case lookupRes of
          Absent -> Nothing
          Present v _ -> Just v
{-# INLINABLE alterFEager #-}
#endif

------------------------------------------------------------------------
-- * Combine

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the result.
unionWith :: (Eq k, Hashable k) => (v -> v -> v) -> HashMap k v -> HashMap k v
          -> HashMap k v
unionWith f = unionWithKey (const f)
{-# INLINE unionWith #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
unionWithKey
    :: (Eq k, Hashable k)
    => (k -> v -> v -> v)
    -> HashMap k v
    -> HashMap k v
    -> HashMap k v
unionWithKey f (HashMap sz m) hw =
    let A.Sized diff m' = unionWithKeyInternal f m hw
    in HashMap (diff + sz) m'
{-# INLINE unionWithKey #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the result.
unionWithKeyInternal
    :: (Eq k, Hashable k)
    => (k -> v -> v -> v)
    -> Tree k v
    -> HashMap k v
    -> A.Sized (Tree k v)
unionWithKeyInternal f hm1 (HashMap siz hm2) = go 0 siz hm1 hm2
  where
    -- empty vs. anything
    go !_ !sz t1 Empty = A.Sized sz t1
    go _ !sz Empty t2 = A.Sized sz t2
    -- leaf vs. leaf
    go s !sz t1@(Leaf h1 l1@(L k1 v1)) t2@(Leaf h2 l2@(L k2 v2))
        | h1 == h2  = if k1 == k2
                      then A.Sized (sz - 1) (Leaf h1 (L k1 (f k1 v1 v2)))
                      else A.Sized sz (collision h1 l1 l2)
        | otherwise = goDifferentHash s sz h1 h2 t1 t2
    go s !sz t1@(Leaf h1 (L k1 v1)) t2@(Collision h2 ls2)
        | h1 == h2  =
            let !start = A.length ls2
                !newV = updateOrSnocWithKey f k1 v1 ls2
                !end = A.length newV
            in A.Sized (sz + A.Size (end - start - 1)) (Collision h1 newV)
        | otherwise = goDifferentHash s sz h1 h2 t1 t2
    go s !sz t1@(Collision h1 ls1) t2@(Leaf h2 (L k2 v2))
        | h1 == h2  =
            let !start = A.length ls1
                !newV = updateOrSnocWithKey (flip . f) k2 v2 ls1
                !end = A.length newV
            in A.Sized (sz + A.Size (end - start - 1)) (Collision h1 newV)
        | otherwise = goDifferentHash s sz h1 h2 t1 t2
    go s !sz t1@(Collision h1 ls1) t2@(Collision h2 ls2)
        | h1 == h2  =
            let !start = A.length ls1
                !newV = updateOrConcatWithKey f ls1 ls2
                !end = A.length newV
            in A.Sized (sz + A.Size (end - start - A.length ls2))
                       (Collision h1 newV)
        | otherwise = goDifferentHash s sz h1 h2 t1 t2
    -- branch vs. branch
    go s !sz (BitmapIndexed b1 ary1) (BitmapIndexed b2 ary2) =
        let b'         = b1 .|. b2
            A.RunResA dsz ary' =
                unionArrayByInternal sz
                                     (go (s+bitsPerSubkey))
                                     b1
                                     b2
                                     ary1
                                     ary2
        in A.Sized dsz (bitmapIndexedOrFull b' ary')
    go s !sz (BitmapIndexed b1 ary1) (Full ary2) =
        let A.RunResA dsz ary' =
                unionArrayByInternal sz
                                     (go (s+bitsPerSubkey))
                                     b1
                                     fullNodeMask
                                     ary1
                                     ary2
        in A.Sized dsz (Full ary')
    go s !sz (Full ary1) (BitmapIndexed b2 ary2) =
        let A.RunResA dsz ary' =
                unionArrayByInternal sz
                                     (go (s+bitsPerSubkey))
                                     fullNodeMask
                                     b2
                                     ary1
                                     ary2
        in A.Sized dsz (Full ary')
    go s !sz (Full ary1) (Full ary2) =
        let A.RunResA dsz ary' =
                unionArrayByInternal sz
                                     (go (s+bitsPerSubkey))
                                     fullNodeMask
                                     fullNodeMask
                                     ary1
                                     ary2
        in A.Sized dsz (Full ary')
    -- leaf vs. branch
    go s !sz (BitmapIndexed b1 ary1) t2
        | b1 .&. m2 == 0 = let ary' = A.insert ary1 i t2
                               b'   = b1 .|. m2
                           in A.Sized sz (bitmapIndexedOrFull b' ary')
        | otherwise      = let A.RunResA dsz ary' =
                                   A.updateWithInternal' ary1 i $ \st1 ->
                                       go (s+bitsPerSubkey) sz st1 t2
                           in A.Sized dsz (BitmapIndexed b1 ary')
        where
          h2 = leafHashCode t2
          m2 = mask h2 s
          i = sparseIndex b1 m2
    go s !sz t1 (BitmapIndexed b2 ary2)
        | b2 .&. m1 == 0 = let ary' = A.insert ary2 i $! t1
                               b'   = b2 .|. m1
                           in A.Sized sz (bitmapIndexedOrFull b' ary')
        | otherwise      = let A.RunResA dsz ary' =
                                   A.updateWithInternal' ary2 i $ \st2 ->
                                       go (s+bitsPerSubkey) sz t1 st2
                           in A.Sized dsz (BitmapIndexed b2 ary')
      where
        h1 = leafHashCode t1
        m1 = mask h1 s
        i = sparseIndex b2 m1
    go s !sz (Full ary1) t2 =
        let h2   = leafHashCode t2
            i    = index h2 s
            A.RunResA dsz ary' =
                update16WithInternal' ary1 i $ \st1 ->
                    go (s+bitsPerSubkey) sz st1 t2
        in A.Sized dsz (Full ary')
    go s !sz t1 (Full ary2) =
        let h1   = leafHashCode t1
            i    = index h1 s
            A.RunResA dsz ary' =
                update16WithInternal' ary2 i $ \st2 ->
                    go (s+bitsPerSubkey) sz t1 st2
        in A.Sized dsz (Full ary')

    leafHashCode (Leaf h _) = h
    leafHashCode (Collision h _) = h
    leafHashCode _ = error "leafHashCode"

    goDifferentHash s sz h1 h2 t1 t2
        | m1 == m2  = let A.Sized dsz hm = go (s+bitsPerSubkey) sz t1 t2
                      in A.Sized dsz (BitmapIndexed m1 (A.singleton hm))
        | m1 <  m2  = A.Sized sz (BitmapIndexed (m1 .|. m2) (A.pair t1 t2))
        | otherwise = A.Sized sz (BitmapIndexed (m1 .|. m2) (A.pair t2 t1))
      where
        m1 = mask h1 s
        m2 = mask h2 s
{-# INLINE unionWithKeyInternal #-}

------------------------------------------------------------------------
-- * Transformations

-- | /O(n)/ Transform this map by applying a function to every value.
mapWithKey :: (k -> v1 -> v2) -> HashMap k v1 -> HashMap k v2
mapWithKey f (HashMap sz m) = HashMap sz (go m)
  where
    go Empty                 = Empty
    go (Leaf h (L k v))      = leaf h k (f k v)
    go (BitmapIndexed b ary) = BitmapIndexed b $ A.map' go ary
    go (Full ary)            = Full $ A.map' go ary
    go (Collision h ary)     =
        Collision h $ A.map' (\ (L k v) -> let !v' = f k v in L k v') ary
{-# INLINE mapWithKey #-}

-- | /O(n)/ Transform this map by applying a function to every value.
map :: (v1 -> v2) -> HashMap k v1 -> HashMap k v2
map f = mapWithKey (const f)
{-# INLINE map #-}


------------------------------------------------------------------------
-- * Filter

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only some of them.
mapMaybeWithKey :: (k -> v1 -> Maybe v2) -> HashMap k v1 -> HashMap k v2
mapMaybeWithKey f (HashMap _ m) = HashMap size' m'
  where onLeaf (Leaf h (L k v)) | Just v' <- f k v = Just (leaf h k v')
        onLeaf _ = Nothing

        onColl (L k v) | Just v' <- f k v = Just (L k v')
                       | otherwise = Nothing

        A.Sized size' m' = filterMapAuxInternal onLeaf onColl m
{-# INLINE mapMaybeWithKey #-}

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only some of them.
mapMaybe :: (v1 -> Maybe v2) -> HashMap k v1 -> HashMap k v2
mapMaybe f = mapMaybeWithKey (const f)
{-# INLINE mapMaybe #-}

-- | /O(n)/ Perform an 'Applicative' action for each key-value pair
-- in a 'HashMap' and produce a 'HashMap' of all the results. Each 'HashMap'
-- will be strict in all its values.
--
-- @
-- traverseWithKey f = fmap ('map' id) . "Data.HashMap.Lazy".'Data.HashMap.Lazy.traverseWithKey' f
-- @
--
-- Note: the order in which the actions occur is unspecified. In particular,
-- when the map contains hash collisions, the order in which the actions
-- associated with the keys involved will depend in an unspecified way on
-- their insertion order.
traverseWithKey
  :: Applicative f
  => (k -> v1 -> f v2)
  -> HashMap k v1 -> f (HashMap k v2)
traverseWithKey f (HashMap sz m) = HashMap sz <$> go m
  where
    go Empty                 = pure Empty
    go (Leaf h (L k v))      = leaf h k <$> f k v
    go (BitmapIndexed b ary) = BitmapIndexed b <$> A.traverse' go ary
    go (Full ary)            = Full <$> A.traverse' go ary
    go (Collision h ary)     =
        Collision h <$> A.traverse' (\ (L k v) -> (L k $!) <$> f k v) ary
{-# INLINE traverseWithKey #-}

------------------------------------------------------------------------
-- * Difference and intersection

-- | /O(n*log m)/ Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the values of these keys.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
differenceWith :: (Eq k, Hashable k) => (v -> w -> Maybe v) -> HashMap k v -> HashMap k w -> HashMap k v
differenceWith f a b = foldlWithKey' go empty a
  where
    go m k v = case HM.lookup k b of
                 Nothing -> insert k v m
                 Just w  -> maybe m (\y -> insert k y m) (f v w)
{-# INLINABLE differenceWith #-}

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
intersectionWith :: (Eq k, Hashable k) => (v1 -> v2 -> v3) -> HashMap k v1
                 -> HashMap k v2 -> HashMap k v3
intersectionWith f a b = foldlWithKey' go empty a
  where
    go m k v = case HM.lookup k b of
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
    go m k v = case HM.lookup k b of
                 Just w -> insert k (f k v w) m
                 _      -> m
{-# INLINABLE intersectionWithKey #-}

------------------------------------------------------------------------
-- ** Lists

-- | /O(n*log n)/ Construct a map with the supplied mappings.  If the
-- list contains duplicate mappings, the later mappings take
-- precedence.
fromList :: (Eq k, Hashable k) => [(k, v)] -> HashMap k v
fromList = L.foldl' (\ m (k, !v) -> HM.unsafeInsert k v m) empty
{-# INLINABLE fromList #-}

-- | /O(n*log n)/ Construct a map from a list of elements.  Uses
-- the provided function @f@ to merge duplicate entries with
-- @(f newVal oldVal)@.
--
-- === Examples
--
-- Given a list @xs@, create a map with the number of occurrences of each
-- element in @xs@:
--
-- > let xs = ['a', 'b', 'a']
-- > in fromListWith (+) [ (x, 1) | x <- xs ]
-- >
-- > = fromList [('a', 2), ('b', 1)]
--
-- Given a list of key-value pairs @xs :: [(k, v)]@, group all values by their
-- keys and return a @HashMap k [v]@.
--
-- > let xs = ('a', 1), ('b', 2), ('a', 3)]
-- > in fromListWith (++) [ (k, [v]) | (k, v) <- xs ]
-- >
-- > = fromList [('a', [3, 1]), ('b', [2])]
--
-- Note that the lists in the resulting map contain elements in reverse order
-- from their occurences in the original list.
--
-- More generally, duplicate entries are accumulated as follows;
-- this matters when @f@ is not commutative or not associative.
--
-- > fromListWith f [(k, a), (k, b), (k, c), (k, d)]
-- > = fromList [(k, f d (f c (f b a)))]
fromListWith :: (Eq k, Hashable k) => (v -> v -> v) -> [(k, v)] -> HashMap k v
fromListWith f = L.foldl' (\ m (k, v) -> unsafeInsertWith f k v m) empty
{-# INLINE fromListWith #-}

-- | /O(n*log n)/ Construct a map from a list of elements.  Uses
-- the provided function to merge duplicate entries.
--
-- === Examples
--
-- Given a list of key-value pairs where the keys are of different flavours, e.g:
--
-- > data Key = Div | Sub
--
-- and the values need to be combined differently when there are duplicates,
-- depending on the key:
--
-- > combine Div = div
-- > combine Sub = (-)
--
-- then @fromListWithKey@ can be used as follows:
--
-- > fromListWithKey combine [(Div, 2), (Div, 6), (Sub, 2), (Sub, 3)]
-- > = fromList [(Div, 3), (Sub, 1)]
--
-- More generally, duplicate entries are accumulated as follows;
--
-- > fromListWith f [(k, a), (k, b), (k, c), (k, d)]
-- > = fromList [(k, f k d (f k c (f k b a)))]
--
-- @since 0.2.11
fromListWithKey :: (Eq k, Hashable k) => (k -> v -> v -> v) -> [(k, v)] -> HashMap k v
fromListWithKey f = L.foldl' (\ (HashMap sz m) (k, v) ->
     let A.Sized diff m' = unsafeInsertWithKey f k v m
     in HashMap (sz + diff) m') empty
{-# INLINE fromListWithKey #-}

------------------------------------------------------------------------
-- Array operations

updateWith :: Eq k => (v -> v) -> k -> A.Array (Leaf k v) -> A.Array (Leaf k v)
updateWith f k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go !k !ary !i !n
        | i >= n    = ary
        | otherwise = case A.index ary i of
            (L kx y) | k == kx   -> let !v' = f y in A.update ary i (L k v')
                     | otherwise -> go k ary (i+1) n
{-# INLINABLE updateWith #-}

-- | Append the given key and value to the array. If the key is
-- already present, instead update the value of the key by applying
-- the given function to the new and old value (in that order). The
-- value is always evaluated to WHNF before being inserted into the
-- array.
updateOrSnocWith :: Eq k => (v -> v -> v) -> k -> v -> A.Array (Leaf k v)
                 -> A.Array (Leaf k v)
updateOrSnocWith f = updateOrSnocWithKey (const f)
{-# INLINABLE updateOrSnocWith #-}

-- | Append the given key and value to the array. If the key is
-- already present, instead update the value of the key by applying
-- the given function to the new and old value (in that order). The
-- value is always evaluated to WHNF before being inserted into the
-- array.
updateOrSnocWithKey :: Eq k => (k -> v -> v -> v) -> k -> v -> A.Array (Leaf k v)
                 -> A.Array (Leaf k v)
updateOrSnocWithKey f k0 v0 ary0 = go k0 v0 ary0 0 (A.length ary0)
  where
    go !k v !ary !i !n
        | i >= n = A.run $ do
            -- Not found, append to the end.
            mary <- A.new_ (n + 1)
            A.copy ary 0 mary 0 n
            let !l = v `seq` (L k v)
            A.write mary n l
            return mary
        | otherwise = case A.index ary i of
            (L kx y) | k == kx   -> let !v' = f k v y in A.update ary i (L k v')
                     | otherwise -> go k v ary (i+1) n
{-# INLINABLE updateOrSnocWithKey #-}

------------------------------------------------------------------------
-- Smart constructors
--
-- These constructors make sure the value is in WHNF before it's
-- inserted into the constructor.

leaf :: Hash -> k -> v -> Tree k v
leaf h k = \ !v -> Leaf h (L k v)
{-# INLINE leaf #-}
