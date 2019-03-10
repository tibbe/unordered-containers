{-# LANGUAGE BangPatterns, CPP, PatternGuards, MagicHash, UnboxedTuples #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Trustworthy #-}

------------------------------------------------------------------------
-- |
-- Module      :  Data.HashMap.Strict
-- Copyright   :  2010-2012 Johan Tibell
-- License     :  BSD-style
-- Maintainer  :  johan.tibell@gmail.com
-- Stability   :  provisional
-- Portability :  portable
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
module Data.HashMap.Strict.Base
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
    , lookupDefault
    , (!)
    , insert
    , insertWith
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
    , HM.foldr
    , foldrWithKey

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
    ) where

import Data.Bits ((.&.), (.|.))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative (..), (<$>))
#endif
import qualified Data.List as L
import Data.Hashable (Hashable)
import Prelude hiding (map, lookup)

import qualified Data.HashMap.Array as A
import qualified Data.HashMap.Base as HM
import Data.HashMap.Base hiding (
    alter, alterF, adjust, fromList, fromListWith, insert, insertWith,
    differenceWith, intersectionWith, intersectionWithKey, map, mapWithKey,
    mapMaybe, mapMaybeWithKey, singleton, update, unionWith, unionWithKey,
    traverseWithKey)
import Data.HashMap.Unsafe (runST)
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
insertWith f k0 v0 m0 = go h0 s0 k0 v0 0 m0
  where
    h0 = hashWithSalt s0 k0
    s0 = defaultSalt
    go !h _ !k x !_ Empty = leaf h k x
    go h s k x bs (Leaf hy lf@(L ky y))
        | hy == h = if ky == k
                    then leaf h k (f x y)
                    else collision h s lf (l k x)
        | otherwise = x `seq` runST (two bs h k x hy ky y)
    go h s k x bs (BitmapIndexed b ary)
        | b .&. m == 0 =
            let ary' = A.insert ary i $! leaf h k x
            in bitmapIndexedOrFull (b .|. m) ary'
        | otherwise =
            let st   = A.index ary i
                st'  = go h s k x (bs+bitsPerSubkey) st
                ary' = A.update ary i $! st'
            in BitmapIndexed b ary'
      where m = mask h bs
            i = sparseIndex b m
    go h s k x bs (Full ary) =
        let st   = A.index ary i
            st'  = go h s k x (bs+bitsPerSubkey) st
            ary' = update16 ary i $! st'
        in Full ary'
      where i = index h bs
    go h s k x bs t@(Collision hx l1@(L k1 v1) l2@(L k2 v2) hm)
        | h == hx   =
           let go'
                 | k == k1   = Collision hx (l k (f x v1)) l2 hm
                 | k == k2   = Collision hx l1 (l k (f x v2)) hm
                 | otherwise = Collision hx l1 l2 $ go (hashWithSalt (nextSalt s) k) (nextSalt s) k x 0 hm
           in go'
        | otherwise = go h s k x bs $ BitmapIndexed (mask hx bs) (A.singleton t)
{-# INLINABLE insertWith #-}

-- | In-place update version of insertWith
unsafeInsertWith :: (Eq k, Hashable k) => (v -> v -> v) -> k -> v -> HashMap k v
                 -> HashMap k v
unsafeInsertWith f k0 v0 m0 = runST (go h0 s0 k0 v0 0 m0)
  where
    h0 = hashWithSalt s0 k0
    s0 = defaultSalt
    go !h !_ !k x !_ Empty = return $! leaf h k x
    go h s k x bs (Leaf hy lf@(L ky y))
        | hy == h = if ky == k
                    then return $! leaf h k (f x y)
                    else return $! collision h s lf (l k x)
        | otherwise = x `seq` two bs h k x hy ky y
    go h s k x bs t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insertM ary i $! leaf h k x
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
    go h s k x bs t@(Collision hx l1@(L k1 v1) l2@(L k2 v2) hm)
        | h == hx   =
          let go'
                | k == k1   = return $! Collision hx (l k (f x v1)) l2 hm
                | k == k2   = return $! Collision hx l1 (l k (f x v2)) hm
                | otherwise = Collision hx l1 l2 <$> go (hashWithSalt (nextSalt s) k) (nextSalt s) k x 0 hm
          in go'
        | otherwise = go h s k x bs $ BitmapIndexed (mask hx bs) (A.singleton t)
{-# INLINABLE unsafeInsertWith #-}

-- | /O(log n)/ Adjust the value tied to a given key in this map only
-- if it is present. Otherwise, leave the map alone.
adjust :: (Eq k, Hashable k) => (v -> v) -> k -> HashMap k v -> HashMap k v
adjust f k0 m0 = go h0 s0 k0 0 m0
  where
    h0 = hashWithSalt s0 k0
    s0 = defaultSalt
    go !_ !_ !_ !_ Empty = Empty
    go h _ k _ t@(Leaf hy (L ky y))
        | hy == h && ky == k = leaf h k (f y)
        | otherwise          = t
    go h s k bs t@(BitmapIndexed b ary)
        | b .&. m == 0 = t
        | otherwise = let st   = A.index ary i
                          st'  = go h s k (bs+bitsPerSubkey) st
                          ary' = A.update ary i $! st'
                      in BitmapIndexed b ary'
      where m = mask h bs
            i = sparseIndex b m
    go h s k bs (Full ary) =
        let i    = index h bs
            st   = A.index ary i
            st'  = go h s k (bs+bitsPerSubkey) st
            ary' = update16 ary i $! st'
        in Full ary'
    go h s k _ t@(Collision hx l1@(L k1 v1) l2@(L k2 v2) hm)
        | h == hx   =
          let go'
                | k == k1   = Collision hx (L k $! f v1) l2 hm
                | k == k2   = Collision hx l1 (L k $! f v2) hm
                | otherwise = Collision hx l1 l2 $ go (hashWithSalt (nextSalt s) k) (nextSalt s) k 0 hm
          in go'
        | otherwise = t
{-# INLINABLE adjust #-}

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
alter f k m =
  case f (HM.lookup k m) of
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
-- Special care is taken to only calculate the hash once. When we rewrite
-- with RULES, we also ensure that we only compare the key for equality
-- once. We force the value of the map for consistency with the rewritten
-- version; otherwise someone could tell the difference using a lazy
-- @f@ and a functor that is similar to Const but not actually Const.
alterF f = \ !k !m ->
  let !h = hashWithSalt s k
      s = defaultSalt
      mv = lookup' h s k m
  in (<$> f mv) $ \fres ->
    case fres of
      Nothing -> delete' h s k m
      Just !v' -> insert' h s k v' m

-- We rewrite this function unconditionally in RULES, but we expose
-- an unfolding just in case it's used in a context where the rules
-- don't fire.
{-# INLINABLE [0] alterF #-}

#if MIN_VERSION_base(4,8,0)
-- See notes in Data.HashMap.Base
test_bottom :: a
test_bottom = error "Data.HashMap.alterF internal error: hit test_bottom"

bogus# :: (# #) -> (# a #)
bogus# _ = error "Data.HashMap.alterF internal error: hit bogus#"

impossibleAdjust :: a
impossibleAdjust = error "Data.HashMap.alterF internal error: impossible adjust"

{-# RULES

-- See detailed notes on alterF rules in Data.HashMap.Base.

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
alterFEager f !k !m = (<$> f mv) $ \fres ->
  case fres of

    ------------------------------
    -- Delete the key from the map.
    Nothing -> case lookupRes of

      -- Key did not exist in the map to begin with, no-op
      Absent -> m

      -- Key did exist, no collision
      Present _ -> deleteKeyExists h s k m

    ------------------------------
    -- Update value
    Just v' -> case lookupRes of

      -- Key did not exist before, insert v' under a new key
      Absent -> insertNewKey h s k v' m

      -- Key existed before, no hash collision
      Present v -> v' `seq`
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

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the result.
unionWith :: (Eq k, Hashable k) => (v -> v -> v) -> HashMap k v -> HashMap k v
          -> HashMap k v
unionWith f = unionWithKey (const f)
{-# INLINE unionWith #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the result.
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
                      then leaf h1 k1 (f k1 v1 v2)
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

------------------------------------------------------------------------
-- * Transformations

-- | /O(n)/ Transform this map by applying a function to every value.
mapWithKey :: (k -> v1 -> v2) -> HashMap k v1 -> HashMap k v2
mapWithKey f = go
  where
    go Empty                 = Empty
    go (Leaf h (L k v))      = leaf h k (f k v)
    go (BitmapIndexed b ary) = BitmapIndexed b $ A.map' go ary
    go (Full ary)            = Full $ A.map' go ary
    go (Collision h (L k1 v1) (L k2 v2) hm)     =
        Collision h (v1 `seq` (L k1 (f k1 v1))) (v2 `seq` (L k2 (f k2 v2))) (go hm)
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
mapMaybeWithKey f = filterMapAux onLeaf
  where onLeaf (Leaf h (L k v)) | Just v' <- f k v = Just (leaf h k v')
        onLeaf _ = Nothing
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
traverseWithKey f = go
  where
    go Empty                 = pure Empty
    go (Leaf h (L k v))      = leaf h k <$> f k v
    go (BitmapIndexed b ary) = BitmapIndexed b <$> A.traverse' go ary
    go (Full ary)            = Full <$> A.traverse' go ary
    go (Collision h (L k1 v1) (L k2 v2) hm) =
        Collision h <$> (L k1 <$> f k1 v1) <*> (L k2 <$> f k2 v2) <*> go hm
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
-- the provided function f to merge duplicate entries (f newVal oldVal).
--
-- For example:
--
-- > fromListWith (+) [ (x, 1) | x <- xs ]
--
-- will create a map with number of occurrences of each element in xs.
--
-- > fromListWith (++) [ (k, [v]) | (k, v) <- xs ]
--
-- will group all values by their keys in a list 'xs :: [(k, v)]' and
-- return a 'HashMap k [v]'.
fromListWith :: (Eq k, Hashable k) => (v -> v -> v) -> [(k, v)] -> HashMap k v
fromListWith f = L.foldl' (\ m (k, v) -> unsafeInsertWith f k v m) empty
{-# INLINE fromListWith #-}

------------------------------------------------------------------------
-- Smart constructors
--
-- These constructors make sure the value is in WHNF before it's
-- inserted into the constructor.

leaf :: Hash -> k -> v -> HashMap k v
leaf h k = \ !v -> Leaf h (l k v)

l :: k -> v -> Leaf k v
l k = \ !v -> L k v
{-# INLINE leaf #-}
