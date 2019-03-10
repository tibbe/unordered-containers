{-# LANGUAGE CPP, DeriveDataTypeable #-}
#if __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#endif
#if __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif

------------------------------------------------------------------------
-- |
-- Module      :  Data.HashSet.Base
-- Copyright   :  2011 Bryan O'Sullivan
-- License     :  BSD-style
-- Maintainer  :  johan.tibell@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- A set of /hashable/ values.  A set cannot contain duplicate items.
-- A 'HashSet' makes no guarantees as to the order of its elements.
--
-- The implementation is based on /hash array mapped trie/.  A
-- 'HashSet' is often faster than other tree-based set types,
-- especially when value comparison is expensive, as in the case of
-- strings.
--
-- Many operations have a average-case complexity of /O(log n)/.  The
-- implementation uses a large base (i.e. 16) so in practice these
-- operations are constant time.

module Data.HashSet.Base
    (
      HashSet

    -- * Construction
    , empty
    , singleton

    -- * Combine
    , union
    , unions

    -- * Basic interface
    , null
    , size
    , member
    , insert
    , delete

    -- * Transformations
    , map

      -- * Difference and intersection
    , difference
    , intersection

    -- * Folds
    , foldl'
    , foldr

    -- * Filter
    , filter

    -- * Conversions

    -- ** Lists
    , toList
    , fromList

    -- * HashMaps
    , toMap
    , fromMap

    -- Exported from Data.HashMap.{Strict, Lazy}
    , keysSet
    ) where

import Control.DeepSeq (NFData(..))
import Data.Data hiding (Typeable)
import Data.HashMap.Base (HashMap, foldrWithKey, equalKeys, equalKeys1)
import Data.Hashable (Hashable(hashWithSalt))
#if __GLASGOW_HASKELL__ >= 711
import Data.Semigroup (Semigroup(..))
#elif __GLASGOW_HASKELL__ < 709
import Data.Monoid (Monoid(..))
#endif
import GHC.Exts (build)
import Prelude hiding (filter, foldr, map, null)
import qualified Data.Foldable as Foldable
import qualified Data.HashMap.Base as H
import qualified Data.List as List
import Data.Typeable (Typeable)
import Text.Read

#if __GLASGOW_HASKELL__ >= 708
import qualified GHC.Exts as Exts
#endif

#if MIN_VERSION_base(4,9,0)
import Data.Functor.Classes
#endif

#if MIN_VERSION_hashable(1,2,5)
import qualified Data.Hashable.Lifted as H
#endif

import Data.Functor ((<$))

-- | A set of values.  A set cannot contain duplicate values.
newtype HashSet a = HashSet {
      asMap :: HashMap a ()
    } deriving (Typeable)

#if __GLASGOW_HASKELL__ >= 708
type role HashSet nominal
#endif

instance (NFData a) => NFData (HashSet a) where
    rnf = rnf . asMap
    {-# INLINE rnf #-}

instance (Eq a) => Eq (HashSet a) where
    HashSet a == HashSet b = equalKeys a b
    {-# INLINE (==) #-}

#if MIN_VERSION_base(4,9,0)
instance Eq1 HashSet where
    liftEq eq (HashSet a) (HashSet b) = equalKeys1 eq a b
#endif

instance (Ord a, Hashable a) => Ord (HashSet a) where
    compare (HashSet a) (HashSet b) = compare a b
    {-# INLINE compare #-}

#if MIN_VERSION_base(4,9,0)
instance Ord1 HashSet where
    liftCompare c (HashSet a) (HashSet b) = liftCompare2 c compare a b
#endif

instance Foldable.Foldable HashSet where
    foldr = Data.HashSet.Base.foldr
    {-# INLINE foldr #-}
    foldl' = Data.HashSet.Base.foldl'
    {-# INLINE foldl' #-}
#if MIN_VERSION_base(4,8,0)
    toList = Data.HashSet.Base.toList
    {-# INLINE toList #-}
    null = Data.HashSet.Base.null
    {-# INLINE null #-}
    length = Data.HashSet.Base.size
    {-# INLINE length #-}
#endif

#if __GLASGOW_HASKELL__ >= 711
instance (Hashable a, Eq a) => Semigroup (HashSet a) where
    (<>) = union
    {-# INLINE (<>) #-}
#endif

instance (Hashable a, Eq a) => Monoid (HashSet a) where
    mempty = empty
    {-# INLINE mempty #-}
#if __GLASGOW_HASKELL__ >= 711
    mappend = (<>)
#else
    mappend = union
#endif
    {-# INLINE mappend #-}

instance (Eq a, Hashable a, Read a) => Read (HashSet a) where
    readPrec = parens $ prec 10 $ do
      Ident "fromList" <- lexP
      xs <- readPrec
      return (fromList xs)

    readListPrec = readListPrecDefault

#if MIN_VERSION_base(4,9,0)
instance Show1 HashSet where
    liftShowsPrec sp sl d m =
        showsUnaryWith (liftShowsPrec sp sl) "fromList" d (toList m)
#endif

instance (Show a) => Show (HashSet a) where
    showsPrec d m = showParen (d > 10) $
      showString "fromList " . shows (toList m)

instance (Data a, Eq a, Hashable a) => Data (HashSet a) where
    gfoldl f z m   = z fromList `f` toList m
    toConstr _     = fromListConstr
    gunfold k z c  = case constrIndex c of
        1 -> k (z fromList)
        _ -> error "gunfold"
    dataTypeOf _   = hashSetDataType
    dataCast1 f    = gcast1 f

#if MIN_VERSION_hashable(1,2,6)
instance H.Hashable1 HashSet where
    liftHashWithSalt h s = H.liftHashWithSalt2 h hashWithSalt s . asMap
#endif

instance (Hashable a) => Hashable (HashSet a) where
    hashWithSalt salt = hashWithSalt salt . asMap

fromListConstr :: Constr
fromListConstr = mkConstr hashSetDataType "fromList" [] Prefix

hashSetDataType :: DataType
hashSetDataType = mkDataType "Data.HashSet.Base.HashSet" [fromListConstr]

-- | /O(1)/ Construct an empty set.
empty :: HashSet a
empty = HashSet H.empty

-- | /O(1)/ Construct a set with a single element.
singleton :: Hashable a => a -> HashSet a
singleton a = HashSet (H.singleton a ())
{-# INLINABLE singleton #-}

-- | /O(1)/ Convert to the equivalent 'HashMap'.
toMap :: HashSet a -> HashMap a ()
toMap = asMap

-- | /O(1)/ Convert from the equivalent 'HashMap'.
fromMap :: HashMap a () -> HashSet a
fromMap = HashSet

-- | /O(n)/ Produce a 'HashSet' of all the keys in the given 'HashMap'.
--
-- @since 0.2.10.0
keysSet :: HashMap k a -> HashSet k
keysSet m = fromMap (() <$ m)

-- | /O(n+m)/ Construct a set containing all elements from both sets.
--
-- To obtain good performance, the smaller set must be presented as
-- the first argument.
union :: (Eq a, Hashable a) => HashSet a -> HashSet a -> HashSet a
union s1 s2 = HashSet $ H.union (asMap s1) (asMap s2)
{-# INLINE union #-}

-- TODO: Figure out the time complexity of 'unions'.

-- | Construct a set containing all elements from a list of sets.
unions :: (Eq a, Hashable a) => [HashSet a] -> HashSet a
unions = List.foldl' union empty
{-# INLINE unions #-}

-- | /O(1)/ Return 'True' if this set is empty, 'False' otherwise.
null :: HashSet a -> Bool
null = H.null . asMap
{-# INLINE null #-}

-- | /O(n)/ Return the number of elements in this set.
size :: HashSet a -> Int
size = H.size . asMap
{-# INLINE size #-}

-- | /O(log n)/ Return 'True' if the given value is present in this
-- set, 'False' otherwise.
member :: (Eq a, Hashable a) => a -> HashSet a -> Bool
member a s = case H.lookup a (asMap s) of
               Just _ -> True
               _      -> False
{-# INLINABLE member #-}

-- | /O(log n)/ Add the specified value to this set.
insert :: (Eq a, Hashable a) => a -> HashSet a -> HashSet a
insert a = HashSet . H.insert a () . asMap
{-# INLINABLE insert #-}

-- | /O(log n)/ Remove the specified value from this set if
-- present.
delete :: (Eq a, Hashable a) => a -> HashSet a -> HashSet a
delete a = HashSet . H.delete a . asMap
{-# INLINABLE delete #-}

-- | /O(n)/ Transform this set by applying a function to every value.
-- The resulting set may be smaller than the source.
map :: (Hashable b, Eq b) => (a -> b) -> HashSet a -> HashSet b
map f = fromList . List.map f . toList
{-# INLINE map #-}

-- | /O(n)/ Difference of two sets. Return elements of the first set
-- not existing in the second.
difference :: (Eq a, Hashable a) => HashSet a -> HashSet a -> HashSet a
difference (HashSet a) (HashSet b) = HashSet (H.difference a b)
{-# INLINABLE difference #-}

-- | /O(n)/ Intersection of two sets. Return elements present in both
-- the first set and the second.
intersection :: (Eq a, Hashable a) => HashSet a -> HashSet a -> HashSet a
intersection (HashSet a) (HashSet b) = HashSet (H.intersection a b)
{-# INLINABLE intersection #-}

-- | /O(n)/ Reduce this set by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before before using the result in the next
-- application.  This function is strict in the starting value.
foldl' :: (a -> b -> a) -> a -> HashSet b -> a
foldl' f z0 = H.foldlWithKey' g z0 . asMap
  where g z k _ = f z k
{-# INLINE foldl' #-}

-- | /O(n)/ Reduce this set by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldr :: (b -> a -> a) -> a -> HashSet b -> a
foldr f z0 = foldrWithKey g z0 . asMap
  where g k _ z = f k z
{-# INLINE foldr #-}

-- | /O(n)/ Filter this set by retaining only elements satisfying a
-- predicate.
filter :: (a -> Bool) -> HashSet a -> HashSet a
filter p = HashSet . H.filterWithKey q . asMap
  where q k _ = p k
{-# INLINE filter #-}

-- | /O(n)/ Return a list of this set's elements.  The list is
-- produced lazily.
toList :: HashSet a -> [a]
toList t = build (\ c z -> foldrWithKey ((const .) c) z (asMap t))
{-# INLINE toList #-}

-- | /O(n*min(W, n))/ Construct a set from a list of elements.
fromList :: (Eq a, Hashable a) => [a] -> HashSet a
fromList = HashSet . List.foldl' (\ m k -> H.insert k () m) H.empty
{-# INLINE fromList #-}

#if __GLASGOW_HASKELL__ >= 708
instance (Eq a, Hashable a) => Exts.IsList (HashSet a) where
    type Item (HashSet a) = a
    fromList = fromList
    toList   = toList
#endif
