{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}

-- | Tests for the 'Data.HashMap.Lazy' module.  We test functions by
-- comparing them to a simpler model, an association list.

module Main (main) where

import Control.Monad ( guard )
import qualified Data.Foldable as Foldable
import Data.Function (on)
import Data.Hashable (Hashable(hashWithSalt))
import qualified Data.List as L
import Data.Ord (comparing)
#if defined(STRICT)
import qualified Data.HashMap.Strict as HM
#else
import qualified Data.HashMap.Lazy as HM
#endif
import qualified Data.Map as M
import Test.QuickCheck (Arbitrary, Property, (==>), (===))
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)

-- Key type that generates more hash collisions.
newtype Key = K { unK :: Int }
            deriving (Arbitrary, Eq, Ord, Read, Show)

instance Hashable Key where
    hashWithSalt salt k = hashWithSalt salt (unK k) `mod` 20

------------------------------------------------------------------------
-- * Properties

------------------------------------------------------------------------
-- ** Instances

pEq :: [(Key, Int)] -> [(Key, Int)] -> Bool
pEq xs = (M.fromList xs ==) `eq` (HM.fromList xs ==)

pNeq :: [(Key, Int)] -> [(Key, Int)] -> Bool
pNeq xs = (M.fromList xs /=) `eq` (HM.fromList xs /=)

pReadShow :: [(Key, Int)] -> Bool
pReadShow xs = M.fromList xs == read (show (M.fromList xs))

pFunctor :: [(Key, Int)] -> Bool
pFunctor = fmap (+ 1) `eq_` fmap (+ 1)

pFoldable :: [(Int, Int)] -> Bool
pFoldable = (L.sort . Foldable.foldr (:) []) `eq`
            (L.sort . Foldable.foldr (:) [])

pHashable :: [(Key, Int)] -> [Int] -> Int -> Property
pHashable xs is salt =
    x == y ==> hashWithSalt salt x === hashWithSalt salt y
  where
    ys = shuffle is xs
    x = HM.fromList xs
    y = HM.fromList ys
    -- Shuffle the list using indexes in the second
    shuffle :: [Int] -> [a] -> [a]
    shuffle idxs = L.map snd
                 . L.sortBy (comparing fst)
                 . L.zip (idxs ++ [L.maximum (0:is) + 1 ..])

------------------------------------------------------------------------
-- ** Basic interface

pSize :: [(Key, Int)] -> Bool
pSize = M.size `eq` HM.size

pMember :: Key -> [(Key, Int)] -> Bool
pMember k = M.member k `eq` HM.member k

pLookup :: Key -> [(Key, Int)] -> Bool
pLookup k = M.lookup k `eq` HM.lookup k

pInsert :: Key -> Int -> [(Key, Int)] -> Bool
pInsert k v = M.insert k v `eq_` HM.insert k v

pDelete :: Key -> [(Key, Int)] -> Bool
pDelete k = M.delete k `eq_` HM.delete k

newtype AlwaysCollide = AC Int
    deriving (Arbitrary, Eq, Ord, Show)

instance Hashable AlwaysCollide where
    hashWithSalt _ _ = 1

-- White-box test that tests the case of deleting one of two keys from
-- a map, where the keys' hash values collide.
pDeleteCollision :: AlwaysCollide -> AlwaysCollide -> AlwaysCollide -> Int
                 -> Property
pDeleteCollision k1 k2 k3 idx = (k1 /= k2) && (k2 /= k3) && (k1 /= k3) ==>
                                HM.member toKeep $ HM.delete toDelete $
                                HM.fromList [(k1, 1 :: Int), (k2, 2), (k3, 3)]
  where
    which = idx `mod` 3
    toDelete
        | which == 0 = k1
        | which == 1 = k2
        | which == 2 = k3
        | otherwise = error "Impossible"
    toKeep
        | which == 0 = k2
        | which == 1 = k3
        | which == 2 = k1
        | otherwise = error "Impossible"

pInsertWith :: Key -> [(Key, Int)] -> Bool
pInsertWith k = M.insertWith (+) k 1 `eq_` HM.insertWith (+) k 1

pAdjust :: Key -> [(Key, Int)] -> Bool
pAdjust k = M.adjust succ k `eq_` HM.adjust succ k

pUpdateAdjust :: Key -> [(Key, Int)] -> Bool
pUpdateAdjust k = M.update (Just . succ) k `eq_` HM.update (Just . succ) k

pUpdateDelete :: Key -> [(Key, Int)] -> Bool
pUpdateDelete k = M.update (const Nothing) k `eq_` HM.update (const Nothing) k

pAlterAdjust :: Key -> [(Key, Int)] -> Bool
pAlterAdjust k = M.alter (fmap succ) k `eq_` HM.alter (fmap succ) k

pAlterInsert :: Key -> [(Key, Int)] -> Bool
pAlterInsert k = M.alter (const $ Just 3) k `eq_` HM.alter (const $ Just 3) k

pAlterDelete :: Key -> [(Key, Int)] -> Bool
pAlterDelete k = M.alter (const Nothing) k `eq_` HM.alter (const Nothing) k

------------------------------------------------------------------------
-- ** Combine

pUnion :: [(Key, Int)] -> [(Key, Int)] -> Bool
pUnion xs ys = M.union (M.fromList xs) `eq_` HM.union (HM.fromList xs) $ ys

pUnionWith :: [(Key, Int)] -> [(Key, Int)] -> Bool
pUnionWith xs ys = M.unionWith (-) (M.fromList xs) `eq_`
                   HM.unionWith (-) (HM.fromList xs) $ ys

pUnions :: [[(Key, Int)]] -> Bool
pUnions xss = M.toAscList (M.unions (map M.fromList xss)) ==
              toAscList (HM.unions (map HM.fromList xss))

------------------------------------------------------------------------
-- ** Transformations

pMap :: [(Key, Int)] -> Bool
pMap = M.map (+ 1) `eq_` HM.map (+ 1)

pMapAccum :: Int -> [(Key, Int)] -> Bool
pMapAccum n = (M.mapAccum  (\a b -> (a + 1, b+1)) n) `eq'` (HM.mapAccum (\a b -> (a + 1, b+1)) n)

------------------------------------------------------------------------
-- ** Difference and intersection

pDifference :: [(Key, Int)] -> [(Key, Int)] -> Bool
pDifference xs ys = M.difference (M.fromList xs) `eq_`
                    HM.difference (HM.fromList xs) $ ys

pIntersection :: [(Key, Int)] -> [(Key, Int)] -> Bool
pIntersection xs ys = M.intersection (M.fromList xs) `eq_`
                      HM.intersection (HM.fromList xs) $ ys

pIntersectionWith :: [(Key, Int)] -> [(Key, Int)] -> Bool
pIntersectionWith xs ys = M.intersectionWith (-) (M.fromList xs) `eq_`
                          HM.intersectionWith (-) (HM.fromList xs) $ ys

pIntersectionWithKey :: [(Key, Int)] -> [(Key, Int)] -> Bool
pIntersectionWithKey xs ys = M.intersectionWithKey go (M.fromList xs) `eq_`
                             HM.intersectionWithKey go (HM.fromList xs) $ ys
  where
    go :: Key -> Int -> Int -> Int
    go (K k) i1 i2 = k - i1 - i2

------------------------------------------------------------------------
-- ** Folds

pFoldr :: [(Int, Int)] -> Bool
pFoldr = (L.sort . M.fold (:) []) `eq` (L.sort . HM.foldr (:) [])

pFoldrWithKey :: [(Int, Int)] -> Bool
pFoldrWithKey = (sortByKey . M.foldrWithKey f []) `eq`
                (sortByKey . HM.foldrWithKey f [])
  where f k v z = (k, v) : z

pFoldl' :: Int -> [(Int, Int)] -> Bool
pFoldl' z0 = foldlWithKey'Map (\ z _ v -> v + z) z0 `eq` HM.foldl' (+) z0

foldlWithKey'Map :: (b -> k -> a -> b) -> b -> M.Map k a -> b
#if MIN_VERSION_containers(4,2,0)
foldlWithKey'Map = M.foldlWithKey'
#else
-- Equivalent except for bottoms, which we don't test.
foldlWithKey'Map = M.foldlWithKey
#endif

------------------------------------------------------------------------
-- ** Filter

pMapMaybeWithKey :: [(Key, Int)] -> Bool
pMapMaybeWithKey = M.mapMaybeWithKey f `eq_` HM.mapMaybeWithKey f
  where f k v = guard (odd (unK k + v)) >> Just (v + 1)

pMapMaybe :: [(Key, Int)] -> Bool
pMapMaybe = M.mapMaybe f `eq_` HM.mapMaybe f
  where f v = guard (odd v) >> Just (v + 1)

pFilter :: [(Key, Int)] -> Bool
pFilter = M.filter odd `eq_` HM.filter odd

pFilterWithKey :: [(Key, Int)] -> Bool
pFilterWithKey = M.filterWithKey p `eq_` HM.filterWithKey p
  where p k v = odd (unK k + v)

------------------------------------------------------------------------
-- ** Conversions

-- 'eq_' already calls fromList.
pFromList :: [(Key, Int)] -> Bool
pFromList = id `eq_` id

pFromListWith :: [(Key, Int)] -> Bool
pFromListWith kvs = (M.toAscList $ M.fromListWith (+) kvs) ==
                    (toAscList $ HM.fromListWith (+) kvs)

pToList :: [(Key, Int)] -> Bool
pToList = M.toAscList `eq` toAscList

pElems :: [(Key, Int)] -> Bool
pElems = (L.sort . M.elems) `eq` (L.sort . HM.elems)

pKeys :: [(Key, Int)] -> Bool
pKeys = (L.sort . M.keys) `eq` (L.sort . HM.keys)

------------------------------------------------------------------------
-- * Test list

tests :: [Test]
tests =
    [
    -- Instances
      testGroup "instances"
      [ testProperty "==" pEq
      , testProperty "/=" pNeq
      , testProperty "Read/Show" pReadShow
      , testProperty "Functor" pFunctor
      , testProperty "Foldable" pFoldable
      , testProperty "Hashable" pHashable
      ]
    -- Basic interface
    , testGroup "basic interface"
      [ testProperty "size" pSize
      , testProperty "member" pMember
      , testProperty "lookup" pLookup
      , testProperty "insert" pInsert
      , testProperty "delete" pDelete
      , testProperty "deleteCollision" pDeleteCollision
      , testProperty "insertWith" pInsertWith
      , testProperty "adjust" pAdjust
      , testProperty "updateAdjust" pUpdateAdjust
      , testProperty "updateDelete" pUpdateDelete
      , testProperty "alterAdjust" pAlterAdjust
      , testProperty "alterInsert" pAlterInsert
      , testProperty "alterDelete" pAlterDelete
      ]
    -- Combine
    , testProperty "union" pUnion
    , testProperty "unionWith" pUnionWith
    , testProperty "unions" pUnions
    -- Transformations
    , testProperty "map" pMap
    , testProperty "mapAccum" pMapAccum
    -- Folds
    , testGroup "folds"
      [ testProperty "foldr" pFoldr
      , testProperty "foldrWithKey" pFoldrWithKey
      , testProperty "foldl'" pFoldl'
      ]
    , testGroup "difference and intersection"
      [ testProperty "difference" pDifference
      , testProperty "intersection" pIntersection
      , testProperty "intersectionWith" pIntersectionWith
      , testProperty "intersectionWithKey" pIntersectionWithKey
      ]
    -- Filter
    , testGroup "filter"
      [ testProperty "filter" pFilter
      , testProperty "filterWithKey" pFilterWithKey
      , testProperty "mapMaybe" pMapMaybe
      , testProperty "mapMaybeWithKey" pMapMaybeWithKey
      ]
    -- Conversions
    , testGroup "conversions"
      [ testProperty "elems" pElems
      , testProperty "keys" pKeys
      , testProperty "fromList" pFromList
      , testProperty "fromListWith" pFromListWith
      , testProperty "toList" pToList
      ]
    ]

------------------------------------------------------------------------
-- * Model

type Model k v = M.Map k v

-- | Check that a function operating on a 'HashMap' is equivalent to
-- one operating on a 'Model'.
eq :: (Eq a, Eq k, Hashable k, Ord k)
   => (Model k v -> a)       -- ^ Function that modifies a 'Model'
   -> (HM.HashMap k v -> a)  -- ^ Function that modified a 'HashMap' in the same
                             -- way
   -> [(k, v)]               -- ^ Initial content of the 'HashMap' and 'Model'
   -> Bool                   -- ^ True if the functions are equivalent
eq f g xs = g (HM.fromList xs) == f (M.fromList xs)

eq' :: (Eq a, Eq k, Eq v, Hashable k, Ord k)
    => (Model k v -> (a,Model k v))       -- ^ Function that modifies a 'Model'
    -> (HM.HashMap k v -> (a,HM.HashMap k v))  -- ^ Function that modified a 'HashMap' in the same
                              -- way
    -> [(k, v)]               -- ^ Initial content of the 'HashMap' and 'Model'
    -> Bool                   -- ^ True if the functions are equivalent
eq' f g xs = (aS == aT) && (M.toAscList t == toAscList s)
    where (aS,s) = g (HM.fromList xs) 
          (aT,t) = f (M.fromList xs)

eq_ :: (Eq k, Eq v, Hashable k, Ord k)
    => (Model k v -> Model k v)            -- ^ Function that modifies a 'Model'
    -> (HM.HashMap k v -> HM.HashMap k v)  -- ^ Function that modified a
                                           -- 'HashMap' in the same way
    -> [(k, v)]                            -- ^ Initial content of the 'HashMap'
                                           -- and 'Model'
    -> Bool                                -- ^ True if the functions are
                                           -- equivalent
eq_ f g = (M.toAscList . f) `eq` (toAscList . g)

------------------------------------------------------------------------
-- * Test harness

main :: IO ()
main = defaultMain tests

------------------------------------------------------------------------
-- * Helpers

sortByKey :: Ord k => [(k, v)] -> [(k, v)]
sortByKey = L.sortBy (compare `on` fst)

toAscList :: Ord k => HM.HashMap k v -> [(k, v)]
toAscList = L.sortBy (compare `on` fst) . HM.toList
