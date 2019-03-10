{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}

-- | Tests for the 'Data.HashMap.Lazy' module.  We test functions by
-- comparing them to a simpler model, an association list.

module Main where

import Control.Monad ( guard )
import qualified Data.Foldable as Foldable
import Data.Function (on)
import Data.Hashable (Hashable(hashWithSalt))
import qualified Data.List as L
import Data.Ord (comparing)
#if defined(STRICT)
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as M
#else
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map.Lazy as M
#endif
import Test.QuickCheck (Arbitrary, Property, (==>), (===))
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)
#if MIN_VERSION_base(4,8,0)
import Data.Functor.Identity (Identity (..))
#endif
import Control.Applicative (Const (..))
import Test.QuickCheck.Function (Fun, apply)
import Test.QuickCheck.Poly (A, B)
#if MIN_VERSION_base(4,9,0)
import Data.Functor.Classes (eq2, compare2)
#endif

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

#if MIN_VERSION_base(4,9,0)
-- Caution: this is a rather weak test. Fortunately, the "Permutation"
-- properties in the HashSet test suite should catch most of what this
-- doesn't.
pEq2 :: [(Key, Int)] -> [(Key, Int)] -> Property
pEq2 xs ys = (x == y) === (x `eq2` y)
  where
    x = HM.fromList xs
    y = HM.fromList ys
#endif

pNeq :: [(Key, Int)] -> [(Key, Int)] -> Bool
pNeq xs = (M.fromList xs /=) `eq` (HM.fromList xs /=)

-- We cannot compare to `Data.Map` as ordering is different.
pOrd1 :: [(Key, Int)] -> Bool
pOrd1 xs = compare x x == EQ
  where
    x = HM.fromList xs

pOrd2 :: [(Key, Int)] -> [(Key, Int)] -> [(Key, Int)] -> Bool
pOrd2 xs ys zs = case (compare x y, compare y z) of
    (EQ, o)  -> compare x z == o
    (o,  EQ) -> compare x z == o
    (LT, LT) -> compare x z == LT
    (GT, GT) -> compare x z == GT
    (LT, GT) -> True -- ys greater than xs and zs.
    (GT, LT) -> True
  where
    x = HM.fromList xs
    y = HM.fromList ys
    z = HM.fromList zs

pOrd3 :: [(Key, Int)] -> [(Key, Int)] -> Bool
pOrd3 xs ys = case (compare x y, compare y x) of
    (EQ, EQ) -> True
    (LT, GT) -> True
    (GT, LT) -> True
    _        -> False
  where
    x = HM.fromList xs
    y = HM.fromList ys

#if MIN_VERSION_base(4,9,0)
pOrd4 :: [(Key, Int)] -> [(Key, Int)] -> Property
pOrd4 xs ys = compare2 x y === compare x y
  where
    x = HM.fromList xs
    y = HM.fromList ys
#endif

pOrdEq :: [(Key, Int)] -> [(Key, Int)] -> Bool
pOrdEq xs ys = case (compare x y, x == y) of
    (EQ, True)  -> True
    (LT, False) -> True
    (GT, False) -> True
    _           -> False
  where
    x = HM.fromList xs
    y = HM.fromList ys

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
    xs' = L.nubBy (\(k,_) (k',_) -> k == k') xs
    ys = shuffle is xs'
    x = HM.fromList xs'
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
    
pDeleteAlwaysCollision :: AlwaysCollide -> AlwaysCollide -> AlwaysCollide -> Int -> Property
pDeleteAlwaysCollision k1 k2 k3 idx = (k1 /= k2) && (k2 /= k3) && (k1 /= k3) ==>
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



newtype MostlyCollide = MC Int
    deriving (Arbitrary, Eq, Ord, Show)

instance Hashable MostlyCollide where
    hashWithSalt s (MC i) = (hashWithSalt s i) `mod` 3

-- White-box test that tests the case of deleting one of two keys from
-- a map, where the keys' hash values collide.
pDeleteMostlyCollision :: MostlyCollide -> MostlyCollide -> MostlyCollide -> Int
                 -> Property
pDeleteMostlyCollision k1 k2 k3 idx =
  (k1 /= k2) && (k2 /= k3) && (k1 /= k3) &&
  (hashWithSalt defaultSalt k1 == hashWithSalt defaultSalt k2) &&
  (hashWithSalt defaultSalt k2 == hashWithSalt defaultSalt k3) &&
  (hashWithSalt defaultSalt k1 == hashWithSalt defaultSalt k3) ==>
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
    defaultSalt = -2578643520546668380 -- TODO what do do with this test?

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


-- We choose the list functor here because we don't fuss with
-- it in alterF rules and because it has a sufficiently interesting
-- structure to have a good chance of breaking if something is wrong.
pAlterF :: Key -> Fun (Maybe A) [Maybe A] -> [(Key, A)] -> Property
pAlterF k f xs =
  fmap M.toAscList (M.alterF (apply f) k (M.fromList xs))
  ===
  fmap toAscList (HM.alterF (apply f) k (HM.fromList xs))

#if !MIN_VERSION_base(4,8,0)
newtype Identity a = Identity {runIdentity :: a}
instance Functor Identity where
  fmap f (Identity x) = Identity (f x)
#endif

pAlterFAdjust :: Key -> [(Key, Int)] -> Bool
pAlterFAdjust k =
  runIdentity . M.alterF (Identity . fmap succ) k `eq_`
  runIdentity . HM.alterF (Identity . fmap succ) k

pAlterFInsert :: Key -> [(Key, Int)] -> Bool
pAlterFInsert k =
  runIdentity . M.alterF (const . Identity . Just $ 3) k `eq_`
  runIdentity . HM.alterF (const . Identity . Just $ 3) k

pAlterFInsertWith :: Key -> Fun Int Int -> [(Key, Int)] -> Bool
pAlterFInsertWith k f =
  runIdentity . M.alterF (Identity . Just . maybe 3 (apply f)) k `eq_`
  runIdentity . HM.alterF (Identity . Just . maybe 3 (apply f)) k

pAlterFDelete :: Key -> [(Key, Int)] -> Bool
pAlterFDelete k =
  runIdentity . M.alterF (const (Identity Nothing)) k `eq_`
  runIdentity . HM.alterF (const (Identity Nothing)) k

pAlterFLookup :: Key
              -> Fun (Maybe A) B
              -> [(Key, A)] -> Bool
pAlterFLookup k f =
  getConst . M.alterF (Const . apply f :: Maybe A -> Const B (Maybe A)) k
  `eq`
  getConst . HM.alterF (Const . apply f) k

------------------------------------------------------------------------
-- ** Combine

pUnion :: [(Key, Int)] -> [(Key, Int)] -> Bool
pUnion xs ys = M.union (M.fromList xs) `eq_` HM.union (HM.fromList xs) $ ys

pUnionWith :: [(Key, Int)] -> [(Key, Int)] -> Bool
pUnionWith xs ys = M.unionWith (-) (M.fromList xs) `eq_`
                   HM.unionWith (-) (HM.fromList xs) $ ys

pUnionWithKey :: [(Key, Int)] -> [(Key, Int)] -> Bool
pUnionWithKey xs ys = M.unionWithKey go (M.fromList xs) `eq_`
                             HM.unionWithKey go (HM.fromList xs) $ ys
  where
    go :: Key -> Int -> Int -> Int
    go (K k) i1 i2 = k - i1 + i2

pUnions :: [[(Key, Int)]] -> Bool
pUnions xss = M.toAscList (M.unions (map M.fromList xss)) ==
              toAscList (HM.unions (map HM.fromList xss))

------------------------------------------------------------------------
-- ** Transformations

pMap :: [(Key, Int)] -> Bool
pMap = M.map (+ 1) `eq_` HM.map (+ 1)

pTraverse :: [(Key, Int)] -> Bool
pTraverse xs =
  L.sort (fmap (L.sort . M.toList) (M.traverseWithKey (\_ v -> [v + 1, v + 2]) (M.fromList (take 10 xs))))
     == L.sort (fmap (L.sort . HM.toList) (HM.traverseWithKey (\_ v -> [v + 1, v + 2]) (HM.fromList (take 10 xs))))

------------------------------------------------------------------------
-- ** Difference and intersection

pDifference :: [(Key, Int)] -> [(Key, Int)] -> Bool
pDifference xs ys = M.difference (M.fromList xs) `eq_`
                    HM.difference (HM.fromList xs) $ ys

pDifferenceWith :: [(Key, Int)] -> [(Key, Int)] -> Bool
pDifferenceWith xs ys = M.differenceWith f (M.fromList xs) `eq_`
                        HM.differenceWith f (HM.fromList xs) $ ys
  where
    f x y = if x == 0 then Nothing else Just (x - y)

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
pFoldr = (L.sort . M.foldr (:) []) `eq` (L.sort . HM.foldr (:) [])

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
#if MIN_VERSION_base(4,9,0)
      , testProperty "eq2 = (==)" pEq2
#endif
      , testProperty "compare reflexive" pOrd1
      , testProperty "compare transitive" pOrd2
      , testProperty "compare antisymmetric" pOrd3
#if MIN_VERSION_base(4,9,0)
      , testProperty "compare2 = compare" pOrd4
#endif
      , testProperty "Ord => Eq" pOrdEq
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
      , testProperty "deleteAlwaysCollision" pDeleteAlwaysCollision
      , testProperty "deleteMostlyCollision" pDeleteMostlyCollision
      , testProperty "insertWith" pInsertWith
      , testProperty "adjust" pAdjust
      , testProperty "updateAdjust" pUpdateAdjust
      , testProperty "updateDelete" pUpdateDelete
      , testProperty "alterAdjust" pAlterAdjust
      , testProperty "alterInsert" pAlterInsert
      , testProperty "alterDelete" pAlterDelete
      , testProperty "alterF" pAlterF
      , testProperty "alterFAdjust" pAlterFAdjust
      , testProperty "alterFInsert" pAlterFInsert
      , testProperty "alterFInsertWith" pAlterFInsertWith
      , testProperty "alterFDelete" pAlterFDelete
      , testProperty "alterFLookup" pAlterFLookup
      ]
    -- Combine
    , testProperty "union" pUnion
    , testProperty "unionWith" pUnionWith
    , testProperty "unionWithKey" pUnionWithKey
    , testProperty "unions" pUnions
    -- Transformations
    , testProperty "map" pMap
    , testProperty "traverse" pTraverse
    -- Folds
    , testGroup "folds"
      [ testProperty "foldr" pFoldr
      , testProperty "foldrWithKey" pFoldrWithKey
      , testProperty "foldl'" pFoldl'
      ]
    , testGroup "difference and intersection"
      [ testProperty "difference" pDifference
      , testProperty "differenceWith" pDifferenceWith
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

infix 4 `eq`

eq_ :: (Eq k, Eq v, Hashable k, Ord k)
    => (Model k v -> Model k v)            -- ^ Function that modifies a 'Model'
    -> (HM.HashMap k v -> HM.HashMap k v)  -- ^ Function that modified a
                                           -- 'HashMap' in the same way
    -> [(k, v)]                            -- ^ Initial content of the 'HashMap'
                                           -- and 'Model'
    -> Bool                                -- ^ True if the functions are
                                           -- equivalent
eq_ f g = (M.toAscList . f) `eq` (toAscList . g)

infix 4 `eq_`

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
