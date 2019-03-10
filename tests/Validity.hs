{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main
    ( main
    ) where

import GHC.Generics (Generic)
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative (Applicative(pure), (<$>), (<*>))
import Data.Monoid (Monoid(mappend, mempty))
import Data.Traversable (Traversable(..))
import Data.Word (Word)
#endif
import Data.Bits (popCount)
import Data.Functor
import Data.Hashable (Hashable(hashWithSalt))
import Data.List (nub)
import Data.Validity
#if defined(STRICT)
import qualified Data.HashMap.Strict as HM
#else
import qualified Data.HashMap.Lazy as HM
#endif
import qualified Data.HashMap.Array as A
import Data.HashMap.Base (HashMap(..), Leaf(..), UnconsHM(..))
import qualified Data.HashMap.Base as HMB
import qualified Data.HashSet as HS
import Data.HashSet (HashSet)

import Data.GenValidity (GenUnchecked(..), GenValid(..), genSplit, genSplit4)
import Data.Validity (Validity)
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck
    ( Arbitrary
    , CoArbitrary
    , Gen
    , Property
    , oneof
    , resize
    , sized
    )
import Test.QuickCheck.Function
    ( (:->)
    , Fun(..)
    , Function(..)
    , apply
    , functionMap
    )
import Test.Validity.Functions
    ( producesValidsOnValids
    , producesValidsOnValids2
    , producesValidsOnValids3
    )
import Test.Validity.GenValidity.Property (genGeneratesValid)
#if !MIN_VERSION_QuickCheck(2,10,0)
-- | Extracts the value of a binary function.
--
-- 'Fn2' is the pattern equivalent of this function.
--
--  > prop_zipWith :: Fun (Int, Bool) Char -> [Int] -> [Bool] -> Bool
--  > prop_zipWith f xs ys = zipWith (applyFun2 f) xs ys == [ applyFun2 f x y | (x, y) <- zip xs ys]
--
applyFun2 :: Fun (a, b) c -> (a -> b -> c)
applyFun2 (Fun _ f) a b = f (a, b)

-- | Extracts the value of a ternary function. 'Fn3' is the
-- pattern equivalent of this function.
applyFun3 :: Fun (a, b, c) d -> (a -> b -> c -> d)
applyFun3 (Fun _ f) a b c = f (a, b, c)

-- | Provides a 'Function' instance for types with 'Integral'.
functionIntegral :: Integral a => (a -> b) -> (a :-> b)
functionIntegral = functionMap fromIntegral fromInteger

instance Function Word where
    function = functionIntegral
#else
import Test.QuickCheck.Function (applyFun2, applyFun3, functionIntegral)
#endif
instance (Validity k, Validity v) => Validity (Leaf k v) where
    validate (L k v) = mconcat [annotate k "key", annotate v "value"]

instance Validity a => Validity (A.Array a) where
    validate a = annotate (A.toList a) "The array elements"

instance (Eq k, Hashable k, Validity k, Validity v) =>
         Validity (UnconsHM k v) where
    validate UnconsEmptyHM = decorate "UnconsEmptyHM" mempty
    validate (UnconsedHM l hm) =
        decorate "UnconsedHM" $
        mconcat [decorate "Leaf" $ validate l, decorate "Map" $ validate hm]

instance (Eq k, Hashable k, Validity k, Validity v) =>
         Validity (HashMap k v) where
    validate hm =
        mconcat
            [ go HMB.defaultSalt 0 hm
            , check
                  (HM.fromList (HM.toList (hm $> ())) == (hm $> ()))
                  "fromList and toList are inverses for this hashmap."
            ]
      where
        go s bs hm_ =
            case hm_ of
                Empty -> mempty
                (Leaf h l@(L k _)) ->
                    decorate "Leaf" $
                    mconcat
                        [ annotate h "Hash"
                        , annotate l "Leaf"
                        , check
                              (HMB.hashWithSalt s k == h)
                              "The hash is correct."
                        ]
                (BitmapIndexed bm a) ->
                    decorate "BitmapIndexed" $
                    mconcat
                        [ annotate bm "Bitmap"
                        , decorate "Array" $
                          decorateList (zip [0 ..] $ A.toList a) $ \(ix, hm__) ->
                              mconcat
                                  [ go s (bs + HMB.bitsPerSubkey) hm__
                                  , check
                                        (not $ HM.null hm__)
                                        "The sub HashMap is not empty"
                                  , decorateList (HM.keys hm__) $ \k ->
                                        flip
                                            check
                                            "The hash, when masked with the current bitmask, of the key, produces the index in the array where the hashmap is found" $
                                        let h = HMB.hashWithSalt s k
                                         in HMB.sparseIndex bm (HMB.mask h bs) ==
                                            ix
                                  ]
                        , check
                              (A.length a == popCount bm)
                              "There are values in the array equal to popCount bm."
                        , check
                              (uniques $ concatMap HM.keys $ A.toList a)
                              "The keys are unique."
                        , check
                              (A.length a >= 1)
                              "The array has at least one element."
                        , check
                              (A.length a > 1 ||
                               not (HMB.isLeafOrCollision (A.index a 0))) $
                          "If the array has only one element, then that element is" ++
                          "not a leaf or collision."
                        ]
                (Full a) ->
                    decorate "Full" $
                    mconcat
                        [ decorate "Array" $
                          decorateList (zip [0 ..] $ A.toList a) $ \(ix, hm__) ->
                              mconcat
                                  [ go s (bs + HMB.bitsPerSubkey) hm__
                                  , check
                                        (not $ HM.null hm__)
                                        "The sub HashMap is not empty"
                                  , decorateList (HM.keys hm__) $ \k ->
                                        flip
                                            check
                                            "The hash, when masked with the current bitmask, of the key, produces the index in the array where the hashmap is found" $
                                        let h = HMB.hashWithSalt s k
                                         in HMB.index h bs == ix
                                  ]
                        , check
                              (A.length a == 2 ^ HMB.bitsPerSubkey)
                              "There are 2 ^ bitsPerSubkey values in the array."
                        , check
                              (uniques $ concatMap HM.keys $ A.toList a)
                              "The keys are unique."
                        ]
                (Collision h l1@(L k1 _) l2@(L k2 _) hm') ->
                    decorate "Collision" $
                    mconcat
                        [ annotate h "Hash"
                        , annotate l1 "The first collision"
                        , annotate l2 "The second collision"
                        , check
                              (HMB.hashWithSalt s k1 == h)
                              "The hash of the first collision is correct."
                        , check
                              (HMB.hashWithSalt s k2 == h)
                              "The hash of the second collision is correct."
                        , check
                              (k1 /= k2)
                              "The keys within the collision are not equal."
                        , check
                              (uniques (k1 : k2 : HM.keys hm'))
                              "The keys are unique."
                        , decorate "The recursive HashMap" $
                          go (HMB.nextSalt s) 0 hm'
                        , check
                              (all (\k -> HMB.hashWithSalt s k == h)
                                   (HM.keys hm'))
                              "All recursive keys hash to the hash within the collision, using the salt at this level."
                        ]

instance (Eq k, Hashable k, Validity k) => Validity (HashSet k) where
    validate hs = decorate "asMap" $ validate $ HS.toMap hs

uniques :: Eq a => [a] -> Bool
uniques l = length (nub l) == length l
#if !MIN_VERSION_validity(0,6,0)
-- | Decorate a validation with a location
decorate :: String -> Validation -> Validation
decorate = flip annotateValidation

annotateValidation :: Validation -> String -> Validation
annotateValidation val s =
    case val of
        Validation errs -> Validation $ map (Location s) errs
#endif

#if !MIN_VERSION_validity(0,8,0)
-- | Decorate a piecewise validation of a list with their location in the list
decorateList :: [a] -> (a -> Validation) -> Validation
decorateList as func =
    mconcat $
    flip map (zip [0 ..] as) $ \(i, a) ->
        decorate
            (unwords
                 ["The element at index", show (i :: Integer), "in the list"]) $
        func a
#endif
instance (GenUnchecked k, GenUnchecked v) => GenUnchecked (Leaf k v) where
    genUnchecked =
        sized $ \n -> do
            (a, b) <- genSplit n
            k <- resize a genUnchecked
            v <- resize b genUnchecked
            pure $ L k v
    shrinkUnchecked (L k v) = [L k' v' | (k', v') <- shrinkUnchecked (k, v)]

instance (GenValid k, GenValid v) => GenValid (Leaf k v) where
    genValid =
        sized $ \n -> do
            (a, b) <- genSplit n
            k <- resize a genValid
            v <- resize b genValid
            pure $ L k v

instance GenUnchecked a => GenUnchecked (A.Array a) where
    genUnchecked = do
        l <- genUnchecked
        pure $ A.fromList (length l) l
    shrinkUnchecked =
        fmap (\l -> A.fromList (length l) l) . shrinkUnchecked . A.toList

instance GenValid a => GenValid (A.Array a) where
    genValid = do
        l <- genValid
        pure $ A.fromList (length l) l

instance (GenUnchecked k, GenUnchecked v) => GenUnchecked (HashMap k v) where
    genUnchecked =
        sized $ \n ->
            case n of
                0 -> pure Empty
                _ ->
                    oneof
                        [ do (a, b) <- genSplit n
                             BitmapIndexed <$> resize a genUnchecked <*>
                                 resize b genUnchecked
                        , do (a, b) <- genSplit n
                             Leaf <$> resize a genUnchecked <*>
                                 resize b genUnchecked
                        , Full <$> genUnchecked
                        , do (a, b, c, d) <- genSplit4 n
                             Collision <$> resize a genUnchecked <*>
                                 resize b genUnchecked <*>
                                 resize c genUnchecked <*>
                                 resize d genUnchecked
                        ]
    shrinkUnchecked hm =
        case hm of
            Empty -> []
            Leaf h l -> [Leaf h' l' | (h', l') <- shrinkUnchecked (h, l)]
            BitmapIndexed bm a ->
                [BitmapIndexed bm' a' | (bm', a') <- shrinkUnchecked (bm, a)]
            Full a -> Full <$> shrinkUnchecked a
            Collision h l1 l2 hm_ ->
                [ Collision h' l1' l2' hm_'
                | (h', l1', l2', hm_') <- shrinkUnchecked (h, l1, l2, hm_)
                ]

-- It turns out it's almost impossible to write this instance without using internals.
-- This is good-enough for now.
instance (Eq k, Hashable k, GenValid k, GenValid v) =>
         GenValid (HashMap k v) where
    genValid = HM.fromList <$> genValid
    shrinkValid hm = HM.fromList <$> shrinkValid (HM.toList hm)
      -- TODO improve the shrinking, maybe.

-- Key type that generates more hash collisions.
newtype Key = K
    { unK :: Int
    } deriving ( Arbitrary
               , CoArbitrary
               , Validity
               , GenUnchecked
               , GenValid
               , Eq
               , Ord
               , Read
               , Show
               , Integral
               , Real
               , Num
               , Enum
               , Generic
               )

instance Hashable Key where
    hashWithSalt salt k = hashWithSalt salt (unK k) `mod` 20

instance Function Key where
    function = functionIntegral

pSingleton :: Property
pSingleton =
    producesValidsOnValids2 (HM.singleton :: Key -> Int -> HM.HashMap Key Int)

pNull :: Property
pNull = producesValidsOnValids (HM.null :: HM.HashMap Key Int -> Bool)

pSize :: Property
pSize = producesValidsOnValids (HM.size :: HM.HashMap Key Int -> Int)

-- These four tests will ensure that `equal1`, etc do not segfault and succesfully
-- evaluate to a `Bool` (or `Ordering`, respectively)
pEqual1 :: Fun (Int, Int) Bool -> Property
pEqual1 f =
    producesValidsOnValids2
        (HMB.equal1 (applyFun2 f) :: HM.HashMap Key Int -> HM.HashMap Key Int -> Bool)

pEqual2 :: Fun (Key, Key) Bool -> Fun (Int, Int) Bool -> Property
pEqual2 f g =
    producesValidsOnValids2
        (HMB.equal2 (applyFun2 f) (applyFun2 g) :: HM.HashMap Key Int -> HM.HashMap Key Int -> Bool)

pCmp1 :: Fun (Int, Int) Ordering -> Property
pCmp1 f =
    producesValidsOnValids2
        (HMB.cmp1 (applyFun2 f) :: HM.HashMap Key Int -> HM.HashMap Key Int -> Ordering)

pCmp2 :: Fun (Key, Key) Ordering -> Fun (Int, Int) Ordering -> Property
pCmp2 f g =
    producesValidsOnValids2
        (HMB.cmp2 (applyFun2 f) (applyFun2 g) :: HM.HashMap Key Int -> HM.HashMap Key Int -> Ordering)

pMember :: Property
pMember =
    producesValidsOnValids2 (HM.member :: Key -> HM.HashMap Key Int -> Bool)

pLookup :: Property
pLookup =
    producesValidsOnValids2
        (HM.lookup :: Key -> HM.HashMap Key Int -> Maybe Int)

pLookupDefault :: Property
pLookupDefault =
    producesValidsOnValids3
        (HM.lookupDefault :: Int -> Key -> HM.HashMap Key Int -> Int)

pInsert :: Property
pInsert =
    producesValidsOnValids3
        (HM.insert :: Key -> Int -> HM.HashMap Key Int -> HM.HashMap Key Int)

pInsertWith :: Property
pInsertWith =
    producesValidsOnValids3
        (HM.insertWith (+) :: Key -> Int -> HM.HashMap Key Int -> HM.HashMap Key Int)

pDelete :: Property
pDelete =
    producesValidsOnValids2
        (HM.delete :: Key -> HM.HashMap Key Int -> HM.HashMap Key Int)

pAdjust :: Fun Int Int -> Property
pAdjust f =
    producesValidsOnValids2
        (HM.adjust (apply f) :: Key -> HM.HashMap Key Int -> HM.HashMap Key Int)

pUpdate :: (Fun Int (Maybe Int)) -> Property
pUpdate f =
    producesValidsOnValids2
        (HM.update (apply f) :: Key -> HM.HashMap Key Int -> HM.HashMap Key Int)

pAlter :: Property
pAlter =
    producesValidsOnValids2
        (HM.alter (fmap succ) :: Key -> HM.HashMap Key Int -> HM.HashMap Key Int)

pAlterF :: Fun (Maybe Int) [Maybe Int] -> Property
pAlterF f =
    producesValidsOnValids2
        (HM.alterF (apply f) :: Key -> HM.HashMap Key Int -> [HM.HashMap Key Int])

pUnion :: Property
pUnion =
    producesValidsOnValids2
        (HM.union :: HashMap Key Int -> HashMap Key Int -> HashMap Key Int)

pUnionWith :: Fun (Int, Int) Int -> Property
pUnionWith f =
    producesValidsOnValids2
        (HM.unionWith (applyFun2 f) :: HashMap Key Int -> HashMap Key Int -> HashMap Key Int)

pUnionWithKey :: Fun (Key, Int, Int) Int -> Property
pUnionWithKey f =
    producesValidsOnValids2
        (HM.unionWithKey (applyFun3 f) :: HashMap Key Int -> HashMap Key Int -> HashMap Key Int)

pUnions :: Property
pUnions =
    producesValidsOnValids (HM.unions :: [HashMap Key Int] -> HashMap Key Int)

pMap :: Fun Int Int -> Property
pMap f =
    producesValidsOnValids
        (HM.map (apply f) :: HashMap Key Int -> HashMap Key Int)

pMapWithKey :: Fun (Key, Int) Int -> Property
pMapWithKey f =
    producesValidsOnValids
        (HM.mapWithKey (applyFun2 f) :: HashMap Key Int -> HashMap Key Int)

pTraverseWithKey :: Fun (Key, Int) (Maybe Int) -> Property
pTraverseWithKey f =
    producesValidsOnValids
        (HM.traverseWithKey (applyFun2 f) :: HashMap Key Int -> Maybe (HashMap Key Int))

pDifference :: Property
pDifference =
    producesValidsOnValids2
        (HM.difference :: HashMap Key Int -> HashMap Key Int -> HashMap Key Int)

pDifferenceWith :: Fun (Int, Int) (Maybe Int) -> Property
pDifferenceWith f =
    producesValidsOnValids2
        (HM.differenceWith (applyFun2 f) :: HashMap Key Int -> HashMap Key Int -> HashMap Key Int)

pIntersection :: Property
pIntersection =
    producesValidsOnValids2
        (HM.intersection :: HashMap Key Int -> HashMap Key Int -> HashMap Key Int)

pIntersectionWith :: Fun (Int, Int) Int -> Property
pIntersectionWith f =
    producesValidsOnValids2
        (HM.intersectionWith (applyFun2 f) :: HashMap Key Int -> HashMap Key Int -> HashMap Key Int)

pIntersectionWithKey :: Fun (Key, Int, Int) Int -> Property
pIntersectionWithKey f =
    producesValidsOnValids2
        (HM.intersectionWithKey (applyFun3 f) :: HashMap Key Int -> HashMap Key Int -> HashMap Key Int)

pFoldl' :: Fun (Word, Int) Word -> Property
pFoldl' f =
    producesValidsOnValids2
        (HM.foldl' (applyFun2 f) :: Word -> HashMap Key Int -> Word)

pFoldlWithKey' :: Fun (Word, Key, Int) Word -> Property
pFoldlWithKey' f =
    producesValidsOnValids2
        (HM.foldlWithKey' (applyFun3 f) :: Word -> HashMap Key Int -> Word)

pFoldr :: Fun (Int, Word) Word -> Property
pFoldr f =
    producesValidsOnValids2
        (HM.foldr (applyFun2 f) :: Word -> HashMap Key Int -> Word)

pFoldrWithKey :: Fun (Key, Int, Word) Word -> Property
pFoldrWithKey f =
    producesValidsOnValids2
        (HM.foldrWithKey (applyFun3 f) :: Word -> HashMap Key Int -> Word)

pFilter :: Fun Int Bool -> Property
pFilter f =
    producesValidsOnValids
        (HM.filter (apply f) :: HashMap Key Int -> HashMap Key Int)

pFilterWithKey :: Fun (Key, Int) Bool -> Property
pFilterWithKey f =
    producesValidsOnValids
        (HM.filterWithKey (applyFun2 f) :: HashMap Key Int -> HashMap Key Int)

pMapMaybe :: Fun Int (Maybe Int) -> Property
pMapMaybe f =
    producesValidsOnValids
        (HM.mapMaybe (apply f) :: HashMap Key Int -> HashMap Key Int)

pMapMaybeWithKey :: Fun (Key, Int) (Maybe Int) -> Property
pMapMaybeWithKey f =
    producesValidsOnValids
        (HM.mapMaybeWithKey (applyFun2 f) :: HashMap Key Int -> HashMap Key Int)

pKeys :: Property
pKeys = producesValidsOnValids (HM.keys :: HashMap Key Int -> [Key])

pElems :: Property
pElems = producesValidsOnValids (HM.elems :: HashMap Key Int -> [Int])

pToList :: Property
pToList = producesValidsOnValids (HM.toList :: HashMap Key Int -> [(Key, Int)])

pFromList :: Property
pFromList =
    producesValidsOnValids (HM.fromList :: [(Key, Int)] -> HashMap Key Int)

pFromListWith :: Fun (Int, Int) Int -> Property
pFromListWith f =
    producesValidsOnValids
        (HM.fromListWith (applyFun2 f) :: [(Key, Int)] -> HashMap Key Int)

pKeysSet :: Property
pKeysSet = producesValidsOnValids (HM.keysSet :: HashMap Key Int -> HashSet Key)

pUnconsHM :: Property
pUnconsHM =
    producesValidsOnValids (HMB.unconsHM :: HashMap Key Int -> UnconsHM Key Int)

-- There isn't currently a pUnconsA because I (David Feuer) don't know
-- the right way to tell genvalidity-hspec that we only want cases
-- where the array is non-empty and all of its elements are non-empty.
------------------------------------------------------------------------
-- * Test list
tests :: [Test]
tests =
    let genValidHelper gen = genGeneratesValid gen (const [])
    -- Basic interface
     in [ testGroup
              "HashMap"
              [ testProperty "genValid generates valid values for Leaf" $
                genValidHelper (genValid :: Gen (Leaf Key Int))
              , testProperty "genValid generates valid values for Array" $
                genValidHelper (genValid :: Gen (A.Array Key))
              , testProperty "genValid generates valid values for HashMap" $
                genValidHelper (genValid :: Gen (HashMap Key Int))
              ]
        , testGroup
              "HashMap"
              [ testProperty "singleton produces valid HashMaps" pSingleton
              , testProperty "null produces valid Bools" pNull
              , testProperty "size produces valid HashMaps" pSize
              , testProperty "equal1 produce valid Bools" pEqual1
              , testProperty "equal2 produce valid Bools" pEqual2
              , testProperty "cmp1 produce valid Orderings" pCmp1
              , testProperty "cmp2 produce valid Orderings" pCmp2
              , testProperty "member produces valid HashMaps" pMember
              , testProperty "lookup produces valid HashMaps" pLookup
              , testProperty
                    "lookupDefault produces valid HashMaps"
                    pLookupDefault
              , testProperty "insert produces valid HashMaps" pInsert
              , testProperty "insertWith produces valid HashMaps" pInsertWith
              , testProperty "delete produces valid HashMaps" pDelete
              , testProperty "adjust produces valid HashMaps" pAdjust
              , testProperty "update produces valid HashMaps" pUpdate
              , testProperty "alter produces valid HashMaps" pAlter
              , testProperty "alterF produces valid HashMaps" pAlterF
              , testProperty "union produces valid HashMaps" pUnion
              , testProperty "unionWith produces valid HashMaps" pUnionWith
              , testProperty
                    "unionWithKey produces valid HashMaps"
                    pUnionWithKey
              , testProperty "unions produces valid HashMaps" pUnions
              , testProperty "map produces valid HashMaps" pMap
              , testProperty "mapWithKey produces valid HashMaps" pMapWithKey
              , testProperty
                    "traverseWithKey produces valid HashMaps"
                    pTraverseWithKey
              , testProperty "difference produces valid HashMaps" pDifference
              , testProperty
                    "differenceWith produces valid HashMaps"
                    pDifferenceWith
              , testProperty
                    "intersection produces valid HashMaps"
                    pIntersection
              , testProperty
                    "intersectionWith produces valid HashMaps"
                    pIntersectionWith
              , testProperty
                    "intersectionWithKey produces valid HashMaps"
                    pIntersectionWithKey
              , testProperty "foldl' produces valid HashMaps" pFoldl'
              , testProperty
                    "foldlWithKey' produces valid HashMaps"
                    pFoldlWithKey'
              , testProperty "foldr produces valid HashMaps" pFoldr
              , testProperty
                    "foldrWithKey produces valid HashMaps"
                    pFoldrWithKey
              , testProperty "filter produces valid HashMaps" pFilter
              , testProperty
                    "filterWithKey produces valid HashMaps"
                    pFilterWithKey
              , testProperty "mapMaybe produces valid HashMaps" pMapMaybe
              , testProperty
                    "mapMaybeWithKey produces valid HashMaps"
                    pMapMaybeWithKey
              , testProperty "keys produces valid lists" pKeys
              , testProperty "elems produces valid lists" pElems
              , testProperty "toList produces valid lists" pToList
              , testProperty "fromList produces valid HashMaps" pFromList
              , testProperty
                    "fromListWith produces valid HashMaps"
                    pFromListWith
              , testProperty "unconsHM produces valid HashMaps" pUnconsHM
              , testProperty "keysSet produces valid HashSets" pKeysSet
              ]
        ]

main :: IO ()
main = defaultMain tests
