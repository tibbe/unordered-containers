{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Stats where

import qualified Data.HashMap.Internal.Array as A
import Data.HashMap.Internal (HashMap(..))
import qualified Data.HashMap.Internal as HM
import Data.Semigroup

data Histogram = H {
      empty         :: !Int
    , leaf          :: !Int
    , bitmapIndexed :: !Int
    , full          :: !Int
    , collision     :: !Int
    } deriving Show

instance Semigroup Histogram where
    h1 <> h2 = H {
          empty         = empty h1 + empty h2
        , leaf          = leaf h1 + leaf h2
        , bitmapIndexed = bitmapIndexed h1 + bitmapIndexed h2
        , full          = full h1 + full h2
        , collision     = collision h1 + collision h2
        }

instance Monoid Histogram where
    mempty = H 0 0 0 0 0
#if __GLASGOW_HASKELL__ < 803
    mappend = (<>)
#endif

-- | Count the number of node types at each level
nodeHistogram :: HM.Tree k v -> [Histogram]
nodeHistogram Empty = [mempty { empty = 1 }]
nodeHistogram (Leaf {}) = [mempty { leaf = 1 }]
nodeHistogram (BitmapIndexed _ ary) =
    mempty { bitmapIndexed = 1 } :
    A.foldl' (\ xs -> zipWith_ merge xs . nodeHistogram) [] ary
nodeHistogram (Full ary) =
    mempty { full = 1 } :
    A.foldl' (\ xs -> zipWith_ merge xs . nodeHistogram) [] ary
nodeHistogram (Collision {}) = [mempty { collision = 1 }]

merge (Just h1) (Just h2) = h1 `mappend` h2
merge (Just h) Nothing    = h `mappend` mempty
merge Nothing (Just h)    = mempty `mappend` h
merge Nothing Nothing     = error "impossible"

zipWith_ :: (Maybe a -> Maybe b -> c) -> [a] -> [b] -> [c]
zipWith_ f = go
  where
    go [] []         = []
    go [] (y:ys)     = let z = f Nothing (Just y) in z `seq` (z : go [] ys)
    go (x:xs) []     = let z = f (Just x) Nothing in z `seq` (z : go xs [])
    go (x:xs) (y:ys) = let z = f (Just x) (Just y) in z `seq` (z : go xs ys)
{-# INLINE zipWith_ #-}

ppHistogram :: [Histogram] -> String
ppHistogram = go 0
  where
    go _ []             = ""
    go lvl ((H {..}):hs) =
        indent ++ "empty: " ++ show empty ++ "\n" ++
        indent ++ "leaf: " ++ show leaf ++ "\n" ++
        indent ++ "bitmapIndexed: " ++ show bitmapIndexed ++ "\n" ++
        indent ++ "full: " ++ show full ++ "\n" ++
        indent ++ "collision: " ++ show collision ++ "\n" ++
        go (lvl+2) hs
      where indent = replicate lvl ' '
