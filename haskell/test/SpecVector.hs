module SpecVector where

import qualified Data.Vector.Unboxed as VU
import QuickSort
import System.Random.MWC
import Test.Tasty.Hspec

genRandomVector :: Int -> IO (VU.Vector Int)
genRandomVector size =
  withSystemRandom . asGenST $ \gen -> uniformVector gen size

sorted :: (VU.Unbox a, Ord a) => VU.Vector a -> Bool
sorted vec = snd $ VU.foldr'
  (\(v) (a, r) -> if r && v <= a then (v, True) else (a, False))
  (VU.last vec, True)
  vec

spec_vector :: Spec
spec_vector = do
  it "QuickSort (10, random)" $ do
    let vec = VU.fromList [6, 3, 4, 9, 1, 7, 8, 2, 5, 0 :: Int]
    mvec <- VU.thaw vec
    quicksortUM_ mvec
    vec' <- VU.freeze mvec

    vec' `shouldBe` VU.fromList [0 .. 9]
  it "QuickSort (10, ordered)" $ do
    let vec = VU.fromList [0 :: Int .. 9]
    quicksort vec `shouldBe` VU.fromList [0 .. 9]
  it "QuickSort (10000)" $ do
    vec  <- genRandomVector 10000
    mvec <- VU.thaw vec
    quicksortUM_ mvec
    vec' <- VU.freeze mvec

    sorted vec' `shouldBe` True
