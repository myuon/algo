module QuickSort where

import Control.Monad
import Data.Foldable
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import Data.ByteString.Internal (accursedUnutterablePerformIO)
import Debug.Trace

quicksortUM_ :: (VUM.Unbox a, Ord a, Show a) => VUM.IOVector a -> IO ()
quicksortUM_ !vec = go 0 (VUM.length vec - 1)
 where
  go :: Int -> Int -> IO ()
  go !low !high
    | low >= high = return ()
    | otherwise = do
      pi <- partition low high

      go low      (pi - 1)
      go (pi + 1) high

  partition :: Int -> Int -> IO Int
  partition !low !high = do
    let n = high - low
    !pivot <- VUM.read vec high

    i      <- foldlM
      ( \(!i) (!j) -> do
        !aj <- VUM.read vec j
        if aj <= pivot
          then VUM.swap vec (i + 1) j >> return (i + 1)
          else return i
      )
      (low - 1)
      [low .. high - 1]

    VUM.swap vec (i + 1) high

    return $ i + 1

  medianOf !x !y !z | z < y     = medianOf x z y
                    | y < x     = medianOf y x z
                    | otherwise = y


quicksortUM :: (VU.Unbox a, Ord a, Show a) => VU.Vector a -> IO (VU.Vector a)
quicksortUM !vec = VU.thaw vec >>= quicksortUM_ >> return vec

quicksort :: (VU.Unbox a, Ord a, Show a) => VU.Vector a -> VU.Vector a
quicksort !vec = accursedUnutterablePerformIO $ quicksortUM vec

unsafeQuicksort :: (VU.Unbox a, Ord a, Show a) => VU.Vector a -> VU.Vector a
unsafeQuicksort !vec =
  accursedUnutterablePerformIO $ VU.thaw vec >>= quicksortUM_ >> return vec
