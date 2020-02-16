module QuickSort where

import Control.Monad
import Control.Monad.Fix
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
      (low', high') <- partition low high

      go low         (low' - 1)
      go (high' + 1) high

  partition :: Int -> Int -> IO (Int, Int)
  partition !low !high = do
    let n = high - low
    !pivot <- do
      !x <- VUM.read vec low
      !y <- VUM.read vec ((low + high) `div` 2)
      !z <- VUM.read vec high
      return $ medianOf x y z

    fix
      ( \(!f) (!low, !high) -> if low > high
        then return (low, high)
        else do
          low' <- fix
            ( \(!g) (!j) ->
              ( \inc -> if inc
                  then (if j < high then g else return) (j + 1)
                  else return j
                )
                =<< (< pivot)
                <$> VUM.read vec j
            )
            low
          high' <- fix
            ( \(!g) (!j) ->
              ( \inc -> if inc
                  then (if j > low then g else return) (j - 1)
                  else return j
                )
                =<< (pivot <)
                <$> VUM.read vec j
            )
            high

          if low' >= high'
            then return (low', high')
            else VUM.swap vec low' high' >> f (low' + 1, high' - 1)
      )
      (low, high)

  dropWhileM f []     = return []
  dropWhileM f (x:xs) = f x >>= \b -> if b then dropWhileM f xs else return xs

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
