{-# LANGUAGE BangPatterns #-}
import Control.Monad
import Control.Monad.Fix
import Data.Foldable (foldl')
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import Data.ByteString.Internal (accursedUnutterablePerformIO)

uread :: VUM.Unbox a => Int -> VUM.IOVector a -> a
uread !i !v = accursedUnutterablePerformIO $ VUM.unsafeRead v i

uwrite :: VUM.Unbox a => Int -> a -> VUM.IOVector a -> VUM.IOVector a
uwrite !i !a !v =
  accursedUnutterablePerformIO $ VUM.unsafeWrite v i a >> return v

uswap :: VUM.Unbox a => Int -> Int -> VUM.IOVector a -> VUM.IOVector a
uswap !i !j !v =
  accursedUnutterablePerformIO $ VUM.unsafeSwap v i j >> return v

ufreeze :: VUM.Unbox a => VUM.IOVector a -> VU.Vector a
ufreeze !v = accursedUnutterablePerformIO $ VU.unsafeFreeze v

uthaw :: VUM.Unbox a => VU.Vector a -> VUM.IOVector a
uthaw !v = accursedUnutterablePerformIO $ VU.unsafeThaw v

data Pair a b = Pair !a !b
data UnionFind = UnionFind (Pair (VUM.IOVector Int) (VUM.IOVector Int))

new :: Int -> UnionFind
new !n = UnionFind $ Pair (uthaw $ VU.fromList [0 .. n - 1])
                          (accursedUnutterablePerformIO $ VUM.replicate n 1)

findUF :: UnionFind -> Int -> Int
findUF !(UnionFind (Pair elems _)) !k = fix
  ( \f (!elems, !k, !path) -> case uread k elems of
    n | n == k -> foldl' (\(!acc) !p -> uwrite p n acc) elems path `seq` n
    n          -> f (elems, n, n : path)
  )
  (elems, k, [k])

sizeUF :: UnionFind -> Int -> Int
sizeUF !uf@(UnionFind (Pair _ sizes)) !i =
  let j = findUF uf i in j `seq` uread j sizes

unionUF :: UnionFind -> Int -> Int -> UnionFind
unionUF !uf@(UnionFind (Pair elem sizes)) !i !j =
  let pi = findUF uf i
      pj = findUF uf j
      si = uread pi sizes
      sj = uread pj sizes
  in  if pi == pj
        then uf
        else
          let (t1, t2) = if si < sj then (pi, pj) else (pj, pi)
          in  UnionFind $ Pair (uwrite t1 t2 elem) (uwrite t2 (si + sj) sizes)
