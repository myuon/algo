import Control.Monad.Fix
import Data.Foldable (foldl')
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import Data.ByteString.Internal (accursedUnutterablePerformIO)

uread :: VUM.Unbox a => Int -> VUM.IOVector a -> a
uread i v = accursedUnutterablePerformIO $ VUM.unsafeRead v i

uwrite :: VUM.Unbox a => Int -> a -> VUM.IOVector a -> VUM.IOVector a
uwrite i a v = accursedUnutterablePerformIO $ VUM.unsafeWrite v i a >> return v

uswap :: VUM.Unbox a => Int -> Int -> VUM.IOVector a -> VUM.IOVector a
uswap i j v = accursedUnutterablePerformIO $ VUM.unsafeSwap v i j >> return v

ufreeze :: VUM.Unbox a => VUM.IOVector a -> VU.Vector a
ufreeze v = accursedUnutterablePerformIO $ VU.unsafeFreeze v

uthaw :: VUM.Unbox a => VU.Vector a -> VUM.IOVector a
uthaw v = accursedUnutterablePerformIO $ VU.unsafeThaw v

newtype UnionFind = UnionFind (VUM.IOVector Int, VUM.IOVector Int)

findUF :: UnionFind -> Int -> Int
findUF (UnionFind (elems, _)) k = fix
  ( \f (elems, k, path) -> case uread k elems of
    n | n == k -> {- foldl' (\acc p -> uwrite p n acc) elems path `seq` -}n
    n -> f (elems, n, n : path)
  )
  (elems, k, [k])

sizeUF :: UnionFind -> Int -> Int
sizeUF (UnionFind (_, sizes)) i = uread i sizes

uwriteElem :: Int -> Int -> UnionFind -> UnionFind
uwriteElem i a (UnionFind (elem, sizes)) = UnionFind (uwrite i a elem, sizes)

uwriteSize :: Int -> Int -> UnionFind -> UnionFind
uwriteSize i a (UnionFind (elem, sizes)) = UnionFind (elem, uwrite i a sizes)

unionUF :: UnionFind -> Int -> Int -> (UnionFind, Int)
unionUF uf@(UnionFind (elem, sizes)) i j =
  let pi  = findUF uf i
      pj  = findUF uf j
      si  = uread pi sizes
      sj  = uread pj sizes
      sij = si + sj
  in  if pi == pj
      then
        (uf, 0)
      else
        let (t1, t2) = if si < sj then (pi, pj) else (pj, pi)
        in  ( UnionFind (uwrite t1 t2 elem, uwrite t1 0 $ uwrite t2 sij sizes)
            , si * sj
            )
