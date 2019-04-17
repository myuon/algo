import Control.Monad.Fix
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import System.IO.Unsafe

uread :: VUM.Unbox a => Int -> VUM.IOVector a -> a
uread i v = unsafePerformIO $ VUM.read v i

uwrite :: VUM.Unbox a => Int -> a -> VUM.IOVector a -> VUM.IOVector a
uwrite i a v = unsafePerformIO $ VUM.write v i a >> return v

uswap :: VUM.Unbox a => Int -> Int -> VUM.IOVector a -> VUM.IOVector a
uswap i j v = unsafePerformIO $ VUM.swap v i j >> return v

ufreeze :: VUM.Unbox a => VUM.IOVector a -> VU.Vector a
ufreeze v = unsafePerformIO $ VU.freeze v

data PQueue a = PQueue Int (VUM.IOVector a)

new :: VUM.Unbox a => Int -> PQueue a
new s = PQueue 0 $ unsafePerformIO $ VUM.new s

push :: Ord a => VUM.Unbox a => a -> PQueue a -> PQueue a
push a (PQueue k vec) = PQueue (k + 1) vec'
 where
  vec' = up k a $ uwrite k a vec

  up i cv vec = (\(_, v) -> v) $ fix
    ( \f (ci, vec) ->
      let pi = (ci - 1) `div` 2
          pv = uread pi vec
      in  if 0 < ci && pv < cv
            then let vec' = uswap pi ci vec in vec' `seq` f (pi, vec')
            else (ci, vec)
    )
    (i, vec)

popMax :: (Ord a, Bounded a, VUM.Unbox a) => PQueue a -> (a, PQueue a)
popMax (PQueue k vec) | k < 0     = error "size < 0"
                      | otherwise = (uread 0 vec, PQueue (k - 1) vec')
 where
  vec' = let v = uswap (k - 1) 0 vec in v `seq` down 0 (uread 0 vec) v

  down i cv vec = (\(_, v) -> v) $ fix
    ( \f (ci, vec) ->
      let li = ci * 2 + 1
          lv = if li < k - 1 then uread li vec else minBound
          ri = ci * 2 + 2
          rv = if ri < k - 1 then uread ri vec else minBound
      in  if cv >= lv && cv >= rv
            then (ci, vec)
            else
              let p    = if lv < rv then ri else li
                  vec' = uswap p ci vec
              in  vec' `seq` f (p, vec')
    )
    (i, vec)
