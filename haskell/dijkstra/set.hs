import Control.Monad.Fix
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VM
import qualified Data.Set as S
import System.IO.Unsafe

uread :: VU.Unbox a => Int -> VM.IOVector a -> a
uread i v = unsafeDupablePerformIO $ VM.unsafeRead v i

uwrite :: VU.Unbox a => Int -> a -> VM.IOVector a -> VM.IOVector a
uwrite i a v = unsafeDupablePerformIO $ VM.unsafeWrite v i a >> return v

umodify :: VU.Unbox a => Int -> (a -> a) -> VM.IOVector a -> VM.IOVector a
umodify i f v = unsafeDupablePerformIO $ VM.unsafeModify v f i >> return v

uthaw :: VU.Unbox a => VU.Vector a -> VM.IOVector a
uthaw = unsafeDupablePerformIO . VU.unsafeThaw

ufreeze :: VU.Unbox a => VM.IOVector a -> VU.Vector a
ufreeze = unsafeDupablePerformIO . VU.unsafeFreeze

dijkstra
  :: Int  -- ^ nodes
  -> V.Vector (VU.Vector (Int, Double))  -- ^ edges from i-th node: (end, cost)
  -> Int  -- ^ start node
  -> VU.Vector Double  -- ^ constructed graph
dijkstra n edges s = ufreeze $ snd $ fix
  ( \f (nodes, costs) -> case S.minView nodes of
    Nothing              -> (S.empty, costs)
    Just ((c, n), nodes) -> if c <= uread n costs
      then
        let es = edges V.! n
        in  f $ VU.foldl'
              ( \(ns, cs) (e, ec) ->
                let c' = c + ec
                in  c' `seq` if c' < uread e costs
                      then
                        let a = S.insert (c', e) ns
                            b = uwrite e c' cs
                        in  a `seq` b `seq` (a, b)
                      else (ns, cs)
              )
              (nodes, costs)
              es
      else f (nodes, costs)
  )
  (nodes0, costs0)
 where
  costs0 :: VM.IOVector Double
  costs0 = uwrite s 0 (uthaw $ VU.replicate n $ fromIntegral (maxBound :: Int))

  nodes0 :: S.Set (Double, Int)
  nodes0 = S.singleton (0, s)
