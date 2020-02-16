{-# LANGUAGE BangPatterns #-}
import Control.Monad.Fix
import Data.Foldable
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import qualified Data.ByteString.Char8 as B
import Data.ByteString.Internal (accursedUnutterablePerformIO)
import Debug.Trace

uread :: VUM.Unbox a => Int -> VUM.IOVector a -> a
uread !i !v = accursedUnutterablePerformIO $ VUM.unsafeRead v i

uwrite :: VUM.Unbox a => Int -> a -> VUM.IOVector a -> VUM.IOVector a
uwrite !i !a !v =
  accursedUnutterablePerformIO $ VUM.unsafeWrite v i a >> return v

uswap :: VUM.Unbox a => Int -> Int -> VUM.IOVector a -> VUM.IOVector a
uswap !i !j !v =
  accursedUnutterablePerformIO $ VUM.unsafeSwap v i j >> return v

uthaw :: VUM.Unbox a => VU.Vector a -> VUM.IOVector a
uthaw !v = accursedUnutterablePerformIO $ VU.unsafeThaw v

ufreeze :: VUM.Unbox a => VUM.IOVector a -> VU.Vector a
ufreeze !v = accursedUnutterablePerformIO $ VU.unsafeFreeze v

new :: VUM.Unbox a => Int -> PQueue a
new !s = PQueue 0 $ accursedUnutterablePerformIO $ VUM.new (s + 1)

umodifyV :: Int -> (a -> a) -> VM.IOVector a -> VM.IOVector a
umodifyV !i !f !v = accursedUnutterablePerformIO $ VM.modify v f i >> return v

uthawV :: V.Vector a -> VM.IOVector a
uthawV !v = accursedUnutterablePerformIO $ V.thaw v

ufreezeV :: VM.IOVector a -> V.Vector a
ufreezeV !v = accursedUnutterablePerformIO $ V.freeze v

dijkstra
  :: Int  -- ^ nodes
  -> V.Vector [(Int, Int)]  -- ^ edges from i-th node: (end, cost)
  -> Int  -- ^ start node
  -> Int  -- ^ end node
  -> VU.Vector Int  -- ^ constructed graph
dijkstra !n !edges !s !t = ufreeze $ snd $ fix
  ( \f (!nodes, !costs) -> case popMin nodes of
    Nothing              -> (nodes, costs)
    Just ((c, n), nodes) -> if c <= uread n costs
      then
        let es = edges V.! n
        in  f $ foldl'
              ( \(!ns, !cs) (!e, !ec) ->
                let c' = c + ec
                in  if c' < uread e costs
                      then (push (c', e) ns, uwrite e c' cs)
                      else (ns, cs)
              )
              (nodes, costs)
              es
      else f (nodes, costs)
  )
  (nodes0, costs0)
 where
  costs0 :: VUM.IOVector Int
  costs0 = uwrite s 0 $ uthaw $ VU.replicate n maxBound

  nodes0 :: PQueue (Int, Int)
  nodes0 = push (0, s) $ new 0
