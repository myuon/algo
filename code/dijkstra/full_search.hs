{-# LANGUAGE BangPatterns #-}
import Control.Arrow
import Control.Monad.Fix
import Data.Foldable
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM
import Data.ByteString.Internal (accursedUnutterablePerformIO)
import System.IO.Unsafe

uread :: VU.Unbox a => Int -> VM.IOVector a -> a
uread i v = accursedUnutterablePerformIO $ VM.unsafeRead v i

uwrite :: VU.Unbox a => Int -> a -> VM.IOVector a -> VM.IOVector a
uwrite i !a v = accursedUnutterablePerformIO $ VM.unsafeWrite v i a >> return v

umodify :: VU.Unbox a => Int -> (a -> a) -> VM.IOVector a -> VM.IOVector a
umodify i f v =
  accursedUnutterablePerformIO $ VM.unsafeModify v f i >> return v

uthaw :: VU.Unbox a => VU.Vector a -> VM.IOVector a
uthaw = accursedUnutterablePerformIO . VU.unsafeThaw

ufreeze :: VU.Unbox a => VM.IOVector a -> VU.Vector a
ufreeze = accursedUnutterablePerformIO . VU.unsafeFreeze

dijkstra
  :: (VU.Unbox a, Bounded a, Ord a, Num a)
  => Int  -- ^ nodes
  -> V.Vector [(Int, a)]  -- ^ edges from i-th node: (end, cost)
  -> Int  -- ^ start node
  -> VU.Vector a  -- ^ constructed graph
dijkstra !n !edges !s = ufreeze $ fst $ fix
  ( \f (!costs, !visited) -> case findMinView costs visited of
    (-1) -> (costs, visited)
    n ->
      let
        visited' = uwrite n True visited
        c        = uread n costs
      in
        if c <= uread n costs
          then
            let es = edges V.! n
            in  f
                $  flip (,) visited'
                $! foldl'
                     ( \(!cs) (!e, !ec) ->
                       let c' = c + ec
                       in  c' `seq` if c' < uread e costs
                             then uwrite e c' cs
                             else cs
                     )
                     costs
                     es
          else f (costs, visited')
  )
  (costs0, visited0)
 where
  costs0 :: (VU.Unbox a, Bounded a, Num a) => VUM.IOVector a
  costs0 = uwrite s 0 (uthaw $ VU.replicate n maxBound)

  visited0 :: VUM.IOVector Bool
  visited0 = uthaw $ VU.replicate n False

  findMinView
    :: (VU.Unbox a, Bounded a, Ord a)
    => VUM.IOVector a
    -> VUM.IOVector Bool
    -> Int
  findMinView vec visited =
    fst
      $ foldl'
          ( \(!j, !acc) !i ->
            let a = uread i vec in if a < acc then (i, a) else (j, acc)
          )
          (-1, maxBound)
      $ filter (\(!i) -> uread i visited == False) [0 .. n - 1]
