{-# LANGUAGE OverloadedStrings, BangPatterns, CPP #-}
#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE MagicHash, UnboxedTuples #-}
#endif
import Control.Monad.Fix
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VUM

#if __GLASGOW_HASKELL__ >= 710
import Data.ByteString.Internal (accursedUnutterablePerformIO)
#else
import GHC.IO (IO(IO),unsafeDupablePerformIO)
import GHC.Base (realWorld#)

{-# INLINE accursedUnutterablePerformIO #-}
accursedUnutterablePerformIO :: IO a -> a
accursedUnutterablePerformIO (IO m) = case m realWorld# of (# _, r #) -> r
#endif

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

data PQueue a = PQueue !Int !(VUM.IOVector a)

new :: VUM.Unbox a => Int -> PQueue a
new !s = PQueue 0 $ accursedUnutterablePerformIO $ VUM.new (s + 1)

push :: (Ord a, VUM.Unbox a, Bounded a) => a -> PQueue a -> PQueue a
push !a !(PQueue k vec) = PQueue (k + 1) vec'
 where
  vec' = up k a $ uwrite k a $ if VUM.length vec == k
    then accursedUnutterablePerformIO $ VUM.unsafeGrow vec (VUM.length vec * 2)
    else vec

  up !i !cv !vec = (\(_, v) -> v) $ fix
    ( \f (!ci, !vec) ->
      let pi = (ci - 1) `div` 2
          pv = if 0 < ci then uread pi vec else maxBound
      in  if 0 < ci && pv < cv
            then let vec' = uswap pi ci vec in vec' `seq` f (pi, vec')
            else (ci, vec)
    )
    (i, vec)

popMax :: (Ord a, Bounded a, VUM.Unbox a) => PQueue a -> Maybe (a, PQueue a)
popMax !(PQueue k vec) | k <= 0    = Nothing
                       | otherwise = Just (uread 0 vec, PQueue (k - 1) vec')
 where
  vec' = let v = uswap (k - 1) 0 vec in v `seq` down 0 (uread 0 vec) v

  down !i !cv !vec = (\(_, v) -> v) $ fix
    ( \ !f (!ci, !vec) ->
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

popMax' :: (Ord a, Bounded a, VUM.Unbox a) => PQueue a -> (a, PQueue a)
popMax' !pq = maybe (error "size < 0") id $ popMax pq

main = go $ new 0
 where
  go !queue = do
    b <- B.getLine
    if b == "end"
      then return ()
      else if B.head b == 'i'
        then do
          let Just (n, _) = B.readInt $ B.drop 7 b
          go $ push n queue
        else do
          let (x, queue') = popMax' queue
          print x
          go queue'
