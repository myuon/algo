import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad
import Data.List
import qualified Data.Vector.Unboxed as VU
import Gauge
import QuickSort
import System.Random

randomSampleList :: Int -> IO [Int]
randomSampleList i = evaluate $ force (take i (randoms (mkStdGen 0) :: [Int]))

randomSampleVector :: Int -> IO (VU.Vector Int)
randomSampleVector i =
  evaluate $ force $ VU.fromList (take i (randoms (mkStdGen 0) :: [Int]))

main = do
  defaultMain
    [ bgroup
        "sort"
        [ bench "Data.List.sort" $ nfAppIO (fmap sort . randomSampleList) 1000
        , bench "Quicksort" $ nfAppIO (quicksortUM <=< randomSampleVector) 1000
        ]
    ]
