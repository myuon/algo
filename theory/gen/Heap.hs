{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Heap where {

import qualified Control.Monad;
import qualified Control.Monad.ST;
import qualified Data.STRef;
import qualified Data.Array.ST;

type RealWorld = Control.Monad.ST.RealWorld;
type ST s a = Control.Monad.ST.ST s a;
type STRef s a = Data.STRef.STRef s a;
type STArray s a = Data.Array.ST.STArray s Integer a;

newSTRef = Data.STRef.newSTRef;
readSTRef = Data.STRef.readSTRef;
writeSTRef = Data.STRef.writeSTRef;

newArray :: Integer -> a -> ST s (STArray s a);
newArray k = Data.Array.ST.newArray (0, k - 1);

newListArray :: [a] -> ST s (STArray s a);
newListArray xs = Data.Array.ST.newListArray (0, (fromInteger . toInteger . length) xs - 1) xs;

newFunArray :: Integer -> (Integer -> a) -> ST s (STArray s a);
newFunArray k f = Data.Array.ST.newListArray (0, k - 1) (map f [0..k-1]);

lengthArray :: STArray s a -> ST s Integer;
lengthArray a = Control.Monad.liftM (\(_, l) -> l + 1) (Data.Array.ST.getBounds a);

readArray :: STArray s a -> Integer -> ST s a;
readArray = Data.Array.ST.readArray;

writeArray :: STArray s a -> Integer -> a -> ST s ();
writeArray = Data.Array.ST.writeArray;

}
