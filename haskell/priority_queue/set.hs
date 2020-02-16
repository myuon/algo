import qualified Data.Set as S

-- Entry k v should be unique in a queue

data Entry k v = Entry k v
  deriving (Eq, Ord, Show)

newtype PQueue a = PQueue { getQueue :: S.Set a }

empty :: PQueue a
empty = PQueue S.empty

insert :: (Ord a) => a -> PQueue a -> PQueue a
insert a (PQueue set) = PQueue $ S.insert a set

popMax :: PQueue a -> Maybe (a, PQueue a)
popMax (PQueue set) = fmap (second PQueue) $ S.maxView set
