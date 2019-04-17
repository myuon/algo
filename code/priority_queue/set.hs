-- Entry k v should be unique in a queue

data Entry k v = Entry k v
  deriving (Eq, Ord, Show)

newtype PQueue k v = PQueue { getQueue :: S.Set (Entry k v) }

empty :: PQueue k v
empty = PQueue S.empty

insert :: (Ord k, Ord v) => k -> v -> PQueue k v -> PQueue k v
insert k v (PQueue set) = PQueue $ S.insert (Entry k v) set

popMax :: PQueue k v -> Maybe (Entry k v, PQueue k v)
popMax (PQueue set) = fmap (second PQueue) $ S.maxView set
