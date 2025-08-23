module HashMap (
  HashMap,
  empty,
  get
) where

import Data.Array
import Data.Hashable
import Data.List

type Bucket k v = [(k, v)]
data HashMap k v = HashMap {
  buckets :: (Array Word (Bucket k v)),
  len :: Word,
  cap :: Word
}

empty :: HashMap k v
empty = HashMap {
  buckets = array (0, 6) [(i, []) | i <- [0..]],
  len = 0,
  cap = 7
}

get :: (Hashable k, Eq k) => HashMap k v -> k -> Maybe v
get (HashMap { buckets, len, cap }) key =
  let h = fromInteger . toInteger . abs $ hash key
      b = buckets ! (h `mod` cap)
  in find (\(k,_) -> k == key) b >>= return . snd
