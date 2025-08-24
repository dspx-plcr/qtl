module HashMap (
  HashMap,
  GetOrPut(..),
  empty,
  get,
  put,
  getOrPut,
) where

import Control.Monad.ST
import Data.Array
import Data.Hashable
import Data.List
import Data.STRef

type Bucket k v = [(k, v)]
data HashMap k v = HashMap {
  buckets :: (Array Word (Bucket k v)),
  len :: Word,
  cap :: Word
}

data GetOrPut k v = Get v | Put (HashMap k v)

empty :: HashMap k v
empty = HashMap {
  buckets = array (0, 6) [(i, []) | i <- [0..]],
  len = 0,
  cap = 7
}

grow :: Hashable k => HashMap k v -> HashMap k v
grow HashMap { buckets, len, cap } = runST $ do
  let cap' = ceiling $ 2.0 * (fromIntegral cap) / 3.0
  let hashfn = flip mod cap' . fromInteger . toInteger . abs . hash
  let pair i = newSTRef [] >>= return . (,) i
  buckets' <- mapM pair [0..cap'-1] >>= return . array (0, cap'-1)
  let store (k, v) = modifySTRef (buckets' ! (hashfn k)) ((:) (k,v))
  mapM_ (mapM_ store) $ elems buckets
  let extract (i, kvs) = readSTRef kvs >>= \kvs' -> return (i, kvs')
  buckets'' <- mapM extract (assocs buckets') >>= return . array (0, cap')
  return HashMap { buckets = buckets'', len, cap = cap' }

get :: (Hashable k, Eq k) => HashMap k v -> k -> Maybe v
get (HashMap { buckets, len, cap }) key =
  let h = fromInteger . toInteger . abs $ hash key
      b = buckets ! (h `mod` cap)
  in find (\(k,_) -> k == key) b >>= return . snd

putAssumeCap :: (Hashable k, Eq k) => HashMap k v -> k -> v -> HashMap k v
putAssumeCap map key value =
  let h = fromInteger . toInteger . abs $ hash key
      idx = mod h map.cap
      b = (:) (key, value) . filter ((/=) key . fst) $ map.buckets ! idx
  in HashMap { buckets = map.buckets // [(idx, b)], len = map.len, cap = map.cap }

put :: (Hashable k, Eq k) => HashMap k v -> k -> v -> HashMap k v
put map =
  let map' = if (fromIntegral map.cap) / (fromIntegral map.len) > 0.8
               then grow map else map
  in putAssumeCap map

getOrPut :: (Hashable k, Eq k) => HashMap k v -> k -> v -> GetOrPut k v
getOrPut map key value = case get map key of
  Nothing -> Put $ put map key value
  Just v -> Get v
