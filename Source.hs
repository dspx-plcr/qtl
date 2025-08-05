module Source (
  Slice,
  Mark,

  slice,
  peek_unsafe,
  peek,
  advance,
  skip,
  sub
) where

import Data.Maybe

data Mark = Mark {
  pos :: Int,
  line :: Int,
  col :: Int
}

instance Show (Mark) where
  show Mark { line, col } = show line ++ ":" ++ show col

nextLine :: Mark -> Mark
nextLine m = Mark (m.pos + 1) (m.line + 1) 1

nextCol :: Mark -> Mark
nextCol m = Mark (m.pos + 1) m.line (m.col + 1)

data Slice = Slice {
  buf :: String,
  begin :: Mark,
  end :: Mark
} deriving (Show)

slice :: String -> Slice
slice str =
  let ls = lines str
      begin = Mark 0 1 1
      end = Mark (length str - 1) (length ls) (length $ last ls)
  in Slice str begin end

peek_unsafe :: Slice -> Char
peek_unsafe Slice { buf } = head buf

peek :: Slice -> Maybe Char
peek sl@Slice { begin, end } =
  (if begin.pos <= end.pos then Just . peek_unsafe else const Nothing) sl

advance :: Slice -> Slice
advance s = sub s 1 Nothing

skip :: Slice -> Word -> Slice
skip s n =
  let (d, t) = splitAt (fromEnum n) s.buf
      f acc val = (if val == '\n' then nextLine else nextCol) acc
  in s { buf = t, begin = foldl f s.begin d }

sub :: Slice -> Word -> Maybe Word -> Slice
sub s n Nothing = skip s n
sub s n (Just m) = let s' = skip s n in s' {
	buf = take (fromEnum m) s'.buf,
  end = (skip s' m).begin
}
