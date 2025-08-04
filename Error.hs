module Error (
  Error,
  Result,
  
  errorHere,
  errorSlice,
  mergeErrors,
  buildMessage
) where

import Data.List hiding (append)
import Data.List.NonEmpty (NonEmpty((:|)), toList, append)

import Source

type Result a = Either (NonEmpty Error) a
data Error = Error {
  source :: Slice,
  msg :: String
}

errorHere :: Slice -> String -> Result a
errorHere sl st = Left (Error sl { end = sl.begin } st :| [])

errorSlice :: Slice -> String -> Result a
errorSlice sl st = Left (Error sl st :| [])

mergeErrors :: Result a -> Result a -> Result a
mergeErrors (Right _) ys = ys
mergeErrors xs (Right _) = xs
mergeErrors (Left xs) (Left ys) = Left $ append xs ys

buildMessage :: NonEmpty Error -> String
buildMessage = intercalate "\n" . map f . toList
  where f e = (show e.source.begin) ++
          (if e.source.begin.pos /= e.source.end.pos
           then "--" ++ show e.source.end else "") ++
          " " ++ e.msg
