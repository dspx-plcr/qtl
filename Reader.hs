module Reader (
  Item(..),
  Term(..),
  pp,
  read,
  isAtomChar
) where

import Control.Arrow
import Control.Monad.ST
import Data.Array
import Data.Function
import Data.List (intercalate, reverse)
import Data.List.NonEmpty (NonEmpty(..))
import Data.STRef
import Data.Text (Text, pack, unpack)

import Error
import Source

data State = State {
  buf :: Slice,
  last :: Mark,
  stack :: [(Int, Mark, String)],
  nextTok :: Int
}

instance Show State where
  show st = "Reader.State { buf = " ++ show st.buf ++ ", stack = " ++
      show st.stack ++ ", nextTok = " ++ show st.nextTok ++ "}"

data Term =
    Forest (Array Word Item)
  | List (Array Word Item)
  | Atom Text

data Item = Item { source :: Slice, term :: Term }

newState :: String -> State
newState prog = State {
  buf = slice prog,
  stack = [],
  nextTok = 0
}

advance :: STRef s State -> ST s ()
advance st = modifySTRef st $ \st -> st { buf = Source.advance st.buf }

stop :: STRef s State -> ST s ()
stop st = modifySTRef st $ \st -> st { last = st.buf.begin }

isWhitespace c = c `elem` " \t\n\r"
isAtomChar c = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
  (c >= '0' && c <= '9') || (c `elem` "-=!@#$%^&*_+,./<>?;:~")
params :: [Item] -> Array Word Item
params ls = listArray (1, fromIntegral $ length ls) (reverse ls)

pp :: Item -> String
pp Item { term = (Atom str) } = unpack str
pp Item { term = (List arr) } =
  "(" ++ (intercalate " " (map pp (elems arr))) ++ ")"
pp Item { term = (Forest fst) } = intercalate "\n" . map pp . elems $ fst

readForest :: STRef s State -> ST s (Result Item)
readForest str = do
  st <- readSTRef str
  res <- helper []
  st' <- readSTRef str
  return $ case res of
    Left err -> Left err
    Right res ->
      let buf = st.buf
      in Right $ Item { source = buf { end = st'.last }, term = Forest res
      }
  where
    helper :: [Item] -> ST s (Result (Array Word Item))
    helper res = do
      st <- readSTRef str
      case peek st.buf of
        Nothing -> return . Right . params $ res
        Just '(' -> readList str >>= \case
          Left err -> return $ Left err
          Right item -> helper (item:res)
        Just c | isWhitespace c -> advance str >> helper res
        Just c | isAtomChar c -> readAtom str >>= \case
          Left err -> return $ Left err
          Right item -> helper (item:res)
        Just c -> return . errorHere st.buf $
          "unrecognised character `" ++ [c] ++ "`"
      
readList :: STRef s State -> ST s (Result Item)
readList str = do
  st <- readSTRef str
  advance str
  res <- helper []
  st' <- readSTRef str
  return $ case res of
    Left err -> mergeErrors (errorHere st.buf "error parsing list") (Left err)
    Right res ->
      let buf = st.buf
      in Right $ Item { source = buf { end = st'.last }, term = List res }
  where
    helper :: [Item] -> ST s (Result (Array Word Item))
    helper res = do
      st <- readSTRef str
      case peek st.buf of
        Nothing -> return $ errorHere st.buf "unexpected EOF when parsing list"
        Just ')' -> stop str >> advance str >> (return . Right $ params res)
        Just c -> do
          x <- _read str
          st' <- readSTRef str
          case x of
            Nothing -> return $
              errorHere st'.buf "unexpected EOF when parsing list"
            Just (Left err) -> return $ Left err
            Just (Right item) -> helper (item:res)

readAtom :: STRef s State -> ST s (Result Item)
readAtom str = do
  st <- readSTRef str
  res <- helper ""
  st' <- readSTRef str
  return $ case res of
    Left err -> Left err
    Right res ->
      let buf = st.buf
      in Right $ Item { source = buf { end = st'.last }, term = Atom res }
  where
    helper :: String -> ST s (Result Text)
    helper at = do
      st <- readSTRef str
      case peek st.buf of
        Just c | isAtomChar c -> stop str >> advance str >> helper (c:at)
        _ | null at -> return $ errorHere st.buf "expected atom character"
        _ -> return . Right . pack . reverse $ at

_read :: STRef s State -> ST s (Maybe (Result Item))
_read str = do
  st <- readSTRef str
  case peek st.buf of
    Nothing -> return Nothing
    Just '(' -> readList str >>= return . Just
    Just c | isWhitespace c -> advance str >> _read str
    Just c | isAtomChar c -> readAtom str >>= return . Just
    _ -> return . Just $ errorHere st.buf "unexpected character"

read :: String -> Result Item
read = newState >>> \st -> runST $ newSTRef st >>= readForest
