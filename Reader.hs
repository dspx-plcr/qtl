module Reader (
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

import Error
import Source

data State = State {
  buf :: Slice,
  stack :: [(Int, Mark, String)],
  nextTok :: Int
}

instance Show State where
  show st = "Reader.State { buf = " ++ show st.buf ++ ", stack = " ++
      show st.stack ++ ", nextTok = " ++ show st.nextTok ++ "}"

data Term =
    Forest Slice (Array Int Term)
  | List Slice (Array Int Term)
  | Atom Slice String

newState :: String -> State
newState prog = State {
  buf = slice prog,
  stack = [],
  nextTok = 0
}

advance :: State -> State
advance st = st { buf = Source.advance st.buf }

isWhitespace c = c `elem` " \t\n\r"
isAtomChar c = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
  (c >= '0' && c <= '9') || (c `elem` "-=!@#$%^&*_+,./<>?;:~")
params ls = listArray (1, length ls) (reverse ls)

pp :: Term -> String
pp (Atom _ str) = str
pp (List _ arr) = "(" ++ (intercalate " " (map pp (elems arr))) ++ ")"
pp (Forest _ fst) = intercalate "\n" . map pp . elems $ fst

readForest :: STRef s State -> ST s (Result Term)
readForest str = do
  st <- readSTRef str
  res <- helper []
  st' <- readSTRef str
  return $ case res of
    Left err -> Left err
    Right res ->
      let buf = st.buf in Right . Forest (buf { end = st'.buf.end }) $ res
  where
    helper :: [Term] -> ST s (Result (Array Int Term))
    helper res = do
      st <- readSTRef str
      case peek st.buf of
        Nothing -> return . Right . params $ res
        Just '(' -> readList str >>= \case
          Left err -> return $ Left err
          Right term -> helper (term:res)
        Just c | isWhitespace c -> modifySTRef str advance >> helper res
        Just c | isAtomChar c -> readAtom str >>= \case
        	Left err -> return $ Left err
        	Right term -> helper (term:res)
      
readList :: STRef s State -> ST s (Result Term)
readList str = do
  st <- readSTRef str
  modifySTRef str advance
  res <- helper []
  st' <- readSTRef str
  return $ case res of
    Left err -> mergeErrors (errorHere st.buf "error parsing list") (Left err)
    Right res ->
      let buf = st.buf in Right . List (buf { end = st'.buf.end }) $ res
  where
    helper :: [Term] -> ST s (Result (Array Int Term))
    helper res = do
      st <- readSTRef str
      case peek st.buf of
        Nothing -> return $ errorHere st.buf "unexpected EOF when parsing list"
        Just ')' -> do
          modifySTRef str advance
          st' <- readSTRef str
          let end = st'.buf.begin
          return . Right $ params res
        Just c -> do
          x <- _read str
          st' <- readSTRef str
          case x of
            Nothing -> return $
              errorHere st'.buf "unexpected EOF when parsing list"
            Just (Left err) -> return $ Left err
            Just (Right term) -> helper (term:res)

readAtom :: STRef s State -> ST s (Result Term)
readAtom str = do
  st <- readSTRef str
  res <- helper ""
  st' <- readSTRef str
  return $ case res of
    Left err -> Left err
    Right res ->
      let buf = st.buf in Right . Atom (buf { end = st'.buf.end }) $ res
  where
    helper :: String -> ST s (Result String)
    helper at = do
      st <- readSTRef str
      case peek st.buf of
        Just c | isAtomChar c -> modifySTRef str advance >> helper (c:at)
        _ | null at -> return $ errorHere st.buf "expected atom character"
        _ -> return . Right $ reverse at

_read :: STRef s State -> ST s (Maybe (Result Term))
_read str = do
  st <- readSTRef str
  case peek st.buf of
    Nothing -> return Nothing
    Just '(' -> readList str >>= return . Just
    Just c | isWhitespace c -> modifySTRef str advance >> _read str
    Just c | isAtomChar c -> readAtom str >>= return . Just
    _ -> return . Just $ errorHere st.buf "unexpected character"

read :: String -> Result Term
read = newState >>> \st -> runST $ newSTRef st >>= readForest
