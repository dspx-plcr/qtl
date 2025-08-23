module Typer (
  Item(..),
  Term(..),

  pp,
  typecheck
)where

import Control.Monad.ST
import Data.Array
import Data.STRef
import Data.Text (Text, unpack)

import qualified HashMap as HM
import qualified Parser as P
import Source
import Error

data State = State {
  terms :: HM.HashMap Text Term,
  types :: HM.HashMap Text Term
}

data Item =
    Toplevel (Array Word Item)
  | Item { name :: Text, typ :: Term, val :: Term }
data Term =
    Level Word
  | Fun (Array Word Term)
  | Prim (Array Word Term)
  | Schema (Array Word Item)

newState :: State
newState = State { terms = HM.empty, types = HM.empty }

pp :: Item -> String
pp item = "<<unimplemented Typer.pp>>"

_typecheck :: STRef s State -> P.Item -> ST s (Result Item)
_typecheck str item = do
  st <- readSTRef str
  case item.term of
    P.Forest fs ->
      let f :: (Word, P.Item) -> ST s (Result (Word, Item))
          f (i, item) = do
            res <- _typecheck str item
            return $ res >>= \r -> Right (i, r)
          mkTerm :: [(Word, Item)] -> Result Item
          mkTerm = Right . Toplevel . array (bounds fs)
      in mapM f (assocs fs) >>= return . ((=<<) mkTerm) . sequence
    P.Atom a -> return $ case (HM.get st.types a, HM.get st.terms a) of
      (Nothing, Nothing) -> errorHere item.source $
        "unrecognised term `" ++ (unpack a) ++ "`"
      (Nothing, _) -> errorHere item.source $
        "internal error: term used before type is known"
      (_, Nothing) -> errorHere item.source $
        "term used before value is known `" ++ (unpack a) ++ "`"
      (Just typ, Just val) -> Right $ Item { name = a, typ, val }
    _ -> return $ errorHere item.source "<<unimplemented _typecheck>>"

typecheck :: P.Item -> Result Item
typecheck item = runST $ newSTRef newState >>= flip _typecheck item
