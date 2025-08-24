module Typer (
  Item(..),
  Term(..),

  pp,
  typecheck
)where

import Control.Monad.ST
import Data.Array
import Data.Function
import Data.STRef
import Data.Text (Text, unpack)

import qualified HashMap as HM
import qualified Parser as P
import Source
import Error

data State = State {
  terms :: HM.HashMap Text Tagged,
  types :: HM.HashMap Text Tagged
}

data Item =
    Toplevel (Array Word Item)
  | Item { name :: Text, typ :: Tagged, val :: Tagged }
  | Type Text Tagged
  | Value Text Tagged
data Tagged = Tagged { source :: Slice, term :: Term }
data Term =
    Level Word
  | Fun (Array Word Term)
  | Prim (Array Word Term)
  | Schema (Array Word Item)

newState :: State
newState = State { terms = HM.empty, types = HM.empty }

pp :: Item -> String
pp item = "<<unimplemented Typer.pp>>"

lookup :: State -> Slice -> Text -> Result Item
lookup st source name = case (HM.get st.types name, HM.get st.terms name) of
  (Nothing, Nothing) -> errorHere source $
    "unrecognised term `" ++ (unpack name) ++ "`"
  (Nothing, _) -> errorHere source $
    "internal error: term used before type is known"
  (_, Nothing) -> errorHere source $
    "term used before value is known `" ++ (unpack name) ++ "`"
  (Just typ, Just val) -> Right $ Item { name , typ, val }

normalise :: STRef s State -> P.Item -> ST s (Result Term)
normalise str item = do
  return $ errorHere item.source "<<unimplemented normalise>>"

_typecheck :: STRef s State -> P.Item -> ST s (Result Item)
_typecheck str item =
  case item.term of
    P.Forest fs ->
      let f :: (Word, P.Item) -> ST s (Result (Word, Item))
          f (i, item) = do
            res <- _typecheck str item
            return $ res >>= \r -> Right (i, r)
          mkTerm :: [(Word, Item)] -> Result Item
          mkTerm = Right . Toplevel . array (bounds fs)
      in mapM f (assocs fs) >>= return . ((=<<) mkTerm) . sequence
    P.Funcall fun args ->
      return $ errorHere item.source "<<unimplemented funcall>>"
      -- check the arguments
      -- normalise the term
      -- return the normalised Item
    P.Atom a -> do { st <- readSTRef str; return $ lookup st item.source a }
    P.PrimOp pop -> case pop of
      P.Claim name def -> do
        -- The order of evaluation here might be fucky: if the `def` clause
        -- claims to define `name`, then we'll report the original name as being
        -- a duplicate of the `def` name, instead of the other way around... but
        -- that also maybe makes sense? Since the definition term should be
        -- evaluated before this claim takes affect
        def' <- normalise str def
        st <- readSTRef str
        let tag term = Tagged { source = item.source, term }
        let { put tagged = case HM.getOrPut st.types name tagged of
          HM.Get it -> errorHere item.source $
            "duplicate declaration of type `" ++ (unpack name) ++ "`." ++
            " Previously declared at " ++ (show it.source)
          HM.Put map -> Right (map, Type name tagged) }
        (def' >>= put . tag) & \case
          Left e -> return (Left e)
          Right (map, res) ->
            modifySTRef str (\s -> s { types = map }) >> return (Right res)
      _ -> return $ errorHere item.source "<<unimplemented primop _typecheck>>"
    _ -> return $ errorHere item.source "<<unimplemented _typecheck>>"

typecheck :: P.Item -> Result Item
typecheck item = runST $ newSTRef newState >>= flip _typecheck item
