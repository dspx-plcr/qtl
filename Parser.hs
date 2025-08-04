module Parser (
  Item(..),
  Term(..),
  parse,
  pp
) where

import Data.Array (Array, array, assocs, bounds, (!))
import Data.Function ((&))
import Data.Ix (rangeSize)
import Data.Text (Text)

import Error
import Reader
import Source

data Item = Item { source :: Slice, term :: Term }
data Term =
    Forest (Array Word Item)
  | Funcall Item (Array Word Item)
  | PrimOp PrimOp
  | Atom Text

data PrimOp =
    Claim Text Item
  | Alias Text Item

pp :: Item -> String
pp Item { term = _ } = "<<unimplemented pp>>"

from :: Reader.Item -> Term -> Result Item
from item term = Right $ Item { source = item.source, term = term }

parseClaim :: Slice -> Array Word Reader.Item -> Result Term
parseClaim source claim = do
  let b@(l,u) = bounds claim
  if (rangeSize b /= 3)
    then errorHere source "CLAIM must have exactly 2 arguments"
    else return ()
  let id = claim ! (l+1)
  id <- case id.term of
    Reader.Atom atom -> return atom
    _ -> errorHere source "first argument of CLAIM must be an identifier"
  def <- parse $ claim ! (l+2)
  return . PrimOp $ Claim id def

parseAlias :: Slice -> Array Word Reader.Item -> Result Term
parseAlias source alias = errorHere source "<<unimplemented ALIAS parsing>>"

parseClaim :: Slice -> Array Word Reader.Item -> Result Term
parseType source typ = errorHere source "<<unimplemented TYPE parsing>>"

parseSum :: Slice -> Array Word Reader.Item -> Result Term
parseSum source sum = errorHere source "<<unimplemented SUM parsing>>"

parseSchema :: Slice -> Array Word Reader.Item -> Result Term
parseSchema source schema = errorHere source "<<unimplemented SCHEMA parsing>>"

parseFunc :: Slice -> Array Word Reader.Item -> Result Term
parseFunc source fun = errorHere source "<<unimplemented -> parsing>>"

parse :: Reader.Item -> Result Item
parse item =
  let e = errorHere item.source
      f res = do
        term <- res
        return Item { source = item.source, term = term }
  in case Reader.term item of
    --microhs doesn't instance Array as traversable
    --Reader.Forest items -> mapM parse items >>= f . Forest
    Reader.Forest items ->
      let g (i, e) = do { res <- parse e; return (i, res) }
      in mapM g (assocs items) >>= return . array (bounds items) >>=
        from item . Forest
    Reader.List items ->
      if (==) 0 . rangeSize . bounds $ items
      then e "TODO: how to deal with empty list?"
      else f $ case (items ! (items & bounds & fst)).term of
        Reader.Atom "claim" -> parseClaim item.source items
        Reader.Atom "alias" -> parseAlias item.source items
        Reader.Atom "Type" -> parseType item.source items
        Reader.Atom "sum" -> parseSum item.source items
        Reader.Atom "schema" -> parseSchema item.source items
        Reader.Atom "->" -> parseFunc item.source items
    Reader.Atom "claim" -> e "CLAIM must be used as a function"
    Reader.Atom "alias" -> e "ALIAS must be used as a function"
    Reader.Atom "sum" -> e "SUM must be used as a function"
    Reader.Atom "schema" -> e "SCHEMA must be used as a function"
    Reader.Atom "->" -> e "-> must be used as a function"
    Reader.Atom atom -> from item $ Atom atom
