module Parser (
  Item(..),
  Term(..),
  PrimOp(..),
  parse,
  pp
) where

import Data.Array (Array, array, assocs, bounds, elems, listArray, (!))
import Data.Function ((&))
import Data.Ix (rangeSize)
import Data.List (intercalate)
import Data.Maybe (maybe)
import Data.Text (Text, unpack)
import Text.Read (readMaybe)

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
  | Function (Array Word Item) Item
  | Schema
    { params :: SchemaParams
    , indices :: SchemaIndices
    , prims :: SchemaPrims }
  | Type Word

data SchemaParams = SchemaParams {
  source :: Slice,
  items :: Array Word (Text, Item)
}

data SchemaIndices = SchemaIndices {
  source :: Slice,
  items :: Array Word Item
}

data SchemaPrims = SchemaPrims {
  items :: Array Word (Text, Item)
}

pp :: Item -> String
pp Item { term } = case term of
  Forest fs -> intercalate "\n" . map pp . elems $ fs
  Funcall fun params -> "(" ++ (pp fun) ++ (sp params) ++ (ppV params) ++ ")"
  PrimOp p -> case p of
    Claim id def -> "(claim " ++ (unpack id) ++ " " ++ (pp def) ++ ")"
    Alias id def -> "(alias " ++ (unpack id) ++ " " ++ (pp def) ++ ")"
    Function params ret -> "(-> " ++ (ppV params) ++ " " ++ (pp ret) ++ ")"
    Schema { params, indices, prims } -> "(schema (" ++
    	(ppBinds " " params.items) ++ ") (" ++ (ppV indices.items) ++ ")\n\t" ++
    	(ppBinds "\n\t" prims.items) ++ ")"
    Type level -> "(Type " ++ (show level) ++ ")"
  Atom atom -> unpack atom
  where
    ppV = intercalate " " . map pp . elems
    sp xs = if rangeSize (bounds xs) == 0 then "" else " "
    ppBinds int binds =
      let f (n, d) = "(" ++ (unpack n) ++ " " ++ (pp d) ++ ")"
      in intercalate int . map f $ elems binds

from :: Reader.Item -> Term -> Result Item
from item term = Right $ Item { source = item.source, term = term }

parseClaim :: Slice -> Array Word Reader.Item -> Result Term
parseClaim source claim = do
  let b@(l,_) = bounds claim
  if (rangeSize b /= 3)
    then errorSlice source "CLAIM must have exactly 2 arguments"
    else return ()
  let id = claim ! (l+1)
  id <- case id.term of
    Reader.Atom atom -> return atom
    _ -> errorSlice source "first argument of CLAIM must be an identifier"
  def <- parse $ claim ! (l+2)
  return . PrimOp $ Claim id def

parseAlias :: Slice -> Array Word Reader.Item -> Result Term
parseAlias source alias = do
  let b@(l,_) = bounds alias
  if (rangeSize b /= 3)
    then errorSlice source "ALIAS must have exactly 2 arguments"
    else return ()
  let id = alias ! (l+1)
  id <- case id.term of
    Reader.Atom atom -> return atom
    _ -> errorSlice source "first argument of ALIAS must be an identifier"
  def <- parse $ alias ! (l+2)
  return . PrimOp $ Alias id def

parseType :: Slice -> Array Word Reader.Item -> Result Term
parseType source typ = do
  let b@(l,_) = bounds typ
  if (rangeSize b /= 2)
    then errorSlice source "TYPE must have exactly 1 argument"
    else return ()
  lvl <- case (typ ! (l+1)).term of
    Reader.Atom l -> Right l
    _ -> errorSlice source "TYPE expects a non-negative int argument"
  let err = errorSlice source "TYPE expects a non-negative int argument"
  lvl <- maybe err Right . readMaybe . unpack $ lvl
  return . PrimOp $ Type lvl

parseSum :: Slice -> Array Word Reader.Item -> Result Term
parseSum source sum = errorSlice source "<<unimplemented SUM parsing>>"

parseSchema :: Slice -> Array Word Reader.Item -> Result Term
parseSchema source schema = do
  let b@(l,u) = bounds schema
  if (rangeSize b < 4)
    then errorSlice source "SCHEMA expects at least 3 arguments"
    else return ()

  let paramErr = "SCHEMA parameters are lists of a binding name and type"
  let primErr = "SCHEMA primitives are lists of a binding name and type"
  let parseBind :: String -> (Word, Reader.Item) -> Result (Word, (Text, Item))
      parseBind err (i, Reader.Item { source, term = Reader.List items }) = do
        let b@(l,u) = bounds items
        if (rangeSize b /= 2)
          then errorSlice source err
          else return ()
        id <- case (items ! l).term of
          Reader.Atom atom -> return atom
          _ -> errorSlice (items ! l).source
            "SCHEMA parameter binding must be an identifier"
        typ <- parse $ items ! (l+1)
        return (i, (id, typ))
      parseBind err (i, Reader.Item { source }) = errorSlice source err
  let parseIndex :: (Word, Reader.Item) -> Result (Word, Item)
      parseIndex (i, e) = parse e >>= \e -> return (i, e)
  let _:params:indices:prims = map snd $ assocs schema
  params <- case schema ! (l+1) of
    Reader.Item { source, term = Reader.List items } -> do
      its <- mapM (parseBind paramErr) $ assocs items
      let items' = array (bounds items) its
      return SchemaParams { source, items = items' }
    _ -> errorSlice source "SCHEMA parameter list must be a list of lists"
  indices <- case schema ! (l+2) of
    Reader.Item { source, term = Reader.List items } -> do
      its <- mapM parseIndex $ assocs items
      let items' = array (bounds items) its
      return SchemaIndices { source, items = items' }
    _ -> errorSlice source "SCHEMA indices list must be a list"
  prims <- do
    its <- mapM (parseBind primErr) . zip [l..] $ prims
    let items = array (l, u-3) its
    return SchemaPrims { items }
  return . PrimOp $ Schema { params, indices, prims }

parseFunc :: Slice -> Array Word Reader.Item -> Result Term
parseFunc source fun = do
  let b@(l,u) = bounds fun
  if rangeSize b < 3
    then errorSlice source "-> type must have at least one parameter and return"
    else return ()
  ret <- parse $ fun ! u
  let its = take (rangeSize b - 2) . drop 1 $ elems fun
  params <- mapM parse its
  return . PrimOp $ Function (listArray (l,u-2) params) ret

parse :: Reader.Item -> Result Item
parse item =
  let e = errorSlice item.source
      f res = do
        term <- res
        return Item { source = item.source, term = term }
  in case item.term of
    --microhs doesn't instance Array as traversable
    --Reader.Forest items -> mapM parse items >>= f . Forest
    Reader.Forest items ->
      let g (i, e) = do { res <- parse e; return (i, res) }
      in mapM g (assocs items) >>= return . array (bounds items) >>=
        from item . Forest
    Reader.List items ->
      let b@(l,u) = bounds items in
      if rangeSize b == 0
      then e "TODO: how to deal with empty list?"
      else f $ case (items ! (items & bounds & fst)).term of
        Reader.Atom "claim" -> parseClaim item.source items
        Reader.Atom "alias" -> parseAlias item.source items
        Reader.Atom "Type" -> parseType item.source items
        Reader.Atom "sum" -> parseSum item.source items
        Reader.Atom "schema" -> parseSchema item.source items
        Reader.Atom "->" -> parseFunc item.source items
        _ -> do
          let fun:params = elems items
          fun <- parse fun
          params <- mapM parse params
          return $ Funcall fun (listArray (l,u-1) params)
    Reader.Atom "claim" -> e "CLAIM must be used as a function"
    Reader.Atom "alias" -> e "ALIAS must be used as a function"
    Reader.Atom "sum" -> e "SUM must be used as a function"
    Reader.Atom "schema" -> e "SCHEMA must be used as a function"
    Reader.Atom "->" -> e "-> must be used as a function"
    Reader.Atom atom -> from item $ Atom atom
