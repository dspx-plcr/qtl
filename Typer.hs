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
  | Self -- TODO: Do we need to also track the name(id??) of the enclosing type?
  | Schema
    { params :: Array Word (Text, Tagged)
    , indices :: Array Word Tagged
    , prims :: Array Word (Text, Tagged) }

instance Eq Tagged where
  tag == tag' = tag.term == tag'.term

instance Eq Term where
  Level lvl == Level lvl' = lvl == lvl'
  Fun fun == Fun fun' = fun == fun'
  Prim prim == Prim prim' = prim == prim'
  Self == Self = True
  Schema params indices prims == Schema params' indices' prims' =
    params == params' && indices == indices' && prims == prims'
  _ == _ = False

newState :: State
newState = State { terms = HM.empty, types = HM.empty }

pp :: Item -> String
pp Item { name, typ, val } =
  "(claim " ++ (unpack name) ++ " " ++ (ppTerm typ.term) ++ ")\n"
  ++ "(alias " ++ (unpack name) ++ " " ++ (ppTerm val.term) ++ ")\n"

ppTerm :: Term -> String
ppTerm = \case
  Level lvl -> "(Type " ++ (show lvl) ++ ")"
  Fun fun -> "(->)"
  Prim prim -> "<<unimplemented prim pp>>"
  Self -> "<<self>>"
  Schema _ _ _ -> "<<unimplemented schema pp>>"

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
normalise str item =
  case item.term of
    P.PrimOp pop -> case pop of
      P.Type level -> return . Right $ Level level
      P.Schema { params, indices, prims } -> do
        let { normPair it = normalise str (snd it) >>= return . \case
          Left e -> Left e
          Right res -> Right
            (fst it, Tagged { source = (snd it).source, term = res }) }
        let { normOne it = normalise str it >>= return . \case
          Left e -> Left e
          Right res -> Right $ Tagged { source = it.source, term = res } }
        params' <- mapM normPair (elems params.items) >>= return . mapM id
        indices' <- mapM normOne (elems indices.items) >>= return . mapM id
        -- TODO: define the params locally for this one
        prims' <- mapM normPair (elems prims.items) >>= return . mapM id
        return $ do
          params'' <- params'
          indices'' <- indices'
          prims'' <- prims'
          Right $ Schema {
            params = listArray (bounds params.items) params'',
            indices = listArray (bounds indices.items) indices'',
            prims = listArray (bounds prims.items) prims''
          }
      _ -> return $ errorHere item.source "<<unimplemented normalise primop>>"
    P.Atom name -> do
      s <- readSTRef str
      return $ case HM.get s.terms name of
        Nothing -> errorHere item.source $
          "use of undefined term `" ++ (unpack name) ++ "`"
        Just (Tagged _ term) -> Right term
    _ -> return $ errorHere item.source "<<unimplemented normalise>>"

getType :: Term -> Term
getType = \case
  Level lvl -> Level (lvl + 1)
  Fun fun -> Self -- TODO: actually do this
  Prim prim -> Fun prim
  Self -> Self -- TODO: this is almost surely wrong?
  Schema { params, indices, prims } -> Self -- TODO: actually do this

hasType :: Tagged -> Tagged -> Result ()
hasType val typ =
  let vtyp = getType val.term
  in if typ.term == vtyp
     then Right ()
     else errorHere val.source $ "value has type `" ++ (ppTerm vtyp)
       ++ "`, but expected type of `" ++ (ppTerm typ.term) ++ "`"

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
      P.Alias name def -> readSTRef str >>= \st -> case HM.get st.types name of
        Nothing -> return . errorHere item.source $
          "attempting to define value with no declared type"
        Just typ -> do
          tmp <- do
            s <- readSTRef str
            let terms = HM.put s.terms name $
                  Tagged { source = def.source, term = Self }
            newSTRef $ s { terms }
          -- The order of evaluation here might be fucky: if the `def` clause
          -- claims to define `name`, then we'll report the original name as
          -- being a duplicate of the `def` name, instead of the other way
          -- around... but that also maybe makes sense? Since the definition
          -- term should be evaluated before this claim takes affect
          -- TODO: normalise after the check we haven't defined already
          def' <- normalise tmp def
          st <- readSTRef str
          let tag term = Tagged { source = def.source, term }
          let { put tagged = case HM.getOrPut st.terms name tagged of
            HM.Get it -> errorHere item.source $
              "duplicate definition of value `" ++ (unpack name) ++ "`." ++
              " Previously defined at " ++ (show it.source)
            HM.Put map -> Right (map, tagged) }
          -- TODO: clense your sould and fix this garbage
          do { d <- def' >>= return . tag; hasType d typ; put d } & \case
            Left e -> return (Left e)
            Right (map, val) -> do
              modifySTRef str (\s -> s { terms = map })
              return . Right $ Item { name, typ, val }
      P.Claim name def -> do
        -- The order of evaluation here might be fucky: if the `def` clause
        -- claims to define `name`, then we'll report the original name as being
        -- a duplicate of the `def` name, instead of the other way around... but
        -- that also maybe makes sense? Since the definition term should be
        -- evaluated before this claim takes affect
        -- TODO: normalise after the check we haven't declared already
        def' <- normalise str def
        st <- readSTRef str
        let tag term = Tagged { source = def.source, term }
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
