module Ctx where

import Text.Megaparsec (SourcePos)
import Data.List (intercalate)

import Common
import Core
import Surface
import Val
import Evaluation
import Globals

data Ctx = Ctx {
  lvl :: Lvl,
  ns :: [Name],
  ts :: [Val],
  vs :: Env,
  pos :: Maybe SourcePos,
  bds :: [BD],
  path :: Path
}

empty :: Ctx
empty = Ctx 0 [] [] [] Nothing [] Here

define :: Name -> Core -> Val -> Core -> Val -> Ctx -> Ctx
define x a t c v ctx = Ctx (lvl ctx + 1) (x : ns ctx) (t : ts ctx) (v : vs ctx) (pos ctx) (Defined : bds ctx) (Define (path ctx) x a c)

bind :: Name -> Val -> Ctx -> Ctx
bind x t ctx = Ctx (lvl ctx + 1) (x : ns ctx) (t : ts ctx) (vvar (lvl ctx) : vs ctx) (pos ctx) (Bound : bds ctx) (Bind (path ctx) x (quote (lvl ctx) t))

enter :: SourcePos -> Ctx -> Ctx
enter p ctx = ctx { pos = Just p }

closeVal :: Ctx -> Val -> Clos
closeVal ctx v = Clos (vs ctx) (quote (lvl ctx + 1) v)

showC :: Ctx -> Core -> String
showC ctx c = show $ fromCore (ns ctx) c

showVWith :: QuoteLevel -> Ctx -> Val -> String
showVWith ql ctx v = show $ fromCore (ns ctx) (quoteWith ql (lvl ctx) v)

showV :: Ctx -> Val -> String
showV ctx v = show $ fromCore (ns ctx) (quote (lvl ctx) v)

showLocal :: Ctx -> String
showLocal ctx = let zipped = zip3 (ns ctx) (ts ctx) (vs ctx) in
  intercalate "\n" $ map format zipped
    where
      format (x, t, v) = case showV ctx v of
        y | x == y -> x ++ " : " ++ showV ctx t
        sv -> x ++ " : " ++ showV ctx t ++ " = " ++ sv

lookupVarMaybe :: Ctx -> Name -> IO (Maybe (Ix, Val))
lookupVarMaybe ctx x = go (ns ctx) (ts ctx) 0
  where
    go :: [Name] -> [Val] -> Ix -> IO (Maybe (Ix, Val))
    go [] [] _ = return Nothing
    go (y : _) (ty : _) i | x == y = return $ Just (i, ty)
    go (_ : ns) (_ : ts) i = go ns ts (i + 1)
    go _ _ _ = error "impossible"

lookupVar :: Ctx -> Name -> IO (Ix, Val)
lookupVar ctx x = do
  res <- lookupVarMaybe ctx x
  case res of
    Just e -> return e
    Nothing -> error $ "undefined variable " ++ x

indexCtx :: Ctx -> Ix -> IO Val
indexCtx ctx = go (ts ctx)
  where
    go [] i = error $ "undefined var " ++ show i
    go (ty : _) 0 = return ty
    go (_ : tl) n = go tl (n - 1)

lookupGlobal :: Name -> IO GlobalEntry
lookupGlobal x = do
  case getGlobal x of
    Just e -> return e
    Nothing -> error $ "undefined global " ++ x
