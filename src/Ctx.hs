module Ctx where

import Text.Megaparsec (SourcePos)
import Data.List (intercalate)

import Common
import Core
import Surface
import Val
import Evaluation
import Globals
import Zonking
import Unification (strLevel)

data Path
  = Here
  | Define Path Name Core Core
  | Bind Path Name Icit Core VLevel

closeType :: Lvl -> Path -> Core -> VLevel -> IO Core
closeType k mcl b ub = case mcl of
  Here -> return b
  Bind mcl x i a ua -> do
    ub' <- strLevel k k ub
    closeType (k - 1) mcl (Pi x i a (quoteLevel k ua) b ub') (vlmax ua ub)
  Define mcl x a t -> closeType (k - 1) mcl (Let x a t b) ub

data Ctx = Ctx {
  lvl :: Lvl,
  ns :: [Name],
  allns :: [Either Name Name],
  ts :: [Val],
  vs :: Env,
  ctxus :: [VLevel],
  pos :: Maybe SourcePos,
  pruning :: Pruning,
  path :: Path
}

names :: Ctx -> [Name]
names = reverse . go . path
  where
    go Here = []
    go (Define p x _ _) = x : go p
    go (Bind p x _ _ _) = x : go p

empty :: Ctx
empty = Ctx 0 [] [] [] [] [] Nothing [] Here

define :: Name -> Core -> Val -> VLevel -> Core -> Val -> Ctx -> Ctx
define x a t u c v ctx = Ctx (lvl ctx + 1) (x : ns ctx) (Right x : allns ctx) (t : ts ctx) (v : vs ctx) (u : ctxus ctx) (pos ctx) (Nothing : pruning ctx) (Define (path ctx) x a c)

bind :: Name -> Icit -> Val -> VLevel -> Ctx -> Ctx
bind x i t u ctx = Ctx (lvl ctx + 1) (x : ns ctx) (Right x : allns ctx) (t : ts ctx) (vvar (lvl ctx) : vs ctx) (u : ctxus ctx) (pos ctx) (Just i : pruning ctx) (Bind (path ctx) x i (quote (lvl ctx) t) u)

bindInsert :: Name -> Icit -> Val -> VLevel -> Ctx -> Ctx
bindInsert x i t u ctx = Ctx (lvl ctx + 1) (ns ctx) (Left x : allns ctx) (t : ts ctx) (vvar (lvl ctx) : vs ctx) (u : ctxus ctx) (pos ctx) (Just i : pruning ctx) (Bind (path ctx) x i (quote (lvl ctx) t) u)

enter :: SourcePos -> Ctx -> Ctx
enter p ctx = ctx { pos = Just p }

closeVal :: Ctx -> Val -> Clos
closeVal ctx v = Clos (vs ctx) (quote (lvl ctx + 1) v)

closeVLevel :: Ctx -> VLevel -> ClosLevel
closeVLevel ctx v = ClosLevel (vs ctx) (quoteLevel (lvl ctx + 1) v)

allNames :: Ctx -> [Name]
allNames ctx = map (either id id) $ allns ctx

showC :: Ctx -> Core -> String
showC ctx c = show $ fromCore (allNames ctx) c

showVWith :: QuoteLevel -> Ctx -> Val -> String
showVWith ql ctx v = show $ fromCore (allNames ctx) (quoteWith ql (lvl ctx) v)

showV :: Ctx -> Val -> String
showV ctx v = show $ fromCore (allNames ctx) (quote (lvl ctx) v)

showVZ :: Ctx -> Val -> String
showVZ ctx v = show $ fromCore (allNames ctx) (zonkCtx ctx $ quote (lvl ctx) v)

showVLevel :: Ctx -> VLevel -> String
showVLevel ctx VOmega = "omega"
showVLevel ctx VOmegaSuc = "omega^"
showVLevel ctx (VFin v) = showV ctx v

showCZ :: Ctx -> Core -> String
showCZ ctx c = showC ctx (zonkCtx ctx c)

showVLevelZ :: Ctx -> VLevel -> String
showVLevelZ ctx (VFin v) = showVZ ctx v
showVLevelZ ctx l = showVLevel ctx l

showLocal :: Ctx -> String
showLocal ctx = let zipped = zip3 (allNames ctx) (ts ctx) (vs ctx) in
  intercalate "\n" $ map format zipped
    where
      format (x, t, v) = case showV ctx v of
        y | x == y -> x ++ " : " ++ showV ctx t
        sv -> x ++ " : " ++ showV ctx t ++ " = " ++ sv

lookupVarMaybe :: Ctx -> Name -> IO (Maybe (Ix, Val, VLevel))
lookupVarMaybe ctx x = go (allns ctx) (ts ctx) (ctxus ctx) 0
  where
    go :: [Either Name Name] -> [Val] -> [VLevel] -> Ix -> IO (Maybe (Ix, Val, VLevel))
    go [] [] [] _ = return Nothing
    go (Right y : _) (ty : _) (u : _) i | x == y = return $ Just (i, ty, u)
    go (_ : ns) (_ : ts) (_ : us) i = go ns ts us (i + 1)
    go ns ts us i =
      error $ "impossible (" ++ show (length ns) ++ ", " ++ show (length ts) ++ ", " ++ show (length us) ++ ", " ++ show i ++ ")"

lookupVar :: Ctx -> Name -> IO (Ix, Val, VLevel)
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

zonkCtx :: Ctx -> Core -> Core
zonkCtx ctx = zonk (lvl ctx) (vs ctx)

zonkLevelCtx :: Ctx -> Level -> Level
zonkLevelCtx ctx = zonkLevel (lvl ctx) (vs ctx)
