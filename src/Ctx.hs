module Ctx where

import Data.Coerce (coerce)
import Text.Megaparsec (SourcePos)

import Common
import Levels
import Core
import Val
import Evaluation
import Surface

type Binders = [(Name, Bool, Maybe VTy)]

data Ctx = Ctx {
  lvl :: Lvl,
  env :: Env,
  binders :: Binders,
  pos :: Maybe SourcePos
}

empty :: Ctx
empty = Ctx 0 [] [] Nothing

define :: Name -> VTy -> Val -> Ctx -> Ctx
define x t v (Ctx l e b pos) = Ctx (l + 1) (Right v : e) ((x, False, Just t) : b) pos

bind :: Name -> VTy -> Ctx -> Ctx
bind x t (Ctx l e b pos) = Ctx (l + 1) (Right (VVar l) : e) ((x, False, Just t) : b) pos

bindInsert :: Name -> VTy -> Ctx -> Ctx
bindInsert x t (Ctx l e b pos) = Ctx (l + 1) (Right (VVar l) : e) ((x, True, Just t) : b) pos

bindLevel :: Name -> Ctx -> Ctx
bindLevel x (Ctx l e b pos) = Ctx (l + 1) (Left (vFinLevelVar l) : e) ((x, False, Nothing) : b) pos

bindLevelInsert :: Name -> Ctx -> Ctx
bindLevelInsert x (Ctx l e b pos) = Ctx (l + 1) (Left (vFinLevelVar l) : e) ((x, True, Nothing) : b) pos

enter :: SourcePos -> Ctx -> Ctx
enter p ctx = ctx { pos = Just p }

indexCtx :: Ctx -> Ix -> Maybe (Maybe VTy)
indexCtx ctx i = go (binders ctx) (coerce i)
  where
    go :: Binders -> Int -> Maybe (Maybe VTy)
    go [] _ = Nothing
    go ((_, _, mty) : _) 0 = Just mty
    go (_ : bs) i = go bs (i - 1)
  
lookupCtx :: Ctx -> Name -> Maybe (Ix, Maybe VTy)
lookupCtx ctx x = go (binders ctx) 0
  where
    go :: Binders -> Int -> Maybe (Ix, Maybe VTy)
    go [] _ = Nothing
    go ((y, False, mty) : _) i | x == y = Just (Ix i, mty)
    go (_ : bs) i = go bs (i + 1)

closeVal :: Ctx -> Val -> Clos Val
closeVal ctx v = Clos (env ctx) (quote (lvl ctx + 1) v)

closeLevel :: Ctx -> Val -> Clos VFinLevel
closeLevel ctx v = Clos (env ctx) (quote (lvl ctx + 1) v)

showV :: Ctx -> Val -> String
showV ctx v = showC ctx (quote (lvl ctx) v)

showC :: Ctx -> Tm -> String
showC ctx tm = prettyCore (map fst3 (binders ctx)) tm
  where
    fst3 (a, _, _) = a

evalCtx :: Ctx -> Tm -> Val
evalCtx ctx tm = eval (env ctx) tm

finLevelCtx :: Ctx -> FinLevel -> VFinLevel
finLevelCtx ctx l = finLevel (env ctx) l

quoteCtx :: Ctx -> Val -> Tm
quoteCtx ctx v = quote (lvl ctx) v

prettyCore :: [Name] -> Tm -> String
prettyCore ns tm = show (go ns tm)
  where
    go ns = \case
      Var i -> SVar (ns !! coerce i)
      Global x -> SVar x
      Prim (Left x) -> SVar (show x)
      Prim (Right x) -> SVar (show x)
      App f a i -> SApp (go ns f) (go ns a) (Right i)
      Lam x i b -> SLam x (Right i) Nothing (go (x : ns) b)
      Pi x i t b -> SPi x i (go ns t) (go (x : ns) b)
      AppLvl f l -> SAppLvl (go ns f) (goFinLevel ns l)
      LamLvl x b -> SLamLvl x (go (x : ns) b)
      PiLvl x b -> SPiLvl x (go (x : ns) b)
      Sigma x t b -> SSigma x (go ns t) (go (x : ns) b)
      Pair a b -> SPair (go ns a) (go ns b)
      Let x t v b -> SLet x (Just $ go ns t) (go ns v) (go (x : ns) b)
      Proj s p -> SProj (go ns s) (goProj p)
        where
          goProj Fst = SFst
          goProj Snd = SSnd
          goProj (PNamed (Just x) _) = SNamed x
          goProj (PNamed Nothing i) = SIndex i
      Type Omega -> SVar "Type omega"
      Type Omega1 -> SVar "Type omega1"
      Type (FinLevel l) -> SType (goFinLevel ns l)

    goFinLevel ns (FLVar i) = SLVar (ns !! coerce i)
    goFinLevel ns FLZ = SLZ
    goFinLevel ns (FLS l) = SLS (goFinLevel ns l)
    goFinLevel ns (FLMax a b) = SLMax (goFinLevel ns a) (goFinLevel ns b)
