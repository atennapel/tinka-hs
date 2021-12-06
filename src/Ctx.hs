module Ctx where

import Data.Coerce (coerce)
import Text.Megaparsec (SourcePos)
import Data.List (intercalate)

import Common
import Levels
import Core
import Val
import Evaluation
import Surface

data BinderEntry = BinderEntry {
  bName :: Name,
  bIcit :: Icit,
  bInserted :: Bool,
  bTy :: Maybe VTy
}

type Binders = [BinderEntry]

data Ctx = Ctx {
  lvl :: Lvl,
  env :: Env,
  binders :: Binders,
  pos :: Maybe SourcePos
}

empty :: Ctx
empty = Ctx 0 [] [] Nothing

define :: Name -> VTy -> Val -> Ctx -> Ctx
define x t v (Ctx l e b pos) = Ctx (l + 1) (Right v : e) (BinderEntry x Expl False (Just t) : b) pos

bind :: Name -> Icit -> VTy -> Ctx -> Ctx
bind x i t (Ctx l e b pos) = Ctx (l + 1) (Right (VVar l) : e) (BinderEntry x i False (Just t) : b) pos

bindInsert :: Name -> Icit -> VTy -> Ctx -> Ctx
bindInsert x i t (Ctx l e b pos) = Ctx (l + 1) (Right (VVar l) : e) (BinderEntry x i True (Just t) : b) pos

bindLevel :: Name -> Ctx -> Ctx
bindLevel x (Ctx l e b pos) = Ctx (l + 1) (Left (vFinLevelVar l) : e) (BinderEntry x Impl False Nothing : b) pos

bindLevelInsert :: Name -> Ctx -> Ctx
bindLevelInsert x (Ctx l e b pos) = Ctx (l + 1) (Left (vFinLevelVar l) : e) (BinderEntry x Impl True Nothing : b) pos

enter :: SourcePos -> Ctx -> Ctx
enter p ctx = ctx { pos = Just p }

indexCtx :: Ctx -> Ix -> Maybe (Maybe VTy)
indexCtx ctx i = go (binders ctx) (coerce i)
  where
    go :: Binders -> Int -> Maybe (Maybe VTy)
    go [] _ = Nothing
    go (e : _) 0 = Just $ bTy e
    go (_ : bs) i = go bs (i - 1)
  
lookupCtx :: Ctx -> Name -> Maybe (Ix, Maybe VTy)
lookupCtx ctx x = go (binders ctx) 0
  where
    go :: Binders -> Int -> Maybe (Ix, Maybe VTy)
    go [] _ = Nothing
    go (BinderEntry y _ False mty : _) i | x == y = Just (Ix i, mty)
    go (_ : bs) i = go bs (i + 1)

closeVal :: Ctx -> Val -> Clos Val
closeVal ctx v = Clos (env ctx) (quote (lvl ctx + 1) v)

closeLevel :: Ctx -> Val -> Clos VFinLevel
closeLevel ctx v = Clos (env ctx) (quote (lvl ctx + 1) v)

showV :: Ctx -> Val -> String
showV ctx v = showC ctx (quote (lvl ctx) v)

names :: Ctx -> [Name]
names ctx = map bName (binders ctx)

showC :: Ctx -> Tm -> String
showC ctx tm = prettyCore (names ctx) tm

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
      AppLvl f l -> SAppLvl (go ns f) (finLevelToSurface ns l)
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
      Type (FinLevel l) -> SType (finLevelToSurface ns l)

finLevelToSurface :: [Name] -> FinLevel -> SLevel
finLevelToSurface ns (FLVar i) = SLVar (ns !! coerce i)
finLevelToSurface ns FLZ = SLNat 0
finLevelToSurface ns (FLS l) =
  case finLevelToSurface ns l of
    SLNat i -> SLNat (i + 1)
    l -> SLS l
finLevelToSurface ns (FLMax a b) = SLMax (finLevelToSurface ns a) (finLevelToSurface ns b)

prettyFinLevel :: [Name] -> FinLevel -> String
prettyFinLevel ns l = show (finLevelToSurface ns l)

prettyFinLevelCtx :: Ctx -> FinLevel -> String
prettyFinLevelCtx ctx l = prettyFinLevel (names ctx) l

instance Show Ctx where
  show ctx@(Ctx l env bs _) =
    let vs = zipWith var bs env in
    intercalate "\n" (map showVar vs)
    where
      var :: BinderEntry -> Either VFinLevel Val -> (Name, Icit, Either VFinLevel (VTy, Val))
      var (BinderEntry x i _ Nothing) (Left l) = (x, i, Left l)
      var (BinderEntry x i _ (Just ty)) (Right v) = (x, i, Right (ty, v))
      var _ _ = undefined

      showVar :: (Name, Icit, Either VFinLevel (VTy, Val)) -> String
      showVar (x, _, Left l') = "<" ++ x ++ ">" ++ showValue x (prettyFinLevelCtx ctx (quoteFinLevel l l'))
      showVar (x, Expl, Right (ty, v)) = x ++ " : " ++ showV ctx ty ++ showValue x (showV ctx v)
      showVar (x, Impl, Right (ty, v)) = "{" ++ x ++ "} : " ++ showV ctx ty ++ showValue x (showV ctx v)

      showValue :: Name -> String -> String
      showValue x v | x == v = ""
      showValue x v = " = " ++ v
