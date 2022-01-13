module Ctx where

import Data.Coerce (coerce)
import Text.Megaparsec (SourcePos)
import Data.List (intercalate)
import qualified Data.Set as S

import Common
import Levels
import Core
import Val
import Evaluation
import Surface
import Zonking

data BinderEntry = BinderEntry {
  bName :: Name,
  bInstance :: Bool,
  bIcit :: Icit,
  bInserted :: Bool,
  bTy :: Maybe (VTy, VLevel)
}

type Binders = [BinderEntry]

data Ctx = Ctx {
  lvl :: Lvl,
  env :: Env,
  binders :: Binders,
  bds :: [Maybe Icit],
  pos :: Maybe SourcePos
}

empty :: Ctx
empty = Ctx 0 [] [] [] Nothing

define :: Name -> Bool -> VTy -> VLevel -> Val -> Ctx -> Ctx
define x inst t u v (Ctx l e b bds pos) = Ctx (l + 1) (Right v : e) (BinderEntry x inst Expl False (Just (t, u)) : b) (Nothing : bds) pos

bind :: Name -> Icit -> VTy -> VLevel -> Ctx -> Ctx
bind x i t u (Ctx l e b bds pos) = Ctx (l + 1) (Right (VVar l) : e) (BinderEntry x False i False (Just (t, u)) : b) (Just i : bds) pos

bindInsert :: Name -> Icit -> VTy -> VLevel -> Ctx -> Ctx
bindInsert x i t u (Ctx l e b bds pos) = Ctx (l + 1) (Right (VVar l) : e) (BinderEntry x False i True (Just (t, u)) : b) (Just i : bds) pos

bindLevel :: Name -> Ctx -> Ctx
bindLevel x (Ctx l e b bds pos) = Ctx (l + 1) (Left (vFinLevelVar l) : e) (BinderEntry x False (Impl ImplUnif) False Nothing : b) (Just Expl : bds) pos

bindLevelInsert :: Name -> Ctx -> Ctx
bindLevelInsert x (Ctx l e b bds pos) = Ctx (l + 1) (Left (vFinLevelVar l) : e) (BinderEntry x False (Impl ImplUnif) True Nothing : b) (Just Expl : bds) pos

enter :: SourcePos -> Ctx -> Ctx
enter p ctx = ctx { pos = Just p }

indexCtx :: Ctx -> Ix -> Maybe (Maybe (VTy, VLevel))
indexCtx ctx i = go (binders ctx) (coerce i)
  where
    go :: Binders -> Int -> Maybe (Maybe (VTy, VLevel))
    go [] _ = Nothing
    go (e : _) 0 = Just $ bTy e
    go (_ : bs) i = go bs (i - 1)

lookupCtx :: Ctx -> Name -> Maybe (Ix, Maybe (VTy, VLevel))
lookupCtx ctx x = go (binders ctx) 0
  where
    go :: Binders -> Int -> Maybe (Ix, Maybe (VTy, VLevel))
    go [] _ = Nothing
    go (BinderEntry y _ _ False mty : _) i | x == y = Just (Ix i, mty)
    go (_ : bs) i = go bs (i + 1)

levelVars :: Ctx -> S.Set Lvl
levelVars ctx = S.fromList $ levels 0 $ binders ctx
  where
    levels i (BinderEntry _ _ _ _ Nothing : rest) = (lvl ctx - i - 1) : levels (i + 1) rest
    levels i (_ : rest) = levels (i + 1) rest
    levels i [] = []

closeVal :: Ctx -> Val -> Clos Val
closeVal ctx v = Clos (env ctx) (quote (lvl ctx + 1) v)

closeLevel :: Ctx -> Val -> Clos VFinLevel
closeLevel ctx v = Clos (env ctx) (quote (lvl ctx + 1) v)

closeCL :: Ctx -> VLevel -> ClosLvl
closeCL ctx v = ClosLvl (env ctx) (quoteLevel (lvl ctx + 1) v)

showV :: Ctx -> Val -> String
showV ctx v = showC ctx (quote (lvl ctx) v)

showVZ :: Ctx -> Val -> String
showVZ ctx v = showC ctx (zonkCtx ctx $ quote (lvl ctx) v)

names :: Ctx -> [Name]
names ctx = map bName (binders ctx)

showC :: Ctx -> Tm -> String
showC ctx tm = prettyCore (names ctx) tm

showCZ :: Ctx -> Tm -> String
showCZ ctx tm = prettyCore (names ctx) (zonkCtx ctx tm)

evalCtx :: Ctx -> Tm -> Val
evalCtx ctx tm = eval (env ctx) tm

finLevelCtx :: Ctx -> FinLevel -> VFinLevel
finLevelCtx ctx l = finLevel (env ctx) l

quoteCtx :: Ctx -> Val -> Tm
quoteCtx ctx v = quote (lvl ctx) v

quoteLevelCtx :: Ctx -> VLevel -> Level
quoteLevelCtx ctx l = quoteLevel (lvl ctx) l

quoteFinLevelCtx :: Ctx -> VFinLevel -> FinLevel
quoteFinLevelCtx ctx l = quoteFinLevel (lvl ctx) l

zonkCtx :: Ctx -> Tm -> Tm
zonkCtx ctx = zonk (lvl ctx) (env ctx)

zonkLevelCtx :: Ctx -> Level -> Level
zonkLevelCtx ctx = zonkLevel (lvl ctx) (env ctx)

prettyCore :: [Name] -> Tm -> String
prettyCore ns tm = show (go ns tm)
  where
    go ns = \case
      Var i -> SVar (ns !! coerce i)
      Global x -> SVar x
      Prim (Left x) -> SVar (show x)
      Prim (Right x) -> SVar (show x)
      App f a i -> SApp (go ns f) (go ns a) (Right i)
      Lam x i b -> let x' = chooseName x ns in SLam x' (Right i) Nothing (go (x' : ns) b)
      Pi x i t _ b _ ->let x' = chooseName x ns in SPi x' i (go ns t) (go (x' : ns) b)
      AppLvl f l -> SAppLvl (go ns f) (finLevelToSurface ns l) Nothing
      LamLvl x b -> SLamLvl x Nothing (go (x : ns) b)
      PiLvl x b _ -> let x' = chooseName x ns in SPiLvl x' (go (x' : ns) b)
      Sigma x t _ b _ -> let x' = chooseName x ns in SSigma x' (go ns t) (go (x' : ns) b)
      Con t -> SCon (go ns t)
      Refl -> SRefl
      LabelLit x -> SLabelLit x
      NatLit n -> SNatLit n
      Pair a b -> SPair (go ns a) (go ns b)
      Let x i t v b -> let x' = chooseName x ns in SLet x' i (Just $ go ns t) (go ns v) (go (x' : ns) b)
      Proj s p -> SProj (go ns s) (goProj p)
        where
          goProj Fst = SFst
          goProj Snd = SSnd
          goProj (PNamed (Just x) _) = SNamed x
          goProj (PNamed Nothing i) = SIndex i
      Type Omega -> SVar "Type omega"
      Type Omega1 -> SVar "Type omega1"
      Type (FinLevel l) -> SType (finLevelToSurface ns l)
      Meta m -> SVar $ "?" ++ show m
      InsertedMeta m _ -> SVar $ "?*" ++ show m

finLevelToSurface :: [Name] -> FinLevel -> SLevel
finLevelToSurface ns (FLVar i) = SLVar (ns !! coerce i)
finLevelToSurface ns FLZ = SLNat 0
finLevelToSurface ns (FLS l) =
  case finLevelToSurface ns l of
    SLNat i -> SLNat (i + 1)
    l -> SLS l
finLevelToSurface ns (FLMax a b) = SLMax (finLevelToSurface ns a) (finLevelToSurface ns b)
finLevelToSurface _ (FLMeta m) = SLVar $ "?l" ++ show m

prettyFinLevel :: [Name] -> FinLevel -> String
prettyFinLevel ns l = show (finLevelToSurface ns l)

prettyFinLevelCtx :: Ctx -> FinLevel -> String
prettyFinLevelCtx ctx l = prettyFinLevel (names ctx) l

prettyLevelCtx :: Ctx -> Level -> String
prettyLevelCtx ctx Omega = "omega"
prettyLevelCtx ctx Omega1 = "omega1"
prettyLevelCtx ctx (FinLevel l) = prettyFinLevelCtx ctx l

prettyVLevelCtx :: Ctx -> VLevel -> String
prettyVLevelCtx ctx l = prettyLevelCtx ctx (quoteLevel (lvl ctx) l)

instance Show Ctx where
  show ctx@(Ctx l env bs _ _) =
    let vs = zipWith var bs env in
    intercalate "\n" (map showVar vs)
    where
      var :: BinderEntry -> Either VFinLevel Val -> (Name, Icit, Either VFinLevel (VTy, Val))
      var (BinderEntry x _ i _ Nothing) (Left l) = (x, i, Left l)
      var (BinderEntry x _ i _ (Just (ty, _))) (Right v) = (x, i, Right (ty, v))
      var _ _ = undefined

      showVar :: (Name, Icit, Either VFinLevel (VTy, Val)) -> String
      showVar (x, _, Left l') = "<" ++ x ++ ">" ++ showValue x (prettyFinLevelCtx ctx (quoteFinLevel l l'))
      showVar (x, Expl, Right (ty, v)) = x ++ " : " ++ showVZ ctx ty ++ showValue x (showVZ ctx v)
      showVar (x, Impl ImplUnif, Right (ty, v)) = "{" ++ x ++ "} : " ++ showVZ ctx ty ++ showValue x (showVZ ctx v)
      showVar (x, Impl ImplInst, Right (ty, v)) = "{{" ++ x ++ "}} : " ++ showVZ ctx ty ++ showValue x (showVZ ctx v)

      showValue :: Name -> String -> String
      showValue x v | x == v = ""
      showValue x v = " = " ++ v
