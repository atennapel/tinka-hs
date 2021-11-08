module Elaboration (elaborate, elaborateDef, elaborateDefs) where

import Control.Monad.Trans.Reader (ask, local)

import Ctx
import Surface
import Core
import Val
import Common

checkOrInfer :: Ctx -> Surface -> Maybe Surface -> TC (Core, Core, Val)
checkOrInfer ctx v Nothing = do
  (cv, ty) <- infer ctx v
  gs <- ask
  return (cv, quote gs (lvl ctx) ty, ty)
checkOrInfer ctx v (Just t) = do
  (ct, _) <- inferUniv ctx t
  gs <- ask
  let ty = eval gs (vs ctx) ct
  cv <- check ctx v ty
  return (cv, ct, ty)

check :: Ctx -> Surface -> Val -> TC Core
check ctx tm ty =
  let fty = force ty in
  case (tm, fty) of
    (SPos p s, _) -> check (enter p ctx) s ty
    (SHole, _) -> do
      gs <- ask
      err $ "hole encountered: " ++ showV gs ctx ty
    (SAbs x Nothing b, VPi x' ty b') -> do
      gs <- ask
      cb <- check (bind x ty ctx) b (vinst gs b' $ vvar (lvl ctx))
      return $ Abs x (quote gs (lvl ctx) ty) cb
    (SPair a b, VSigma x ty b') -> do
      ta <- check ctx a ty
      gs <- ask
      tb <- check ctx b (vinst gs b' $ eval gs (vs ctx) ta)
      return $ Pair ta tb (quote gs (lvl ctx) ty)
    (SLet x t v b, _) -> do
      (cv, ct, pty) <- checkOrInfer ctx v t
      gs <- ask
      cb <- check (define x pty (eval gs (vs ctx) cv) ctx) b ty
      return $ Let x ct cv cb
    (SLift t, VU l) | l > 0 -> do
      c <- check ctx t (VU (l - 1))
      return $ Lift c
    (SLiftTerm t, VLift ty) -> do
      c <- check ctx t ty
      return $ LiftTerm c
    (SLower t, ty) -> do
      c <- check ctx t (VLift ty)
      return $ Lower c
    (s, _) -> do
      (c, ty') <- infer ctx s
      gs <- ask
      test (conv gs (lvl ctx) ty' ty) $ "check failed " ++ show s ++ " : " ++ showV gs ctx ty ++ ", got " ++ showV gs ctx ty'
      return c

inferUniv :: Ctx -> Surface -> TC (Core, ULvl)
inferUniv ctx tm = do
  (c, ty) <- infer ctx tm
  case force ty of
    VU l -> return (c, l)
    _ -> do
      gs <- ask
      err $ "expected a universe but got " ++ showV gs ctx ty ++ ", while checking " ++ show tm 

infer :: Ctx -> Surface -> TC (Core, Val)
infer ctx (SPos p s) = infer (enter p ctx) s
infer ctx (SU l) = return (U l, VU (l + 1))
infer ctx t@(SVar x l) =
  case toPrimName x of
    Just prim -> do
      gs <- ask
      return (Prim prim l, primType gs prim l)
    Nothing -> do
      res <- lookupVarMaybe ctx x
      case res of
        Just (i, ty) -> do
          test (l == 0) $ "cannot lift local var " ++ show t 
          return (Var i, ty)
        Nothing -> do
          gs <- ask
          e <- lookupGlobal x
          let vt = if l == 0 then gvtype e else eval gs [] (liftUniv l (gtype e))
          return (Global x l, vt)
infer ctx (SPrimElim x l k) = do
  case toPrimElimName x of
    Just prim -> do
      gs <- ask
      return (PrimElim prim l k, primElimType gs prim l k)
    Nothing -> err $ "undefined primitive " ++ x
infer ctx c@(SApp f a) = do
  (cf, fty) <- infer ctx f
  gs <- ask
  case force fty of
    VPi x t b -> do
      ca <- check ctx a t
      return (App cf ca, vinst gs b (eval gs (vs ctx) ca))
    _ -> err $ "not a pi type in " ++ show c ++ ", got " ++ showV gs ctx fty
infer ctx (SAbs x (Just t) b) = do
  (ct, _) <- inferUniv ctx t
  gs <- ask
  let ty = eval gs (vs ctx) ct
  (cb, rty) <- infer (bind x ty ctx) b
  return (Abs x ct cb, VPi x ty $ closeVal gs ctx rty)
infer ctx (SPi x t b) = do
  (ct, l1) <- inferUniv ctx t
  gs <- ask
  let ty = eval gs (vs ctx) ct
  (cb, l2) <- inferUniv (bind x ty ctx) b
  return (Pi x ct cb, VU (max l1 l2))
infer ctx (SSigma x t b) = do
  (ct, l1) <- inferUniv ctx t
  gs <- ask
  let ty = eval gs (vs ctx) ct
  (cb, l2) <- inferUniv (bind x ty ctx) b
  return (Sigma x ct cb, VU (max l1 l2))
infer ctx (SPair a b) = do
  (ta, va) <- infer ctx a
  (tb, vb) <- infer ctx b
  let vt = VSigma "_" va (Fun $ const vb)
  gs <- ask
  return (Pair ta tb (quote gs (lvl ctx) vt), vt)
infer ctx c@(SProj t p) = do
  (tm, vt) <- infer ctx t
  gs <- ask
  case (force vt, p) of
    (VSigma x ty c, Fst) -> return (Proj tm p, ty)
    (VSigma x ty c, Snd) -> return (Proj tm p, vinst gs c $ vproj (eval gs (vs ctx) tm) Fst)
    _ -> err $ "not a sigma type in " ++ show c ++ ", got " ++ showV gs ctx vt
infer ctx (SLet x t v b) = do
  (cv, ct, ty) <- checkOrInfer ctx v t
  gs <- ask
  (cb, rty) <- infer (define x ty (eval gs (vs ctx) cv) ctx) b
  return (Let x ct cv cb, rty)
infer ctx (SLift t) = do
  (c, l) <- inferUniv ctx t
  return (Lift c, VU (l + 1))
infer ctx (SLiftTerm t) = do
  (c, ty) <- infer ctx t
  return (LiftTerm c, VLift ty)
infer ctx tm@(SLower t) = do
  (c, ty) <- infer ctx t
  case force ty of
    VLift ty' -> return (Lower c, ty')
    _ -> do
      gs <- ask
      err $ "expected lift type in " ++ show tm ++ " but got " ++ showV gs ctx ty
infer ctx s = err $ "unable to infer " ++ show s

elaborate :: Ctx -> Surface -> TC (Core, Core)
elaborate ctx s = do
  (c, ty) <- infer ctx s
  gs <- ask
  return (c, quote gs 0 ty)

reduceExpectedLet :: Core -> Core
reduceExpectedLet (Let _ _ tm _) = tm
reduceExpectedLet tm = tm

elaborateDef :: Def -> TC GlobalCtx
elaborateDef (Def x ty tm) = do
  (etm', ety) <- elaborate empty (SLet x ty tm (SVar x 0))
  let etm = reduceExpectedLet etm'
  gs <- ask
  return $ GlobalEntry x etm ety (eval gs [] etm) (eval gs [] ety) : gs

elaborateDefs :: Defs -> TC GlobalCtx
elaborateDefs [] = do ask
elaborateDefs (hd : tl) = do
      ngs <- elaborateDef hd
      local (const ngs) $ elaborateDefs tl
