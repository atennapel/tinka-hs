module Elaboration (elaborate) where

import Ctx
import Surface
import Core
import Val
import Common

checkOrInfer :: Ctx -> Surface -> Maybe Surface -> TC (Core, Core, Val)
checkOrInfer ctx v Nothing = do
  (cv, ty) <- infer ctx v
  return (cv, quote (lvl ctx) ty, ty)
checkOrInfer ctx v (Just t) = do
  (ct, _) <- inferUniv ctx t
  let ty = eval (vs ctx) ct
  cv <- check ctx v ty
  return (cv, ct, ty)

check :: Ctx -> Surface -> Val -> TC Core
check ctx (SPos p s) ty = check (enter p ctx) s ty
check ctx SHole ty = err $ "hole encountered: " ++ showV ctx ty
check ctx (SAbs x Nothing b) (VPi x' ty b') = do
  cb <- check (bind x ty ctx) b (vinst b' $ vvar (lvl ctx))
  return $ Abs x (quote (lvl ctx) ty) cb
check ctx (SPair a b) tt@(VSigma x ty b') = do
  ta <- check ctx a ty
  tb <- check ctx b (vinst b' $ eval (vs ctx) ta)
  return $ Pair ta tb (quote (lvl ctx) tt)
check ctx (SLet x t v b) rty = do
  (cv, ct, ty) <- checkOrInfer ctx v t
  cb <- check (define x ty (eval (vs ctx) cv) ctx) b rty
  return $ Let x ct cv cb
check ctx s ty = do
  (c, ty') <- infer ctx s
  test (conv (lvl ctx) ty' ty) $ "check failed " ++ show s ++ " : " ++ showV ctx ty ++ ", got " ++ showV ctx ty'
  return c

inferUniv :: Ctx -> Surface -> TC (Core, ULvl)
inferUniv ctx tm = do
  (c, ty) <- infer ctx tm
  case ty of
    VU l -> return (c, l)
    _ -> err $ "expected a universe but got " ++ show (quote (lvl ctx) ty) ++ ", while checking " ++ show tm 

infer :: Ctx -> Surface -> TC (Core, Val)
infer ctx (SPos p s) = infer (enter p ctx) s
infer ctx (SU l) = return (U l, VU (l + 1))
infer ctx (SVar x) = do
  (i, ty) <- lookupVar ctx x
  return (Var i, ty)
infer ctx c@(SApp f a) = do
  (cf, fty) <- infer ctx f
  case fty of
    VPi x t b -> do
      ca <- check ctx a t
      return (App cf ca, vinst b (eval (vs ctx) ca))
    _ -> err $ "not a pi type in " ++ show c ++ ", got " ++ showV ctx fty
infer ctx (SAbs x (Just t) b) = do
  (ct, _) <- inferUniv ctx t
  let ty = eval (vs ctx) ct
  (cb, rty) <- infer (bind x ty ctx) b
  return (Abs x ct cb, VPi x ty $ closeVal ctx rty)
infer ctx (SPi x t b) = do
  (ct, l1) <- inferUniv ctx t
  let ty = eval (vs ctx) ct
  (cb, l2) <- inferUniv (bind x ty ctx) b
  return (Pi x ct cb, VU (max l1 l2))
infer ctx (SSigma x t b) = do
  (ct, l1) <- inferUniv ctx t
  let ty = eval (vs ctx) ct
  (cb, l2) <- inferUniv (bind x ty ctx) b
  return (Sigma x ct cb, VU (max l1 l2))
infer ctx (SPair a b) = do
  (ta, va) <- infer ctx a
  (tb, vb) <- infer ctx b
  let vt = VSigma "_" va (Fun $ const vb)
  return (Pair ta tb (quote (lvl ctx) vt), vt)
infer ctx c@(SProj t p) = do
  (tm, vt) <- infer ctx t
  case (vt, p) of
    (VSigma x ty c, Fst) -> return (Proj tm p, ty)
    (VSigma x ty c, Snd) -> return (Proj tm p, vinst c $ vproj (eval (vs ctx) tm) Fst)
    _ -> err $ "not a sigma type in " ++ show c ++ ", got " ++ show (quote (lvl ctx) vt)
infer ctx (SLet x t v b) = do
  (cv, ct, ty) <- checkOrInfer ctx v t
  (cb, rty) <- infer (define x ty (eval (vs ctx) cv) ctx) b
  return (Let x ct cv cb, rty)
infer ctx s = err $ "unable to infer " ++ show s

elaborate :: Ctx -> Surface -> TC (Core, Core)
elaborate ctx s = do
  (c, ty) <- infer ctx s
  return (c, quote 0 ty)
