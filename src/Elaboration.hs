module Elaboration (elaborate) where

import Ctx
import Surface
import Core
import Val

checkOrInfer :: Ctx -> Surface -> Maybe Surface -> TC (Core, Core, Val)
checkOrInfer ctx v Nothing = do
  (cv, ty) <- infer ctx v
  return (cv, quote (lvl ctx) ty, ty)
checkOrInfer ctx v (Just t) = do
  ct <- check ctx t VU
  let ty = eval (vs ctx) ct
  cv <- check ctx v ty
  return (cv, ct, ty)

check :: Ctx -> Surface -> Val -> TC Core
check ctx (SAbs x Nothing b) (VPi x' ty b') = do
  cb <- check (bind x ty ctx) b (vinst b' $ vvar (lvl ctx))
  return $ Abs x (quote (lvl ctx) ty) cb
check ctx (SLet x t v b) rty = do
  (cv, ct, ty) <- checkOrInfer ctx v t
  cb <- check (define x ty (eval (vs ctx) cv) ctx) b rty
  return $ Let x ct cv cb
check ctx s ty = do
  (c, ty') <- infer ctx s
  test (conv (lvl ctx) ty' ty) $ "check failed " ++ show s ++ " : " ++ showV ctx ty ++ ", got " ++ showV ctx ty'
  return c

infer :: Ctx -> Surface -> TC (Core, Val)
infer ctx SU = return (U, VU) -- type-in-type
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
  ct <- check ctx t VU
  let ty = eval (vs ctx) ct
  (cb, rty) <- infer (bind x ty ctx) b
  return (Abs x ct cb, VPi x ty $ closeVal ctx rty)
infer ctx (SPi x t b) = do
  ct <- check ctx t VU
  let ty = eval (vs ctx) ct
  cb <- check (bind x ty ctx) b VU
  return (Pi x ct cb, VU)
infer ctx (SLet x t v b) = do
  (cv, ct, ty) <- checkOrInfer ctx v t
  (cb, rty) <- infer (define x ty (eval (vs ctx) cv) ctx) b
  return (Let x ct cv cb, rty)
infer ctx s = err $ "unable to infer " ++ show s

elaborate :: Surface -> TC (Core, Core)
elaborate s = do
  (c, ty) <- infer empty s
  return (c, quote 0 ty)
