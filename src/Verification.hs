module Verification (verify) where

import Core
import Ctx
import Val
import Common

check :: Ctx -> Core -> Val -> TC ()
check ctx c ty = do
  ty' <- infer ctx c
  test (conv (lvl ctx) ty' ty) $ "check failed " ++ show c ++ " : " ++ show (quote (lvl ctx) ty) ++ ", got " ++ show (quote (lvl ctx) ty')

infer :: Ctx -> Core -> TC Val
infer ctx U = return VU
infer ctx c@(Var i) =
  let
    go [] i = err $ "undefined var " ++ show c
    go (ty : _) 0 = return ty
    go (_ : tl) n = go tl (n - 1)
  in go (ts ctx) i
infer ctx (Pi x t b) = do
  check ctx t VU
  check (bind x (eval (vs ctx) t) ctx) b VU
  return VU
infer ctx (Sigma x t b) = do
  check ctx t VU
  check (bind x (eval (vs ctx) t) ctx) b VU
  return VU
infer ctx (Abs x t b) = do
  check ctx t VU
  let ty = eval (vs ctx) t
  rty <- infer (bind x ty ctx) b
  return $ VPi x ty (closeVal ctx rty)
infer ctx c@(App f a) = do
  fty <- infer ctx f
  case fty of
    VPi x t b -> do
      check ctx a t
      return $ vinst b (eval (vs ctx) a)
    _ -> err $ "not a pi type in " ++ show c ++ ", got " ++ show (quote (lvl ctx) fty)
infer ctx c@(Pair a b t) = do
  check ctx t VU
  let vt = eval (vs ctx) t
  case vt of
    VSigma x ty c -> do
      check ctx a ty
      check ctx b (vinst c $ eval (vs ctx) a)
      return vt
    _ -> err $ "not a sigma type in " ++ show c
infer ctx c@(Proj t p) = do
  vt <- infer ctx t
  case (vt, p) of
    (VSigma x ty c, Fst) -> return ty
    (VSigma x ty c, Snd) -> return $ vinst c (vproj (eval (vs ctx) t) Fst)
    _ -> err $ "not a sigma type in " ++ show c ++ ", got " ++ show (quote (lvl ctx) vt)
infer ctx (Let x t v b) = do
  check ctx t VU
  let ty = eval (vs ctx) t
  check ctx v ty
  infer (define x ty (eval (vs ctx) v) ctx) b

verify :: Core -> TC Core
verify = fmap (quote 0) . infer empty
