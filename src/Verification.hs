module Verification (verify) where

import Control.Monad.Trans.Reader (ask)

import Core
import Ctx
import Val
import Common

check :: Ctx -> Core -> Val -> TC ()
check ctx c ty = do
  ty' <- infer ctx c
  gs <- ask
  test (conv gs (lvl ctx) ty' ty) $ "check failed " ++ show c ++ " : " ++ showV gs ctx ty ++ ", got " ++ showV gs ctx ty'

inferUniv :: Ctx -> Core -> TC ULvl
inferUniv ctx tm = do
  ty <- infer ctx tm
  gs <- ask
  case force ty of
    VU l -> return l
    _ -> err $ "expected a universe but got " ++ showV gs ctx ty ++ ", while checking " ++ show tm 

infer :: Ctx -> Core -> TC Val
infer ctx (U l) = return $ VU (l + 1)
infer ctx c@(Var i) = indexCtx ctx i
infer ctx (Global x l) = do
  e <- lookupGlobal x
  gs <- ask
  let vt = if l == 0 then gvtype e else eval gs [] (liftUniv l (gtype e))
  return vt
infer ctx (Pi x t b) = do
  l1 <- inferUniv ctx t
  gs <- ask
  l2 <- inferUniv (bind x (eval gs (vs ctx) t) ctx) b
  return $ VU (max l1 l2)
infer ctx (Sigma x t b) = do
  l1 <- inferUniv ctx t
  gs <- ask
  l2 <- inferUniv (bind x (eval gs (vs ctx) t) ctx) b
  return $ VU (max l1 l2)
infer ctx (Abs x t b) = do
  inferUniv ctx t
  gs <- ask
  let ty = eval gs (vs ctx) t
  rty <- infer (bind x ty ctx) b
  return $ VPi x ty (closeVal gs ctx rty)
infer ctx c@(App f a) = do
  fty <- infer ctx f
  gs <- ask
  case force fty of
    VPi x t b -> do
      check ctx a t
      return $ vinst gs b (eval gs (vs ctx) a)
    _ -> err $ "not a pi type in " ++ show c ++ ", got " ++ showV gs ctx fty
infer ctx c@(Pair a b t) = do
  inferUniv ctx t
  gs <- ask
  let vt = eval gs (vs ctx) t
  case force vt of
    VSigma x ty c -> do
      check ctx a ty
      check ctx b (vinst gs c $ eval gs (vs ctx) a)
      return vt
    _ -> err $ "not a sigma type in " ++ show c
infer ctx c@(Proj t p) = do
  vt <- infer ctx t
  gs <- ask
  case (force vt, p) of
    (VSigma x ty c, Fst) -> return ty
    (VSigma x ty c, Snd) -> return $ vinst gs c (vproj (eval gs (vs ctx) t) Fst)
    _ -> err $ "not a sigma type in " ++ show c ++ ", got " ++ showV gs ctx vt
infer ctx (Let x t v b) = do
  inferUniv ctx t
  gs <- ask
  let ty = eval gs (vs ctx) t
  check ctx v ty
  infer (define x ty (eval gs (vs ctx) v) ctx) b

verify :: Core -> TC Core
verify c = do
  gs <- ask
  ty <- infer empty c
  return $ quote gs 0 ty
