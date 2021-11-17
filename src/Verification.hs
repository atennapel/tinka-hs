module Verification (verify) where

import Control.Monad.Trans.Reader (ask)

import Core
import Ctx
import Val
import Common

check :: Ctx -> Core -> Val -> TC ()
check ctx c ty =
  let fty = force ty in
  case (c, fty) of
    (Abs x b, VPi x' ty b') -> do
      gs <- ask
      check (bind x ty ctx) b (vinst gs b' $ vvar (lvl ctx))
    (Pair a b, VSigma x ty b') -> do
      _ <- check ctx a ty
      gs <- ask
      check ctx b (vinst gs b' $ eval gs (vs ctx) a)
    (Let x t v b, _) -> do
      _ <- inferUniv ctx t
      gs <- ask
      let pty = eval gs (vs ctx) t
      _ <- check ctx v ty
      gs <- ask
      check (define x pty (eval gs (vs ctx) v) ctx) b ty
    (Lift t, VU l) | l > 0 -> check ctx t (VU (l - 1))
    (LiftTerm t, VLift ty) -> check ctx t ty
    (Lower t, ty) -> check ctx t (VLift ty)
    (c, _) -> do
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
infer ctx c@(Prim x l) = do
  gs <- ask
  return $ primType gs x l
infer ctx (PrimElim x l k) = do
  gs <- ask
  return $ primElimType gs x l k
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
infer ctx c@(App f a) = do
  fty <- infer ctx f
  gs <- ask
  case force fty of
    VPi x t b -> do
      check ctx a t
      return $ vinst gs b (eval gs (vs ctx) a)
    _ -> err $ "not a pi type in " ++ show c ++ ", got " ++ showV gs ctx fty
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
infer ctx (Lift t) = do
  l <- inferUniv ctx t
  return $ VU (l + 1)
infer ctx (LiftTerm t) = do
  ty <- infer ctx t
  return $ VLift ty
infer ctx tm@(Lower t) = do
  ty <- infer ctx t
  case force ty of
    VLift ty' -> return ty'
    _ -> do
      gs <- ask
      err $ "expected lift type in " ++ show tm ++ " but got " ++ showV gs ctx ty
infer ctx tm = err $ "verify: cannot infer: " ++ show tm

verify :: Core -> TC Core
verify c = do
  gs <- ask
  ty <- infer empty c
  return $ quote gs 0 ty
