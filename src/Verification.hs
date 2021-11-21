module Verification (verify) where

import Core
import Ctx
import Val
import Common
import Evaluation
import Globals

check :: Ctx -> Core -> Val -> IO ()
check ctx c ty =
  let fty = force ty in
  case (c, fty) of
    (Abs x b, VPi x' ty b') -> check (bind x ty ctx) b (vinst b' $ vvar (lvl ctx))
    (Pair a b, VSigma x ty b') -> do
      _ <- check ctx a ty
      check ctx b (vinst b' $ eval (vs ctx) a)
    (Let x t v b, _) -> do
      _ <- inferUniv ctx t
      let pty = eval (vs ctx) t
      _ <- check ctx v ty
      check (define x pty (eval (vs ctx) v) ctx) b ty
    (Lift t, VU l) | l > 0 -> check ctx t (VU (l - 1))
    (LiftTerm t, VLift ty) -> check ctx t ty
    (Lower t, ty) -> check ctx t (VLift ty)
    (Con t, x@(VData l d)) -> check ctx t (vel l 0 d x)
    (Refl, VNe (HPrim PHEq _) [EApp y, EApp x, EApp b, EApp a]) -> do
      test (conv (lvl ctx) a b) $ "verify: type mismatch in Refl: " ++ showV ctx ty
      test (conv (lvl ctx) x y) $ "verify: value mismatch in Refl: " ++ showV ctx ty
    (c, _) -> do
      ty' <- infer ctx c
      test (conv (lvl ctx) ty' ty) $ "verify: check failed " ++ show c ++ " : " ++ showV ctx ty ++ ", got " ++ showV ctx ty'

inferUniv :: Ctx -> Core -> IO ULvl
inferUniv ctx tm = do
  ty <- infer ctx tm
  case force ty of
    VU l -> return l
    _ -> error $ "verify: expected a universe but got " ++ showV ctx ty ++ ", while checking " ++ show tm 

infer :: Ctx -> Core -> IO Val
infer ctx (U l) = return $ VU (l + 1)
infer ctx c@(Var i) = indexCtx ctx i
infer ctx (Global x l) = do
  e <- lookupGlobal x
  let vt = if l == 0 then gvtype e else eval [] (liftUniv l (gtype e))
  return vt
infer ctx c@(Prim x l) = return $ primType x l
infer ctx (PrimElim x l k) = return $ primElimType x l k
infer ctx (Pi x t b) = do
  l1 <- inferUniv ctx t
  l2 <- inferUniv (bind x (eval (vs ctx) t) ctx) b
  return $ VU (max l1 l2)
infer ctx (Sigma x t b) = do
  l1 <- inferUniv ctx t
  l2 <- inferUniv (bind x (eval (vs ctx) t) ctx) b
  return $ VU (max l1 l2)
infer ctx c@(App f a) = do
  fty <- infer ctx f
  case force fty of
    VPi x t b -> do
      check ctx a t
      return $ vinst b (eval (vs ctx) a)
    _ -> error $ "not a pi type in " ++ show c ++ ", got " ++ showV ctx fty
infer ctx c@(Proj t p) = do
  vt <- infer ctx t
  case (force vt, p) of
    (VSigma x ty c, Fst) -> return ty
    (VSigma x ty c, Snd) -> return $ vinst c (vproj (eval (vs ctx) t) Fst)
    _ -> error $ "not a sigma type in " ++ show c ++ ", got " ++ showV ctx vt
infer ctx (Let x t v b) = do
  inferUniv ctx t
  let ty = eval (vs ctx) t
  check ctx v ty
  infer (define x ty (eval (vs ctx) v) ctx) b
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
    _ -> error $ "expected lift type in " ++ show tm ++ " but got " ++ showV ctx ty
infer ctx tm = error $ "verify: cannot infer: " ++ show tm

verify :: Core -> IO Core
verify c = do
  ty <- infer empty c
  return $ quote 0 ty
