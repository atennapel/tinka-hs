module Verification (verify) where

import Core
import Ctx
import Val
import Common
import Evaluation
import Globals
import Universes

import qualified Data.Set as S

-- import Debug.Trace (trace)

check :: Ctx -> Core -> Val -> IO ()
check ctx c ty =
  let fty = force ty in
  case (c, fty) of
    (Abs x i b, VPi x' i' ty u b' _) | i == i' -> check (bind x i ty u ctx) b (vinst b' $ vvar (lvl ctx))
    (Pair a b, VSigma x ty _ b' _) -> do
      _ <- check ctx a ty
      check ctx b (vinst b' $ eval (vs ctx) a)
    (Let x t v b, _) -> do
      u <- inferUniv ctx t
      let pty = eval (vs ctx) t
      _ <- check ctx v ty
      check (define x t pty (UConst u) v (eval (vs ctx) v) ctx) b ty
    (Lift t, VU (UConst l)) | l > 0 -> check ctx t (VU (UConst $ l - 1))
    (LiftTerm t, VLift ty) -> check ctx t ty
    (Lower t, ty) -> check ctx t (VLift ty)
    (Con t, x@(VData l d)) -> check ctx t (vel l 0 d x)
    (Refl, VNe (HPrim PHEq _) [EApp y Expl, EApp x Expl, EApp b Expl, EApp a Expl]) -> do
      test (conv (lvl ctx) a b) $ "verify: type mismatch in Refl: " ++ showV ctx ty
      test (conv (lvl ctx) x y) $ "verify: value mismatch in Refl: " ++ showV ctx ty
    (c, _) -> do
      ty' <- infer ctx c
      test (conv (lvl ctx) ty' ty) $ "verify: check failed " ++ show c ++ " : " ++ showV ctx ty ++ ", got " ++ showV ctx ty'

inferUniv :: Ctx -> Core -> IO ULvl
inferUniv ctx tm = do
  ty <- infer ctx tm
  case force ty of
    VU (UConst l) -> return l
    _ -> error $ "verify: expected a universe but got " ++ showV ctx ty ++ ", while checking " ++ show tm 

infer :: Ctx -> Core -> IO Val
infer ctx (U (UConst l)) = return $ VU (UConst $ l + 1)
infer ctx c@(Var i) = indexCtx ctx i
infer ctx (Global x l) = do
  e <- lookupGlobal x
  let vt = if l == 0 then gvtype e else eval [] (liftUniv l (gtype e))
  return vt
infer ctx c@(Prim x l) = return $ fst $ primType x l
infer ctx (PrimElim x l k) = return $ fst $ primElimType x l k
infer ctx (Pi x i t _ b _) = do
  l1 <- inferUniv ctx t
  l2 <- inferUniv (bind x i (eval (vs ctx) t) (UConst l1) ctx) b
  return $ VU (UConst $ max l1 l2)
infer ctx (Sigma x t _ b _) = do
  l1 <- inferUniv ctx t
  l2 <- inferUniv (bind x Expl (eval (vs ctx) t) (UConst l1) ctx) b
  return $ VU (UConst $ max l1 l2)
infer ctx c@(App f a i) = do
  fty <- infer ctx f
  case force fty of
    VPi x i' t _ b _ -> do
      test (i == i') $ "verify: plicity mismatch in " ++ show c ++ ", got " ++ showV ctx fty
      check ctx a t
      return $ vinst b (eval (vs ctx) a)
    _ -> error $ "verify: not a pi type in " ++ show c ++ ", got " ++ showV ctx fty
infer ctx c@(Proj t p) = do
  vt <- infer ctx t
  case (force vt, p) of
    (VSigma x ty _ c _, Fst) -> return ty
    (VSigma x ty _ c _, Snd) -> return $ vinst c (vproj (eval (vs ctx) t) Fst)
    (_, PNamed _ i) -> go S.empty (eval (vs ctx) t) vt i 0
    _ -> error $ "verify: not a sigma type in " ++ show c ++ ", got " ++ showV ctx vt
  where
    go xs t ty i j = case (force ty, i) of
      (VSigma _ ty _ _ _, 0) -> return ty
      (VSigma x ty _ c _, i) ->
        let name = if x == "_" || S.member x xs then Nothing else Just x in
        go (S.insert x xs) t (vinst c (vproj t (PNamed name j))) (i - 1) (j + 1)
      _ -> error $ "verify: not a sigma type in " ++ show c ++ ", got " ++ showV ctx ty
infer ctx (Let x t v b) = do
  u <- inferUniv ctx t
  let ty = eval (vs ctx) t
  check ctx v ty
  infer (define x t ty (UConst u) v (eval (vs ctx) v) ctx) b
infer ctx (Lift t) = do
  l <- inferUniv ctx t
  return $ VU (UConst $ l + 1)
infer ctx (LiftTerm t) = do
  ty <- infer ctx t
  return $ VLift ty
infer ctx tm@(Lower t) = do
  ty <- infer ctx t
  case force ty of
    VLift ty' -> return ty'
    _ -> error $ "verify: expected lift type in " ++ show tm ++ " but got " ++ showV ctx ty
infer ctx tm = error $ "verify: cannot infer: " ++ show tm 

verify :: Core -> IO Core
verify c = do
  print c
  ty <- infer empty c
  return $ quote 0 ty
