module Verification (verify) where

import Control.Exception (throwIO)
import qualified Data.Set as S

import Core
import Levels
import Val
import Evaluation
import Ctx
import Errors (Error(VerifyError), throwUnless)

check :: Ctx -> Tm -> VTy -> IO ()
check ctx tm ty = do
  let fty = force ty
  case (tm, fty) of
    (Lam x i b, VPi _ i' t c) | i == i' -> check (bind x t ctx) b (vinst c (VVar (lvl ctx)))
    (LamLvl x b, VPiLvl _ c) -> check (bindLevel x ctx) b (vinstLevel c (vFinLevelVar (lvl ctx)))
    (Pair a b, VSigma x ty b') -> do
      check ctx a ty
      check ctx b (vinst b' $ evalCtx ctx a)
    (Let x t v b, _) -> do
      l <- checkTy ctx t
      let vt = evalCtx ctx t
      check ctx v vt
      check (define x vt (evalCtx ctx v) ctx) b ty
    (tm, ty) -> do
      ty' <- infer ctx tm
      throwUnless (conv (lvl ctx) ty' ty) $ VerifyError $ "check failed " ++ show tm ++ " : " ++ showV ctx ty ++ " got " ++ showV ctx ty'

checkTy :: Ctx -> Tm -> IO VLevel
checkTy ctx tm = do
  ty <- infer ctx tm
  case ty of
    VType l -> return l
    ty -> throwIO $ VerifyError $ "expected Type in " ++ show tm ++ " but got " ++ showV ctx ty

checkFinLevel :: Ctx -> FinLevel -> IO ()
checkFinLevel ctx = \case
  l@(FLVar i) ->
    case indexCtx ctx i of
      Just Nothing -> return ()
      Nothing -> throwIO $ VerifyError $ "undefined universe var " ++ show l
      Just (Just _) -> throwIO $ VerifyError $ "universe level variable refers to non-universe value"
  FLZ -> return ()
  FLS l -> checkFinLevel ctx l
  FLMax a b -> checkFinLevel ctx a >> checkFinLevel ctx b

infer :: Ctx -> Tm -> IO VTy
infer ctx = \case
  t@(Var i) ->
    case indexCtx ctx i of
      Just (Just ty) -> return ty
      Nothing -> throwIO $ VerifyError $ "undefined var " ++ show t
      Just Nothing -> throwIO $ VerifyError $ "variable referes to universe level variable: " ++ show t
  Type Omega -> return $ VType VOmega1
  Type (FinLevel l) -> do
    checkFinLevel ctx l
    return $ VType (VFinLevel (vFLS (finLevelCtx ctx l)))
  Pi x i t b -> do
    l1 <- checkTy ctx t
    l2 <- checkTy (bind x (evalCtx ctx t) ctx) b
    return $ VType (l1 <> l2)
  PiLvl x b -> do
    checkTy (bindLevel x ctx) b
    return $ VType VOmega
  Sigma x t b -> do
    l1 <- checkTy ctx t
    l2 <- checkTy (bind x (evalCtx ctx t) ctx) b
    return $ VType (l1 <> l2)
  Let x t v b -> do
    l <- checkTy ctx t
    let vt = evalCtx ctx t
    check ctx v vt
    infer (define x vt (evalCtx ctx v) ctx) b
  LamLvl x b -> do
    rty <- infer (bindLevel x ctx) b
    return $ VPiLvl x (closeLevel ctx rty)
  s@(App f a i) -> do
    ty <- infer ctx f
    case force ty of
      VPi x i' ty c -> do
        throwUnless (i == i') $ VerifyError $ "plicity mismatch in " ++ show s ++ " but got " ++ showV ctx ty
        check ctx a ty
        return $ vinst c (evalCtx ctx a)
      _ -> throwIO $ VerifyError $ "expected a pi in " ++ show s ++ " but got " ++ showV ctx ty
  s@(AppLvl f l) -> do
    ty <- infer ctx f
    case force ty of
      VPiLvl x c -> do
        checkFinLevel ctx l
        return $ vinstLevel c (finLevelCtx ctx l)
      _ -> throwIO $ VerifyError $ "expected a level pi in " ++ show s ++ " but got " ++ showV ctx ty
  s@(Proj t p) -> do
    vt <- infer ctx t
    case (force vt, p) of
      (VSigma x ty c, Fst) -> return ty
      (VSigma x ty c, Snd) -> return $ vinst c (vproj (evalCtx ctx t) Fst)
      (_, PNamed _ i) -> go S.empty (evalCtx ctx t) vt i 0
      _ -> throwIO $ VerifyError $ "verify: not a sigma type in " ++ show s ++ ", got " ++ showV ctx vt
    where
      go xs t ty i j = case (force ty, i) of
        (VSigma _ ty _, 0) -> return ty
        (VSigma x ty c, i) ->
          let name = if x == "_" || S.member x xs then Nothing else Just x in
          go (S.insert x xs) t (vinst c (vproj t (PNamed name j))) (i - 1) (j + 1)
        _ -> throwIO $ VerifyError $ "verify: not a sigma type in " ++ show s ++ ", got " ++ showV ctx ty
  tm -> throwIO $ VerifyError $ "cannot infer: " ++ show tm

verify :: Tm -> IO Tm
verify tm = do
  ty <- infer empty tm
  return $ quote 0 ty
