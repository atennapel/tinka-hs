module Verification (verify) where

import Control.Exception (throwIO)

import Core
import Levels
import Val
import Evaluation
import Ctx
import Errors (Error(VerifyError), throwUnless)

check :: Ctx -> Tm -> VTy -> IO ()
check ctx tm ty = case (tm, ty) of
  (Lam x b, VPi _ t c) -> check (bind x t ctx) b (vinst c (VVar (lvl ctx)))
  (LamLvl x b, VPiLvl _ c) -> check (bindLevel x ctx) b (vinstLevel c (vFinLevelVar (lvl ctx)))
  (Let x t v b, ty) -> do
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
  Pi x t b -> do
    l1 <- checkTy ctx t
    l2 <- checkTy (bind x (evalCtx ctx t) ctx) b
    return $ VType (l1 <> l2)
  PiLvl x b -> do
    checkTy (bindLevel x ctx) b
    return $ VType VOmega
  Let x t v b -> do
    l <- checkTy ctx t
    let vt = evalCtx ctx t
    check ctx v vt
    infer (define x vt (evalCtx ctx v) ctx) b
  c@(App f a) -> do
    fty <- infer ctx f
    case fty of
      VPi x ty c -> do
        check ctx a ty
        return $ vinst c (evalCtx ctx a)
      ty -> throwIO $ VerifyError $ "expected a pi in " ++ show c ++ " but got " ++ showV ctx ty
  c@(AppLvl f l) -> do
    fty <- infer ctx f
    case fty of
      VPiLvl x c -> do
        checkFinLevel ctx l
        return $ vinstLevel c (finLevelCtx ctx l)
      ty -> throwIO $ VerifyError $ "expected a level pi in " ++ show c ++ " but got " ++ showV ctx ty
  tm -> throwIO $ VerifyError $ "cannot infer: " ++ show tm

verify :: Tm -> IO Tm
verify tm = do
  ty <- infer empty tm
  return $ quote 0 ty
