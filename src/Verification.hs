module Verification (verify) where

import Control.Exception (throwIO)
import qualified Data.Set as S

import Common
import Core
import Levels
import Val
import Evaluation
import Ctx
import Errors (Error(VerifyError), throwUnless)
import Globals

check :: Ctx -> Tm -> VTy -> IO ()
check ctx tm ty = do
  debug $ "verify: check " ++ show tm ++ " : " ++ showV ctx ty
  let fty = force ty
  case (tm, fty) of
    (Lam x i b, VPi _ i' t u1 c _) | i == i' -> check (bind x i t u1 ctx) b (vinst c (VVar (lvl ctx)))
    (LamLvl x b, VPiLvl _ c _) -> check (bindLevel x ctx) b (vinstLevel c (vFinLevelVar (lvl ctx)))
    (Pair a b, VSigma x ty _ b' _) -> do
      check ctx a ty
      check ctx b (vinst b' $ evalCtx ctx a)
    (Let x inst t v b, _) -> do
      l <- checkTy ctx t
      let vt = evalCtx ctx t
      check ctx v vt
      check (define x inst vt l (evalCtx ctx v) ctx) b ty
    (tm, ty) -> do
      ty' <- infer ctx tm
      debug $ "verify: unify " ++ showV ctx ty' ++ " ~ " ++ showV ctx ty
      throwUnless (conv (lvl ctx) ty' ty) $ VerifyError $ "check failed " ++ show tm ++ " : " ++ showV ctx ty ++ " got " ++ showV ctx ty'

checkTy :: Ctx -> Tm -> IO VLevel
checkTy ctx tm = do
  debug $ "verify: checkTy " ++ show tm
  ty <- infer ctx tm
  case ty of
    VType l -> return l
    ty -> throwIO $ VerifyError $ "expected Type in " ++ show tm ++ " but got " ++ showV ctx ty

checkFinLevel :: Ctx -> FinLevel -> IO ()
checkFinLevel ctx tm = do
  debug $ "verify: checkFinLevel " ++ show tm
  case tm of
    l@(FLVar i) ->
      case indexCtx ctx i of
        Just Nothing -> return ()
        Nothing -> throwIO $ VerifyError $ "undefined universe var " ++ show l
        Just (Just _) -> throwIO $ VerifyError $ "universe level variable refers to non-universe value"
    FLZ -> return ()
    FLS l -> checkFinLevel ctx l
    FLMax a b -> checkFinLevel ctx a >> checkFinLevel ctx b
    FLMeta m -> throwIO $ VerifyError $ "meta found ?l" ++ show m

infer :: Ctx -> Tm -> IO VTy
infer ctx tm = do
  debug $ "verify: infer " ++ show tm
  case tm of
    t@(Var i) ->
      case indexCtx ctx i of
        Just (Just ty) -> return $ fst ty
        Nothing -> throwIO $ VerifyError $ "undefined var " ++ show t
        Just Nothing -> throwIO $ VerifyError $ "variable referes to universe level variable: " ++ show t
    t@(Global x) ->
      case getGlobal x of
        Just e -> return $ gTy e
        Nothing -> throwIO $ VerifyError $ "undefined global " ++ show t
    Prim (Left x) -> return $ fst $ primType x
    Prim (Right x) -> return $ fst $ primElimType x
    Type Omega -> return $ VType VOmega1
    Type (FinLevel l) -> do
      checkFinLevel ctx l
      return $ VType (VFinLevel (vFLS (finLevelCtx ctx l)))
    Pi x i t _ b _ -> do
      l1 <- checkTy ctx t
      let vt = evalCtx ctx t
      l2 <- checkTy (bind x i vt l1 ctx) b
      return $ VType (l1 <> l2)
    PiLvl x b _ -> do
      checkTy (bindLevel x ctx) b
      return $ VType VOmega
    Sigma x t _ b _ -> do
      l1 <- checkTy ctx t
      l2 <- checkTy (bind x Expl (evalCtx ctx t) l1 ctx) b
      return $ VType (l1 <> l2)
    Let x inst t v b -> do
      l <- checkTy ctx t
      let vt = evalCtx ctx t
      check ctx v vt
      let vv = evalCtx ctx v
      infer (define x inst vt l vv ctx) b
    s@(App f a i) -> do
      ty <- infer ctx f
      case force ty of
        VPi x i' ty _ c _ -> do
          throwUnless (i == i') $ VerifyError $ "plicity mismatch in " ++ show s ++ " but got " ++ showV ctx ty
          check ctx a ty
          let va = evalCtx ctx a
          return $ vinst c va
        _ -> throwIO $ VerifyError $ "expected a pi in " ++ show s ++ " but got " ++ showV ctx ty
    s@(AppLvl f l) -> do
      ty <- infer ctx f
      case force ty of
        VPiLvl x c _ -> do
          checkFinLevel ctx l
          let vl = finLevelCtx ctx l
          return $ vinstLevel c vl
        _ -> throwIO $ VerifyError $ "expected a level pi in " ++ show s ++ " but got " ++ showV ctx ty
    s@(Proj t p) -> do
      vt <- infer ctx t
      case (force vt, p) of
        (VSigma x ty _ c _, Fst) -> return ty
        (VSigma x ty _ c _, Snd) -> return $ vinst c (vproj (evalCtx ctx t) Fst)
        (_, PNamed _ i) -> go S.empty (evalCtx ctx t) vt i 0
        _ -> throwIO $ VerifyError $ "not a sigma type in " ++ show s ++ ", got " ++ showV ctx vt
      where
        go xs t ty i j = case (force ty, i) of
          (VSigma _ ty _ _ _, 0) -> return ty
          (VSigma x ty _ c _, i) ->
            let name = if x == "_" || S.member x xs then Nothing else Just x in
            go (S.insert x xs) t (vinst c (vproj t (PNamed name j))) (i - 1) (j + 1)
          _ -> throwIO $ VerifyError $ "not a sigma type in " ++ show s ++ ", got " ++ showV ctx ty
    tm -> throwIO $ VerifyError $ "cannot infer: " ++ show tm

verify :: Ctx -> Tm -> IO Tm
verify ctx tm = do
  debug $ "verify " ++ show tm
  ty <- infer ctx tm
  return $ quoteCtx ctx ty
