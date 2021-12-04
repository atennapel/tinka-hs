module Elaboration (elaborate) where

import Control.Exception (throwIO)

import Core
import Levels
import Val
import Evaluation
import Ctx
import Errors (Error(ElaborateError), throwUnless)
import Surface

check :: Ctx -> STm -> VTy -> IO Tm
check ctx tm ty = do
  putStrLn $ "check " ++ show tm ++ " : " ++ showV ctx ty
  case (tm, ty) of
    (SPos p tm, ty) -> check (enter p ctx) tm ty
    (SLam x b, VPi _ t c) ->
      Lam x <$> check (bind x t ctx) b (vinst c (VVar (lvl ctx)))
    (SLamLvl x b, VPiLvl _ c) ->
      LamLvl x <$> check (bindLevel x ctx) b (vinstLevel c (vFinLevelVar (lvl ctx)))
    (SLet x t v b, ty) -> do
      (ct, l) <- checkTy ctx t
      let vt = evalCtx ctx ct
      cv <- check ctx v vt
      cb <- check (define x vt (evalCtx ctx cv) ctx) b ty
      return $ Let x ct cv cb
    (tm, ty) -> do
      (ctm, ty') <- infer ctx tm
      throwUnless (conv (lvl ctx) ty' ty) $ ElaborateError $ "check failed " ++ show tm ++ " : " ++ showV ctx ty ++ " got " ++ showV ctx ty'
      return ctm

checkTy :: Ctx -> STm -> IO (Tm, VLevel)
checkTy ctx tm = do
  (ctm, ty) <- infer ctx tm
  case ty of
    VType l -> return (ctm, l)
    ty -> throwIO $ ElaborateError $ "expected Type in " ++ show tm ++ " but got " ++ showV ctx ty

checkFinLevel :: Ctx -> SLevel -> IO FinLevel
checkFinLevel ctx = \case
  l@(SLVar x) ->
    case lookupCtx ctx x of
      Just (i, Nothing) -> return $ FLVar i
      Nothing -> throwIO $ ElaborateError $ "undefined universe var " ++ show l
      Just (_, Just _) -> throwIO $ ElaborateError $ "universe level variable refers to non-universe value"
  SLZ -> return FLZ
  SLS l -> FLS <$> checkFinLevel ctx l
  SLMax a b -> FLMax <$> checkFinLevel ctx a <*> checkFinLevel ctx b

infer :: Ctx -> STm -> IO (Tm, VTy)
infer ctx tm = do
  putStrLn $ "infer " ++ show tm
  case tm of
    SPos p t -> infer (enter p ctx) t
    t@(SVar x) ->
      case lookupCtx ctx x of
        Just (i, Just ty) -> do
          putStrLn $ show t ++ " : " ++ showV ctx ty ++ " ~> '" ++ show i
          return (Var i, ty)
        Nothing -> throwIO $ ElaborateError $ "undefined var " ++ show t
        Just (_, Nothing) -> throwIO $ ElaborateError $ "variable referes to universe level variable: " ++ show t
    SType l -> do
      l' <- checkFinLevel ctx l
      return (Type (FinLevel l'), VType (VFinLevel (vFLS (finLevelCtx ctx l'))))
    SPi x t b -> do
      (ct, l1) <- checkTy ctx t
      (cb, l2) <- checkTy (bind x (evalCtx ctx ct) ctx) b
      return (Pi x ct cb, VType (l1 <> l2))
    SPiLvl x b -> do
      (cb, _) <- checkTy (bindLevel x ctx) b
      return (PiLvl x cb, VType VOmega)
    SLet x t v b -> do
      (ct, l) <- checkTy ctx t
      let vt = evalCtx ctx ct
      cv <- check ctx v vt
      putStrLn $ "got here: " ++ show cv
      (cb, ty) <- infer (define x vt (evalCtx ctx cv) ctx) b
      return (Let x ct cv cb, ty)
    c@(SApp f a) -> do
      (cf, fty) <- infer ctx f
      case fty of
        VPi x ty c -> do
          ca <- check ctx a ty
          return (App cf ca, vinst c (evalCtx ctx ca))
        ty -> throwIO $ ElaborateError $ "expected a pi in " ++ show c ++ " but got " ++ showV ctx ty
    c@(SAppLvl f l) -> do
      (cf, fty) <- infer ctx f
      case fty of
        VPiLvl x c -> do
          l' <- checkFinLevel ctx l
          return (AppLvl cf l', vinstLevel c (finLevelCtx ctx l'))
        ty -> throwIO $ ElaborateError $ "expected a level pi in " ++ show c ++ " but got " ++ showV ctx ty
    tm -> throwIO $ ElaborateError $ "cannot infer: " ++ show tm

elaborate :: Ctx -> STm -> IO (Tm, Ty)
elaborate ctx tm = do
  (tm, vty) <- infer ctx tm
  return (tm, quote (lvl ctx) vty)
