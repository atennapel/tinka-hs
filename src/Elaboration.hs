module Elaboration (elaborate) where

import Control.Exception (throwIO)
import Data.Bifunctor (first)
import qualified Data.Set as S

import Common
import Core
import Levels
import Val
import Evaluation
import Ctx
import Errors (Error(ElaborateError), throwUnless)
import Surface
import Prims

checkOrInfer :: Ctx -> STm -> Maybe STm -> IO (Tm, Tm, Val)
checkOrInfer ctx v Nothing = do
  (cv, ty) <- infer ctx v
  return (cv, quoteCtx ctx ty, ty)
checkOrInfer ctx v (Just t) = do
  (ct, u) <- checkTy ctx t
  let ty = evalCtx ctx ct
  cv <- check ctx v ty
  return (cv, ct, ty)

check :: Ctx -> STm -> VTy -> IO Tm
check ctx tm ty = do
  let fty = force ty
  -- putStrLn $ "check " ++ show tm ++ " : " ++ showV ctx ty
  case (tm, fty) of
    (SPos p tm, _) -> check (enter p ctx) tm ty
    (SLam x i ma b, VPi x' i' ty b') | either (\x -> x == x' && i' == Impl) (== i') i -> do
      case ma of
        Nothing -> return ()
        Just a -> do
          (ca, u') <- checkTy ctx a
          throwUnless (conv (lvl ctx) (evalCtx ctx ca) ty) $ ElaborateError $ "check failed " ++ show tm ++ " : " ++ showV ctx ty ++ " got " ++ showC ctx ca
      cb <- check (bind x ty ctx) b (vinst b' (VVar (lvl ctx)))
      return $ Lam x i' cb
    (t, VPi x Impl a b) -> do
      Lam x Impl <$> check (bindInsert x a ctx) t (vinst b (VVar (lvl ctx)))
    (SLamLvl x b, VPiLvl _ c) ->
      LamLvl x <$> check (bindLevel x ctx) b (vinstLevel c (vFinLevelVar (lvl ctx)))
    (t, VPiLvl x c) ->
      LamLvl x <$> check (bindLevelInsert x ctx) t (vinstLevel c (vFinLevelVar (lvl ctx)))
    (SPair a b, VSigma x ty b') -> do
      ta <- check ctx a ty
      tb <- check ctx b (vinst b' (evalCtx ctx ta))
      return $ Pair ta tb
    (SLet x mt v b, _) -> do
      (cv, ct, vt) <- checkOrInfer ctx v mt
      cb <- check (define x vt (evalCtx ctx cv) ctx) b ty
      return $ Let x ct cv cb
    (tm, ty) -> do
      (ctm, ty') <- infer ctx tm
      throwUnless (conv (lvl ctx) ty' ty) $ ElaborateError $ "check failed " ++ show tm ++ " : " ++ showV ctx ty ++ " got " ++ showV ctx ty'
      return ctm

checkTy :: Ctx -> STm -> IO (Tm, VLevel)
checkTy ctx tm = do
  (ctm, ty) <- infer ctx tm
  case force ty of
    VType l -> return (ctm, l)
    _ -> throwIO $ ElaborateError $ "expected Type in " ++ show tm ++ " but got " ++ showV ctx ty

checkFinLevel :: Ctx -> SLevel -> IO FinLevel
checkFinLevel ctx = \case
  l@(SLVar x) ->
    case lookupCtx ctx x of
      Just (i, Nothing) -> return $ FLVar i
      Nothing -> throwIO $ ElaborateError $ "undefined universe var " ++ show l
      Just (_, Just _) -> throwIO $ ElaborateError $ "universe level variable refers to non-universe value"
  SLS l -> FLS <$> checkFinLevel ctx l
  SLMax a b -> FLMax <$> checkFinLevel ctx a <*> checkFinLevel ctx b
  SLNat i -> return $ addToFinLevel i FLZ

infer :: Ctx -> STm -> IO (Tm, VTy)
infer ctx tm = do
  -- putStrLn $ "infer " ++ show tm
  case tm of
    SPos p t -> infer (enter p ctx) t
    t@(SVar x) ->
      case toPrimName x of
        Just prim -> return (Prim (Left prim), primType prim)
        Nothing ->
          case toPrimElimName x of
            Just prim -> return (Prim (Right prim), primElimType prim)
            Nothing -> do
              case lookupCtx ctx x of
                Just (i, Just ty) -> do
                  -- putStrLn $ show t ++ " : " ++ showV ctx ty ++ " ~> '" ++ show i
                  return (Var i, ty)
                Nothing -> throwIO $ ElaborateError $ "undefined var " ++ show t
                Just (_, Nothing) -> throwIO $ ElaborateError $ "variable referes to universe level variable: " ++ show t
    SType l -> do
      l' <- checkFinLevel ctx l
      return (Type (FinLevel l'), VType (VFinLevel (vFLS (finLevelCtx ctx l'))))
    SPi x i t b -> do
      (ct, l1) <- checkTy ctx t
      (cb, l2) <- checkTy (bind x (evalCtx ctx ct) ctx) b
      return (Pi x i ct cb, VType (l1 <> l2))
    SSigma x t b -> do
      (ct, l1) <- checkTy ctx t
      (cb, l2) <- checkTy (bind x (evalCtx ctx ct) ctx) b
      return (Sigma x ct cb, VType (l1 <> l2))
    SPiLvl x b -> do
      (cb, _) <- checkTy (bindLevel x ctx) b
      return (PiLvl x cb, VType VOmega)
    SLet x mt v b -> do
      (cv, ct, vt) <- checkOrInfer ctx v mt
      (cb, ty) <- infer (define x vt (evalCtx ctx cv) ctx) b
      return (Let x ct cv cb, ty)
    SPair a b -> do
      (ta, va) <- infer ctx a
      (tb, vb) <- infer ctx b
      let vt = VSigma "_" va (Fun $ const vb)
      return (Let "p" (quoteCtx ctx vt) (Pair ta tb) (Var 0), vt)
    c@(SApp f a (Right i)) -> do
      (i, cf, tty) <- case i of
        Impl -> do
          (t, tty) <- infer ctx f
          return (Impl, t, tty)
        Expl -> do
          (t, tty) <- infer ctx f
          return (Expl, t, tty)
      (pt, rt) <- case force tty of
        VPi x i' a b -> do
          throwUnless (i == i') $ ElaborateError $ "app icit mismatch in " ++ show c ++ ": " ++ showV ctx tty
          return (a, b)
        _ -> throwIO $ ElaborateError $ "pi expected in " ++ show c ++ " but got " ++ showV ctx tty
      ca <- check ctx a pt
      return (App cf ca i, vinst rt (evalCtx ctx ca))
    c@(SAppLvl f l) -> do
      (cf, fty) <- infer ctx f
      let ffty = force fty
      case ffty of
        VPiLvl x c -> do
          l' <- checkFinLevel ctx l
          return (AppLvl cf l', vinstLevel c (finLevelCtx ctx l'))
        _ -> throwIO $ ElaborateError $ "expected a level pi in " ++ show c ++ " but got " ++ showV ctx fty
    s@(SLam x (Right i) ma b) -> do
      (a, u1) <- first (evalCtx ctx) <$> case ma of
        Just a -> checkTy ctx a
        Nothing -> throwIO $ ElaborateError $ "cannot infer unannotated lambda: " ++ show s
      (cb, rty) <- infer (bind x a ctx) b
      let vt = VPi x i a (closeVal ctx rty)
      return (Let "f" (quoteCtx ctx vt) (Lam x i cb) (Var 0), vt)
    SLamLvl x b -> do
      (cb, rty) <- infer (bindLevel x ctx) b
      let vt = VPiLvl x (closeLevel ctx rty)
      return (Let "f" (quoteCtx ctx vt) (LamLvl x cb) (Var 0), vt)
    c@(SProj t p) -> do
      (tm, vt) <- infer ctx t
      case (force vt, p) of
        (VSigma x ty c, SFst) -> return (Proj tm Fst, ty)
        (VSigma x ty c, SSnd) -> return (Proj tm Snd, vinst c (vproj (evalCtx ctx tm) Fst))
        (tty, SIndex i) -> do
          a <- go (evalCtx ctx tm) tty i 0
          return (Proj tm (PNamed Nothing i), a)
          where
            go :: Val -> Val -> Ix -> Ix -> IO Val
            go tm ty j j2 = case (force ty, j) of
              (VSigma x ty c, 0) -> return ty
              (VSigma x ty c, j) -> go tm (vinst c (vproj tm (PNamed Nothing j2))) (j - 1) (j2 + 1)
              _ -> error $ "not a sigma type in " ++ show c ++ ": " ++ showV ctx vt
        (tty, SNamed x) -> do
          (a, i) <- go (evalCtx ctx tm) tty 0 S.empty
          return (Proj tm (PNamed (Just x) i), a)
          where
            go :: Val -> Val -> Ix -> S.Set Name -> IO (Val, Ix)
            go tm ty i xs = case force ty of
              VSigma y ty c | x == y -> return (ty, i)
              VSigma y ty c -> do
                let name = if x == "_" || S.member x xs then Nothing else Just y
                go tm (vinst c (vproj tm (PNamed name i))) (i + 1) (S.insert y xs)
              _ -> error $ "name not found " ++ show c ++ ": " ++ showV ctx vt
        _ -> error $ "not a sigma type in " ++ show c ++ ": " ++ showV ctx vt
    tm -> throwIO $ ElaborateError $ "cannot infer: " ++ show tm

elaborate :: Ctx -> STm -> IO (Tm, Ty)
elaborate ctx tm = do
  (tm, vty) <- infer ctx tm
  return (tm, quoteCtx ctx vty)
