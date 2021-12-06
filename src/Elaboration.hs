module Elaboration (elaborate, elaborateDecls) where

import Control.Exception (throwIO, catch)
import qualified Data.Set as S
import System.IO.Unsafe
import Data.IORef

import Common
import Core
import Levels
import Val
import Evaluation hiding (conv)
import Ctx
import Errors (Error(ElaborateError), throwUnless)
import Surface
import Prims
import Verification
import Globals
import Metas
import Unification (unify)

-- holes
data HoleEntry = HoleEntry Ctx Tm Val

type HoleMap = [(Name, HoleEntry)]

holes :: IORef HoleMap
holes = unsafeDupablePerformIO $ newIORef mempty
{-# noinline holes #-}

resetHoles :: IO ()
resetHoles = writeIORef holes mempty

addHole :: Name -> Ctx -> Tm -> Val -> IO ()
addHole x ctx tm ty = do
  hs <- readIORef holes
  case lookup x hs of
    Just _ -> error $ "duplicate hole _" ++ x
    Nothing -> writeIORef holes ((x, HoleEntry ctx tm ty) : hs)

-- elaboration
freshMeta :: Ctx -> IO Tm
freshMeta ctx = do
  m <- newMeta
  return $ InsertedMeta m (bds ctx)

insert' :: Ctx -> IO (Tm, Val) -> IO (Tm, Val)
insert' ctx act = go =<< act where
  go (t, va) = case force va of
    VPi x Impl a b -> do
      m <- freshMeta ctx
      let mv = eval (env ctx) m
      go (App t m Impl, vinst b mv)
    va -> pure (t, va)

insert :: Ctx -> IO (Tm, Val) -> IO (Tm, Val)
insert ctx act = act >>= \case
  (t@(Lam _ Impl _), va) -> return (t, va)
  (t, va) -> insert' ctx (return (t, va))

insertUntilName :: Ctx -> Name -> IO (Tm, Val) -> IO (Tm, Val)
insertUntilName ctx name act = go =<< act where
  go (t, va) = case force va of
    va@(VPi x Impl a b) -> do
      if x == name then
        return (t, va)
      else do
        m <- freshMeta ctx
        let mv = eval (env ctx) m
        go (App t m Impl, vinst b mv)
    _ -> error $ "name " ++ name ++ " not found in pi"

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
    (SHole x, _) -> do
      tm <- freshMeta ctx
      maybe (return ()) (\x -> addHole x ctx tm ty) x
      return tm
    (SLam x i ma b, VPi x' i' ty b') | either (\x -> x == x' && i' == Impl) (== i') i -> do
      case ma of
        Nothing -> return ()
        Just a -> do
          (ca, u') <- checkTy ctx a
          catch (unify (lvl ctx) (evalCtx ctx ca) ty) $ \(err :: Error) ->
            throwIO $ ElaborateError $ "check failed " ++ show tm ++ " : " ++ showV ctx ty ++ " got " ++ showC ctx ca ++ ": " ++ show err
      cb <- check (bind x i' ty ctx) b (vinst b' (VVar (lvl ctx)))
      return $ Lam x i' cb
    (t, VPi x Impl a b) -> do
      Lam x Impl <$> check (bindInsert x Impl a ctx) t (vinst b (VVar (lvl ctx)))
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
      (ctm, ty') <- insert ctx $ infer ctx tm
      catch (unify (lvl ctx) ty' ty) $ \(err :: Error) ->
        throwIO $ ElaborateError $ "check failed " ++ show tm ++ " : " ++ showV ctx ty ++ " got " ++ showV ctx ty' ++ ": " ++ show err
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
                Just (_, Nothing) -> throwIO $ ElaborateError $ "variable referes to universe level variable: " ++ show t
                Nothing -> do
                  case getGlobal x of
                    Just e -> return (Global x, gTy e)
                    Nothing -> throwIO $ ElaborateError $ "undefined var " ++ show t
    SType l -> do
      l' <- checkFinLevel ctx l
      return (Type (FinLevel l'), VType (VFinLevel (vFLS (finLevelCtx ctx l'))))
    SPi x i t b -> do
      (ct, l1) <- checkTy ctx t
      (cb, l2) <- checkTy (bind x i (evalCtx ctx ct) ctx) b
      return (Pi x i ct cb, VType (l1 <> l2))
    SSigma x t b -> do
      (ct, l1) <- checkTy ctx t
      (cb, l2) <- checkTy (bind x Expl (evalCtx ctx ct) ctx) b
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
    c@(SApp f a i) -> do
      (i, cf, tty) <- case i of
        Left name -> do
          (t, tty) <- insertUntilName ctx name $ infer ctx f
          return (Impl, t, tty)
        Right Impl -> do
          (t, tty) <- infer ctx f
          return (Impl, t, tty)
        Right Expl -> do
          (t, tty) <- insert' ctx $ infer ctx f
          return (Expl, t, tty)
      (pt, rt) <- case force tty of
        VPi x i' a b -> do
          throwUnless (i == i') $ ElaborateError $ "app icit mismatch in " ++ show c ++ ": " ++ showV ctx tty
          return (a, b)
        tty -> do
          a <- eval (env ctx) <$> freshMeta ctx
          b <- Clos (env ctx) <$> freshMeta (bind "x" i a ctx)
          catch (unify (lvl ctx) tty (VPi "x" i a b)) $ \(err :: Error) ->
            throwIO $ ElaborateError $ "pi expected in " ++ show c ++ " but got " ++ showV ctx tty ++ ": " ++ show err
          return (a, b)
      ca <- check ctx a pt
      return (App cf ca i, vinst rt (evalCtx ctx ca))
    c@(SAppLvl f l) -> do
      (cf, fty) <- infer ctx f
      l' <- checkFinLevel ctx l
      let ffty = force fty
      case ffty of
        VPiLvl x c -> return (AppLvl cf l', vinstLevel c (finLevelCtx ctx l'))
        tty -> do
          b <- Clos (env ctx) <$> freshMeta (bindLevel "x" ctx)
          catch (unify (lvl ctx) tty (VPiLvl "x" b)) $ \(err :: Error) ->
            throwIO $ ElaborateError $ "expected a level pi in " ++ show c ++ " but got " ++ showV ctx fty ++ ": " ++ show err
          return (AppLvl cf l', vinstLevel b (finLevelCtx ctx l'))
    s@(SLam x (Right i) ma b) -> do
      a <- evalCtx ctx <$> case ma of
        Just a -> fst <$> checkTy ctx a
        Nothing -> freshMeta ctx
      (cb, rty) <- insert ctx $ infer (bind x i a ctx) b
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
        (VSigma x ty c, SSnd) -> return (Proj tm Snd, vinst c (vfst (evalCtx ctx tm)))
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
        (tty, _) | p == SFst || p == SSnd -> do
          a <- eval (env ctx) <$> freshMeta ctx
          b <- Clos (env ctx) <$> freshMeta (bind "x" Expl a ctx)
          catch (unify (lvl ctx) tty (VSigma "x" a b)) $ \(err :: Error) ->
            throwIO $ ElaborateError $ "not a sigma type in " ++ show c ++ ": " ++ showV ctx vt ++ ": " ++ show err
          case p of
            SFst -> return (Proj tm Fst, a)
            SSnd -> return (Proj tm Snd, vinst b (vfst (evalCtx ctx tm)))
            _ -> undefined
        _ -> error $ "not a sigma type in " ++ show c ++ ": " ++ showV ctx vt
    SHole x -> do
      a <- eval (env ctx) <$> freshMeta ctx
      t <- freshMeta ctx
      maybe (return ()) (\x -> addHole x ctx t a) x
      return (t, a)
    tm -> throwIO $ ElaborateError $ "cannot infer: " ++ show tm

showHoles :: HoleMap -> IO ()
showHoles [] = return ()
showHoles ((x, HoleEntry ctx tm ty) : t) = do
  showHoles t
  putStrLn ""
  putStrLn $ "hole\n_" ++ x ++ " : " ++ showVZ ctx ty ++ " = " ++ showCZ ctx tm
  print ctx

elaborate :: Ctx -> STm -> IO (Tm, Ty)
elaborate ctx tm = do
  resetMetas
  resetHoles
  (tm', vty) <- infer ctx tm
  let tm = zonkCtx ctx tm'
  let ty = zonkCtx ctx $ quoteCtx ctx vty
  hs <- readIORef holes
  onlyIf (not $ null hs) $ showHoles hs
  throwUnless (null hs) $ ElaborateError $ "\nholes found:\n" ++ showCZ ctx tm ++ "\n" ++ showCZ ctx ty ++ "\nholes: " ++ show (map fst $ reverse hs)
  solved <- allSolved
  throwUnless solved $ ElaborateError $ "not all metas are solved:\n" ++ showC ctx tm ++ "\n" ++ showC ctx ty
  ty' <- verify ctx tm
  throwUnless (ty == ty') $ ElaborateError $ "elaborated type did not match verified type: " ++ show ty ++ " ~ " ++ show ty'
  return (tm, ty)

elaborateDef :: Maybe String -> Name -> Maybe STy -> STm -> IO GlobalEntry
elaborateDef mod x ty tm =
  case getGlobal x of
    Just e | x /= "_" ->
      error $ "cannot redefine global " ++ maybe "" (++ ".") (gModule e) ++ x ++ " as " ++ maybe "" (++ ".") mod ++ x
    _ -> do
      (etm, ety) <- elaborate empty (SLet x ty tm (SVar x))
      return $ GlobalEntry x (eval [] ety) (eval [] etm) ety etm mod

elaborateDecl :: Maybe String -> Decl -> IO Decls
elaborateDecl _ (Import x) = return []
elaborateDecl mod d@(Def x ty tm) = do
  entry <- elaborateDef mod x ty tm
  addGlobal entry
  return [d]

elaborateDecls :: Maybe String -> Decls -> IO Decls
elaborateDecls mod [] = return []
elaborateDecls mod (hd : tl) = do
  ds <- elaborateDecl mod hd
  nextds <- elaborateDecls mod tl
  return (ds ++ nextds)
