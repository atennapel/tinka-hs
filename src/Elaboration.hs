module Elaboration (elaborate, elaborateDecls) where

import Control.Exception (throwIO, catch)
import qualified Data.Set as S
import System.IO.Unsafe
import Data.IORef
import Data.Bifunctor (first)

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
import Unification

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

freshLMeta :: Ctx -> IO FinLevel
freshLMeta ctx = do
  m <- newLMeta (lvl ctx) (levelVars ctx)
  return $ FLMeta m

insert' :: Ctx -> IO (Tm, Val, VLevel) -> IO (Tm, Val, VLevel)
insert' ctx act = go =<< act where
  go (t, va, lv) = case force va of
    VPi x Impl a _ b u2 -> do
      m <- freshMeta ctx
      let mv = eval (env ctx) m
      go (App t m Impl, vinst b mv, u2)
    VPiLvl x b u -> do
      m <- freshLMeta ctx
      let mv = finLevel (env ctx) m
      go (AppLvl t m, vinstLevel b mv, vinstCL u mv)
    va -> pure (t, va, lv)

insertLvl :: Ctx -> IO (Tm, Val, VLevel) -> IO (Tm, Val, VLevel)
insertLvl ctx act = go =<< act where
  go (t, va, lv) = case force va of
    VPiLvl x b u -> do
      m <- freshLMeta ctx
      let mv = finLevel (env ctx) m
      go (AppLvl t m, vinstLevel b mv, vinstCL u mv)
    va -> pure (t, va, lv)

insert :: Ctx -> IO (Tm, Val, VLevel) -> IO (Tm, Val, VLevel)
insert ctx act = act >>= \case
  (t@(Lam _ Impl _), va, lv) -> return (t, va, lv)
  (t, va, lv) -> insert' ctx (return (t, va, lv))

insertUntilName :: Ctx -> Name -> IO (Tm, Val, VLevel) -> IO (Tm, Val, VLevel)
insertUntilName ctx name act = go =<< act where
  go (t, va, lv) = case force va of
    va@(VPi x Impl a _ b u2) -> do
      if x == name then
        return (t, va, lv)
      else do
        m <- freshMeta ctx
        let mv = eval (env ctx) m
        go (App t m Impl, vinst b mv, u2)
    VPiLvl x b u -> do
      m <- freshLMeta ctx
      let mv = finLevel (env ctx) m
      go (AppLvl t m, vinstLevel b mv, vinstCL u mv)
    _ -> error $ "name " ++ name ++ " not found in pi"

checkOrInfer :: Ctx -> STm -> Maybe STm -> IO (Tm, Tm, Val, VLevel)
checkOrInfer ctx v Nothing = do
  (cv, ty, u) <- infer ctx v
  return (cv, quoteCtx ctx ty, ty, u)
checkOrInfer ctx v (Just t) = do
  (ct, u) <- checkTy ctx t
  let ty = evalCtx ctx ct
  cv <- check ctx v ty u
  return (cv, ct, ty, u)

unifyCtx :: Ctx -> VLevel -> VLevel -> Val -> Val -> String -> String -> IO ()
unifyCtx ctx u u' ty ty' msgu msgty = catch try1 $ \(err :: Error) -> try2
  where
    try1 = do
      catch (unifyLevel (lvl ctx) u u') $ \(err :: Error) ->
        throwIO $ ElaborateError $ msgu ++ ": " ++ show err
      catch (unify (lvl ctx) ty ty') $ \(err :: Error) ->
        throwIO $ ElaborateError $ msgty ++ ": " ++ show err
    try2 = do
      catch (unify (lvl ctx) ty ty') $ \(err :: Error) ->
        throwIO $ ElaborateError $ msgty ++ ": " ++ show err
      catch (unifyLevel (lvl ctx) u u') $ \(err :: Error) ->
        throwIO $ ElaborateError $ msgu ++ ": " ++ show err

check :: Ctx -> STm -> VTy -> VLevel -> IO Tm
check ctx tm ty lv = do
  let fty = force ty
  debug $ "check " ++ show tm ++ " : " ++ showVZ ctx ty ++ " : " ++ prettyVLevelCtx ctx lv
  case (tm, fty) of
    (SPos p tm, _) -> check (enter p ctx) tm ty lv
    (SHole x, _) -> do
      tm <- freshMeta ctx
      maybe (return ()) (\x -> addHole x ctx tm ty) x
      return tm
    (SLam x i ma b, VPi x' i' ty u1 b' u2) | either (\x -> x == x' && i' == Impl) (== i') i -> do
      case ma of
        Nothing -> return ()
        Just a -> do
          (ca, u') <- checkTy ctx a
          let ty' = evalCtx ctx ca
          unifyCtx ctx u' u1 ty' ty
            ("level check failed " ++ show tm ++ " : " ++ showVZ ctx ty ++ " : " ++ prettyVLevelCtx ctx u1 ++ " got " ++ showVZ ctx ty' ++ " : " ++ prettyVLevelCtx ctx u')
            ("check failed " ++ show tm ++ " : " ++ showVZ ctx ty ++ " got " ++ showVZ ctx ty')
      cb <- check (bind x i' ty u1 ctx) b (vinst b' (VVar (lvl ctx))) u2
      return $ Lam x i' cb
    (t, VPi x Impl a u1 b u2) -> do
      Lam x Impl <$> check (bindInsert x Impl a u1 ctx) t (vinst b (VVar (lvl ctx))) u2
    (SLamLvl x b, VPiLvl _ c u) -> do
      let v = vFinLevelVar (lvl ctx)
      LamLvl x <$> check (bindLevel x ctx) b (vinstLevel c v) (vinstCL u v)
    (t, VPiLvl x c u) -> do
      let v = vFinLevelVar (lvl ctx)
      LamLvl x <$> check (bindLevelInsert x ctx) t (vinstLevel c v) (vinstCL u v)
    (SPair a b, VSigma x ty u1 b' u2) -> do
      ta <- check ctx a ty u1
      tb <- check ctx b (vinst b' (evalCtx ctx ta)) u2
      return $ Pair ta tb
    (SLet x mt v b, _) -> do
      (cv, ct, vt, u) <- checkOrInfer ctx v mt
      cb <- check (define x vt u (evalCtx ctx cv) ctx) b ty lv
      return $ Let x ct cv cb

    (SCon t, VData l i d j) -> do
      ct <- check ctx t (vel l i (vlam "i" $ VData l i d) j d) lv
      return $ Con ct
    (SPair _ _, VData l i d j) -> check ctx (SCon tm) ty lv

    (SRefl, VHEq l a b x y) -> do
      catch (unify (lvl ctx) a b >> unify (lvl ctx) x y) $ \(err :: Error) -> 
        catch (unify (lvl ctx) x y >> unify (lvl ctx) a b) $ \(err :: Error) ->
          throwIO $ ElaborateError $ "check failed " ++ show tm ++ " : " ++ showVZ ctx ty ++ ": " ++ show err
      return Refl
    (SVar "[]", VHEq {}) -> check ctx SRefl ty lv

    (SVar x, VLift k l t) | x == "[]" || x == "True" || x == "False" -> do
      ct <- check ctx tm t (VFinLevel l)
      return $ cLiftTerm (quoteFinLevelCtx ctx k) (quoteFinLevelCtx ctx l) (quoteCtx ctx t) ct
    
    (tm, ty) -> do
      (ctm, ty', lv') <- insert ctx $ infer ctx tm      
      unifyCtx ctx lv' lv ty' ty
        ("level check failed " ++ show tm ++ " : " ++ showVZ ctx ty ++ " : " ++ prettyVLevelCtx ctx lv ++ " got " ++ showVZ ctx ty' ++ " : " ++ prettyVLevelCtx ctx lv')
        ("check failed " ++ show tm ++ " : " ++ showVZ ctx ty ++ " got " ++ showVZ ctx ty')
      return ctm

checkTy :: Ctx -> STm -> IO (Tm, VLevel)
checkTy ctx tm = do
  debug $ "checkTy " ++ show tm
  (ctm, ty, _) <- infer ctx tm
  debug $ "checkTy done: " ++ show ctm
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

infer :: Ctx -> STm -> IO (Tm, VTy, VLevel)
infer ctx tm = do
  debug $ "infer " ++ show tm
  case tm of
    SPos p t -> infer (enter p ctx) t
    t@(SVar x) ->
      case toPrimName x of
        Just prim ->
          let (ty, u) = primType prim in
          return (Prim (Left prim), ty, u)
        Nothing ->
          case toPrimElimName x of
            Just prim ->
              let (ty, u) = primElimType prim in
              return (Prim (Right prim), ty, u)
            Nothing -> do
              case lookupCtx ctx x of
                Just (i, Just (ty, u)) -> do
                  debug $ show t ++ " : " ++ showV ctx ty ++ " ~> '" ++ show i
                  return (Var i, ty, u)
                Just (_, Nothing) -> throwIO $ ElaborateError $ "variable referes to universe level variable: " ++ show t
                Nothing -> do
                  case getGlobal x of
                    Just e -> return (Global x, gTy e, gUniv e)
                    Nothing -> throwIO $ ElaborateError $ "undefined var " ++ show t
    SType l -> do
      l' <- checkFinLevel ctx l
      let vl = finLevelCtx ctx l'
      return (Type (FinLevel l'), VType (VFinLevel (vFLS vl)), VFinLevel (vFLS (vFLS vl)))
    SPi x i t b -> do
      (ct, l1) <- checkTy ctx t
      (cb, l2) <- checkTy (bind x i (evalCtx ctx ct) l1 ctx) b
      return (Pi x i ct (quoteLevelCtx ctx l1) cb (quoteLevelCtx ctx l2), VType (l1 <> l2), vLS (l1 <> l2))
    SSigma x t b -> do
      (ct, l1) <- checkTy ctx t
      (cb, l2) <- checkTy (bind x Expl (evalCtx ctx ct) l1 ctx) b
      return (Sigma x ct (quoteLevelCtx ctx l1) cb (quoteLevelCtx ctx l2), VType (l1 <> l2), vLS (l1 <> l2))
    SPiLvl x b -> do
      (cb, l) <- checkTy (bindLevel x ctx) b
      return (PiLvl x cb (quoteLevel (lvl ctx + 1) l), VType VOmega, VOmega1)
    SLet x mt v b -> do
      (cv, ct, vt, l) <- checkOrInfer ctx v mt
      (cb, ty, u) <- infer (define x vt l (evalCtx ctx cv) ctx) b
      return (Let x ct cv cb, ty, u)
    SPair a b -> do
      (ta, va, u1) <- infer ctx a
      (tb, vb, u2) <- infer ctx b
      let vt = VSigma "_" va u1 (Fun $ const vb) u2
      return (Let "p" (quoteCtx ctx vt) (Pair ta tb) (Var 0), vt, u1 <> u2)
    c@(SApp f a i) -> do
      (i, cf, tty, l1) <- case i of
        Left name -> do
          (t, tty, l1) <- insertUntilName ctx name $ infer ctx f
          return (Impl, t, tty, l1)
        Right Impl -> do
          (t, tty, l1) <- insertLvl ctx $ infer ctx f
          return (Impl, t, tty, l1)
        Right Expl -> do
          (t, tty, l1) <- insert' ctx $ infer ctx f
          return (Expl, t, tty, l1)
      (pt, u1, rt, u2) <- case force tty of
        VPi x i' a u1 b u2 -> do
          throwUnless (i == i') $ ElaborateError $ "app icit mismatch in " ++ show c ++ ": " ++ showV ctx tty
          return (a, u1, b, u2)
        tty -> do
          u1 <- VFinLevel . finLevel (env ctx) <$> freshLMeta ctx
          u2 <- VFinLevel . finLevel (env ctx) <$> freshLMeta ctx
          a <- eval (env ctx) <$> freshMeta ctx
          b <- Clos (env ctx) <$> freshMeta (bind "x" i a u1 ctx)
          unifyCtx ctx l1 (u1 <> u2) tty (VPi "x" i a u1 b u2)
            ("pi expected in " ++ show c ++ " but got " ++ showV ctx tty)
            ("pi expected in " ++ show c ++ " but got " ++ showV ctx tty)
          return (a, u1, b, u2)
      ca <- check ctx a pt u1
      return (App cf ca i, vinst rt (evalCtx ctx ca), u2)
    c@(SAppLvl f l) -> do
      (cf, fty, lf) <- infer ctx f
      l' <- checkFinLevel ctx l
      let ffty = force fty
      case ffty of
        VPiLvl x c u -> do
          let v = finLevelCtx ctx l'
          return (AppLvl cf l', vinstLevel c v, vinstCL u v)
        tty -> do
          b <- Clos (env ctx) <$> freshMeta (bindLevel "x" ctx)
          u <- ClosLvl (env ctx) . FinLevel <$> freshLMeta (bindLevel "x" ctx)
          unifyCtx ctx lf VOmega tty (VPiLvl "x" b u)
            ("expected a level pi in " ++ show c ++ " but got " ++ showV ctx fty)
            ("expected a level pi in " ++ show c ++ " but got " ++ showV ctx fty)
          let v = finLevelCtx ctx l'
          return (AppLvl cf l', vinstLevel b v, vinstCL u v)
    s@(SLam x (Right i) ma b) -> do
      (a, u1) <- first (evalCtx ctx) <$> case ma of
        Just a -> checkTy ctx a
        Nothing -> do
          u1 <- VFinLevel . finLevel (env ctx) <$> freshLMeta ctx
          m <- freshMeta ctx
          return (m, u1)
      (cb, rty, u2) <- insert ctx $ infer (bind x i a u1 ctx) b
      let vt = VPi x i a u1 (closeVal ctx rty) u2
      return (Let "f" (quoteCtx ctx vt) (Lam x i cb) (Var 0), vt, u1 <> u2)
    SLamLvl x b -> do
      (cb, rty, u) <- infer (bindLevel x ctx) b
      let vt = VPiLvl x (closeLevel ctx rty) (closeCL ctx u)
      return (Let "f" (quoteCtx ctx vt) (LamLvl x cb) (Var 0), vt, VOmega)
    c@(SProj t p) -> do
      (tm, vt, l1) <- infer ctx t
      case (force vt, p) of
        (VSigma x ty u1 c _, SFst) -> return (Proj tm Fst, ty, u1)
        (VSigma x ty _ c u2, SSnd) -> return (Proj tm Snd, vinst c (vfst (evalCtx ctx tm)), u2)
        (tty, SIndex i) -> do
          (a, u) <- go (evalCtx ctx tm) tty i 0
          return (Proj tm (PNamed Nothing i), a, u)
          where
            go :: Val -> Val -> Ix -> Ix -> IO (Val, VLevel)
            go tm ty j j2 = case (force ty, j) of
              (VSigma x ty u c _, 0) -> return (ty, u)
              (VSigma x ty _ c _, j) -> go tm (vinst c (vproj tm (PNamed Nothing j2))) (j - 1) (j2 + 1)
              _ -> error $ "not a sigma type in " ++ show c ++ ": " ++ showV ctx vt
        (tty, SNamed x) -> do
          (a, u, i) <- go (evalCtx ctx tm) tty 0 S.empty
          return (Proj tm (PNamed (Just x) i), a, u)
          where
            go :: Val -> Val -> Ix -> S.Set Name -> IO (Val, VLevel, Ix)
            go tm ty i xs = case force ty of
              VSigma y ty u c _ | x == y -> return (ty, u, i)
              VSigma y ty _ c _ -> do
                let name = if x == "_" || S.member x xs then Nothing else Just y
                go tm (vinst c (vproj tm (PNamed name i))) (i + 1) (S.insert y xs)
              _ -> error $ "name not found " ++ show c ++ ": " ++ showV ctx vt
        (tty, _) | p == SFst || p == SSnd -> do
          a <- eval (env ctx) <$> freshMeta ctx
          u1 <- VFinLevel . finLevel (env ctx) <$> freshLMeta ctx
          b <- Clos (env ctx) <$> freshMeta (bind "x" Expl a u1 ctx)
          u2 <- VFinLevel . finLevel (env ctx) <$> freshLMeta ctx
          unifyCtx ctx l1 (u1 <> u2) tty (VSigma "x" a u1 b u2)
            ("not a sigma type in " ++ show c ++ ": " ++ showV ctx vt)
            ("not a sigma type in " ++ show c ++ ": " ++ showV ctx vt)
          case p of
            SFst -> return (Proj tm Fst, a, u1)
            SSnd -> return (Proj tm Snd, vinst b (vfst (evalCtx ctx tm)), u2)
            _ -> undefined
        _ -> error $ "not a sigma type in " ++ show c ++ ": " ++ showV ctx vt
    SHole x -> do
      l <- freshLMeta ctx
      let u = VFinLevel $ finLevel (env ctx) l
      a <- eval (env ctx) <$> freshMeta ctx
      t <- freshMeta ctx
      maybe (return ()) (\x -> addHole x ctx t a) x
      return (t, a, u)
    tm -> throwIO $ ElaborateError $ "cannot infer: " ++ show tm

showHoles :: HoleMap -> IO ()
showHoles [] = return ()
showHoles ((x, HoleEntry ctx tm ty) : t) = do
  showHoles t
  putStrLn ""
  putStrLn $ "hole\n_" ++ x ++ " : " ++ showVZ ctx ty ++ " = " ++ showCZ ctx tm
  print ctx

elaborate :: Ctx -> STm -> IO (Tm, Ty, Level)
elaborate ctx tm = do
  resetMetas
  resetHoles
  (tm', vty, vlv) <- infer ctx tm
  let tm = zonkCtx ctx tm'
  let ty = zonkCtx ctx $ quoteCtx ctx vty
  let lv = zonkLevelCtx ctx $ quoteLevelCtx ctx vlv
  hs <- readIORef holes
  onlyIf (not $ null hs) $ showHoles hs
  throwUnless (null hs) $ ElaborateError $ "\nholes found:\n" ++ showCZ ctx tm ++ "\n" ++ showCZ ctx ty ++ "\nholes: " ++ show (map fst $ reverse hs)
  solved <- allSolved
  throwUnless solved $ ElaborateError $ "not all metas are solved:\n" ++ showC ctx tm ++ "\n" ++ showC ctx ty
  solvedL <- allLSolved
  throwUnless solvedL $ ElaborateError $ "not all level metas are solved" 
  ty' <- verify ctx tm
  -- throwUnless (ty == ty') $ ElaborateError $ "elaborated type did not match verified type: " ++ show ty ++ " ~ " ++ show ty'
  return (tm, ty, lv)

elaborateDef :: Maybe String -> Name -> Maybe STy -> STm -> IO GlobalEntry
elaborateDef mod x ty tm =
  case getGlobal x of
    Just e | x /= "_" ->
      error $ "cannot redefine global " ++ maybe "" (++ ".") (gModule e) ++ x ++ " as " ++ maybe "" (++ ".") mod ++ x
    _ -> do
      (etm, ety, elv) <- elaborate empty (SLet x ty tm (SVar x))
      debug $ "finished elaboration of " ++ x
      return $ GlobalEntry x (eval [] ety) (level [] elv) (eval [] etm) ety elv etm mod

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
