module Elaboration (elaborate, elaborateDef, elaborateDefs) where

import Ctx
import Surface
import Core
import Val
import Common
import Verification (verify)
import Evaluation
import Globals
import Metas
import Universes
import Unification

import Data.List (intercalate)
import qualified Data.IntMap as IM
import Data.IORef
import System.IO.Unsafe
import Data.Bifunctor (first)

-- import Debug.Trace (trace)

-- holes
data HoleEntry = HoleEntry Ctx Core Val

type HoleMap = [(Name, HoleEntry)]

holes :: IORef HoleMap
holes = unsafeDupablePerformIO $ newIORef mempty
{-# noinline holes #-}

resetHoles :: IO ()
resetHoles = writeIORef holes mempty

addHole :: Name -> Ctx -> Core -> Val -> IO ()
addHole x ctx tm ty = do
  hs <- readIORef holes
  case lookup x hs of
    Just _ -> error $ "duplicate hole _" ++ x
    Nothing -> writeIORef holes ((x, HoleEntry ctx tm ty) : hs)

-- elaboration
freshMeta :: Ctx -> Val -> Univ -> IO Core
freshMeta ctx a u = do
  let closed = closeType (path ctx) (quote (lvl ctx) a) u
  let closedv = eval [] closed
  m <- newMeta closed closedv
  pure $ AppPruning (Meta m) (pruning ctx)

insert' :: Ctx -> IO (Core, Val, Univ) -> IO (Core, Val, Univ)
insert' ctx act = go =<< act where
  go (t, va, u) = case force va of
    VPi x Impl a u1 b u2 -> do
      m <- freshMeta ctx a u1
      let mv = eval (vs ctx) m
      go (App t m Impl, vinst b mv, u2)
    va -> pure (t, va, u)

insert :: Ctx -> IO (Core, Val, Univ) -> IO (Core, Val, Univ)
insert ctx act = act >>= \case
  (t@(Abs _ Impl _), va, u) -> return (t, va, u)
  (t, va, u) -> insert' ctx (return (t, va, u))

insertUntilName :: Ctx -> Name -> IO (Core, Val, Univ) -> IO (Core, Val, Univ)
insertUntilName ctx name act = go =<< act where
  go (t, va, u) = case force va of
    va@(VPi x Impl a u1 b u2) -> do
      if x == name then
        return (t, va, u)
      else do
        m <- freshMeta ctx a u1
        let mv = eval (vs ctx) m
        go (App t m Impl, vinst b mv, u2)
    _ -> error $ "name " ++ name ++ " not found in pi"

checkOrInfer :: Ctx -> Surface -> Maybe Surface -> IO (Core, Core, Val, Univ)
checkOrInfer ctx v Nothing = do
  (cv, ty, u) <- infer ctx v
  return (cv, quote (lvl ctx) ty, ty, u)
checkOrInfer ctx v (Just t) = do
  (ct, u) <- inferUniv ctx t
  let ty = eval (vs ctx) ct
  cv <- check ctx v ty u
  return (cv, ct, ty, u)

check :: Ctx -> Surface -> Val -> Univ -> IO Core
check ctx tm ty u = do
  let fty = force ty
  let fu = normalizeUniv u
  case (tm, {-trace ("check (" ++ show tm ++ ") : " ++ showV ctx ty ++ " : " ++ show fu ++ " ~> " ++ showV ctx fty) $ -}fty, fu) of
    (SPos p s, _, _) -> check (enter p ctx) s ty u
    (SHole x, _, _) -> do
      tm <- freshMeta ctx ty u
      maybe (return ()) (\x -> addHole x ctx tm ty) x
      return tm
    (SAbs x i ma b, VPi x' i' ty u1 b' u2, _) | either (\x -> x == x' && i' == Impl) (== i') i -> do
      case ma of
        Nothing -> return ()
        Just a -> do
          (ca, u') <- inferUniv ctx a
          unifyUniv u' u1
          unify (lvl ctx) (eval (vs ctx ) ca) ty
      cb <- check (bind x i' ty u1 ctx) b (vinst b' $ vvar (lvl ctx)) u2
      return $ Abs x i' cb
    (t, VPi x Impl a u1 b u2, _) -> do
      cb <- check (bindInsert x Impl a u1 ctx) t (vinst b (VVar (lvl ctx))) u2
      return $ Abs x Impl cb
    (SPair a b, VSigma x ty u1 b' u2, _) -> do
      ta <- check ctx a ty u1
      tb <- check ctx b (vinst b' $ eval (vs ctx) ta) u2
      return $ Pair ta tb
    (SLet x t v b, _, _) -> do
      (cv, ct, pty, ua) <- checkOrInfer ctx v t
      cb <- check (define x ct pty ua cv (eval (vs ctx) cv) ctx) b ty u
      return $ Let x ct cv cb
    (SLift t, VU (UConst l), _) | l > 0 -> do
      c <- check ctx t (VU (UConst $ l - 1)) (UConst l)
      return $ Lift c
    (SLiftTerm t, VLift ty, _) -> do
      c <- check ctx t ty u
      return $ LiftTerm c
    (SLower t, ty, _) -> do
      c <- check ctx t (VLift ty) (us u)
      return $ Lower c
    (SCon t, x@(VData l d), _) -> do
      c <- check ctx t (vel l 0 d x) u
      return $ Con c

    -- some cumulativity
    -- Void^l : Type^k ~> Void^k (if l <= k)
    -- UnitType^l : Type^k ~> Void^k (if l <= k)
    -- Bool^l : Type^k ~> Void^k (if l <= k)
    --
    -- Unit^l : UnitType^k ~> Unit^k (if l <= k)
    -- True/False^l : Bool^k ~> True/False^k (if l <= k)
    (SVar x l, _, UConst k) | toPrimName x == Just PVoid && k > 0 && l <= k - 1 -> do
      unify (lvl ctx) ty (VU (UConst $ k - 1))
      return $ Prim PVoid (k - 1)
    (SVar x l, _, UConst k) | toPrimName x == Just PUnitType && k > 0 && l <= k - 1 -> do
      unify (lvl ctx) ty (VU (UConst $ k - 1))
      return $ Prim PUnitType (k - 1)
    (SVar x l, _, UConst k) | toPrimName x == Just PBool && k > 0 && l <= k - 1 -> do
      unify (lvl ctx) ty (VU (UConst $ k - 1))
      return $ Prim PBool (k - 1)
    
    (SVar x l, VU (UConst k), ut) | toPrimName x == Just PVoid && l <= k -> do
      unifyUniv ut (UConst $ k + 1)
      return $ Prim PVoid k
    (SVar x l, VU (UConst k), ut) | toPrimName x == Just PUnitType && l <= k -> do
      unifyUniv ut (UConst $ k + 1)
      return $ Prim PUnitType k
    (SVar x l, VU (UConst k), ut) | toPrimName x == Just PBool && l <= k -> do
      unifyUniv ut (UConst $ k + 1)
      return $ Prim PBool k

    (SVar x l, VNe (HPrim PUnitType k) [], ut) | toPrimName x == Just PUnit && l <= k -> do
      unifyUniv ut (UConst k)
      return $ Prim PUnit k
    (SVar x l, VNe (HPrim PBool k) [], ut) | toPrimName x == Just PTrue && l <= k -> do
      unifyUniv ut (UConst k)
      return $ Prim PTrue k
    (SVar x l, VNe (HPrim PBool k) [], ut) | toPrimName x == Just PFalse && l <= k -> do
      unifyUniv ut (UConst k)
      return $ Prim PFalse k
    
    (SVar x l, _, UConst k) | toPrimName x == Just PUnit && l <= k -> do
      unify (lvl ctx) ty (VNe (HPrim PUnitType k) [])
      return $ Prim PUnit k
    (SVar x l, _, UConst k) | toPrimName x == Just PTrue && l <= k -> do
      unify (lvl ctx) ty (VNe (HPrim PBool k) [])
      return $ Prim PTrue k
    (SVar x l, _, UConst k) | toPrimName x == Just PFalse && l <= k -> do
      unify (lvl ctx) ty (VNe (HPrim PBool k) [])
      return $ Prim PFalse k

    (SRefl, VNe (HPrim PHEq _) [EApp y Expl, EApp x Expl, EApp b Expl, EApp a Expl], _) -> do
      testIO (unify (lvl ctx) a b) $ \e -> "type mismatch in Refl: " ++ showV ctx ty ++ ": " ++ show e
      testIO (unify (lvl ctx) x y) $ \e -> "value mismatch in Refl: " ++ showV ctx ty ++ ": " ++ show e
      return Refl

    -- infer fallback
    (s, _, _) -> do
      (c, ty', u') <- insert ctx $ infer ctx s
      testIO (unifyUniv u' u) $ \e -> "universe check failed " ++ show s ++ " : " ++ showV ctx ty ++ " : " ++ show u ++ " ~ " ++ show u' ++ ": " ++ show e
      testIO (unify (lvl ctx) ty' ty) $ \e -> "check failed " ++ show s ++ " : " ++ showV ctx ty ++ ", got " ++ showV ctx ty' ++ ": " ++ show e
      return c

inferUniv :: Ctx -> Surface -> IO (Core, Univ)
inferUniv ctx tm = do
  u <- UMeta <$> newUMeta
  ctm <- check ctx tm (VU u) (us u)
  return (ctm, normalizeUniv u)

infer :: Ctx -> Surface -> IO (Core, Val, Univ)
infer ctx (SPos p s) = infer (enter p ctx) s
infer ctx (SU l) = return (U (UConst l), VU (UConst $ l + 1), UConst $ l + 2)
infer ctx t@(SVar x l) =
  case toPrimName x of
    Just prim -> do
      let (t, u) = primType prim l
      return (Prim prim l, t, u)
    Nothing -> do
      res <- lookupVarMaybe ctx x
      case res of
        Just (i, ty, u) -> do
          test (l == 0) $ "cannot lift local var " ++ show t 
          return (Var i, ty, u)
        Nothing -> do
          e <- lookupGlobal x
          let vt = if l == 0 then gvtype e else eval [] (liftUniv l (gtype e))
          return (Global x l, vt, uAddConst l (guniv e))
infer ctx (SPrimElim x l k) = do
  case toPrimElimName x of
    Just prim -> do
      let (t, u) = primElimType prim l k
      return (PrimElim prim l k, t, u)
    Nothing -> error $ "undefined primitive " ++ x
infer ctx c@(SApp f a i) = do
  (i, cf, tty, u) <- case i of
    Left name -> do
      (t, tty, u) <- insertUntilName ctx name $ infer ctx f
      return (Impl, t, tty, u)
    Right Impl -> do
      (t, tty, u) <- infer ctx f
      return (Impl, t, tty, u)
    Right Expl -> do
      (t, tty, u) <- insert' ctx $ infer ctx f
      return (Expl, t, tty, u)
  (pt, u1, rt, u2) <- case force tty of
    VPi x i' a u1 b u2 -> do
      test (i == i') $ "app icit mismatch in " ++ show c ++ ": " ++ showV ctx tty
      return (a, u1, b, u2)
    tty -> do
      u1 <- UMeta <$> newUMeta
      u2 <- UMeta <$> newUMeta
      a <- eval (vs ctx) <$> freshMeta ctx (VU u1) (us u1)
      b <- Clos (vs ctx) <$> freshMeta (bind "x" i a u1 ctx) (VU u2) (us u2)
      unify (lvl ctx) tty (VPi "x" i a u1 b u2)
      return (a, u1, b, u2)
  ca <- check ctx a pt u1
  return (App cf ca i, vinst rt (eval (vs ctx) ca), u2)
infer ctx (SPi x i t b) = do
  (ct, u1) <- inferUniv ctx t
  let ty = eval (vs ctx) ct
  (cb, u2) <- inferUniv (bind x i ty u1 ctx) b
  let lmax = umax u1 u2
  return (Pi x i ct u1 cb u2, VU lmax, us lmax)
infer ctx (SSigma x t b) = do
  (ct, u1) <- inferUniv ctx t
  let ty = eval (vs ctx) ct
  (cb, u2) <- inferUniv (bind x Expl ty u1 ctx) b
  let lmax = umax u1 u2
  return (Sigma x ct u1 cb u2, VU lmax, us lmax)
infer ctx (SPair a b) = do
  (ta, va, u1) <- infer ctx a
  (tb, vb, u2) <- infer ctx b
  let vt = VSigma "_" va u1 (Fun $ const vb) u2
  return (Let "p" (quote (lvl ctx) vt) (Pair ta tb) (Var 0), vt, umax u1 u2)
infer ctx c@(SProj t p) = do
  (tm, vt, _) <- infer ctx t
  case (force vt, p) of
    (VSigma x ty u c _, Fst) -> return (Proj tm p, ty, u)
    (VSigma x ty _ c u, Snd) -> return (Proj tm p, vinst c $ vproj (eval (vs ctx) tm) Fst, u)
    _ -> error $ "not a sigma type in " ++ show c ++ ", got " ++ showV ctx vt
infer ctx (SLet x t v b) = do
  (cv, ct, ty, ut) <- checkOrInfer ctx v t
  (cb, rty, u) <- infer (define x ct ty ut cv (eval (vs ctx) cv) ctx) b
  return (Let x ct cv cb, rty, u)
infer ctx (SLift t) = do
  (c, l) <- inferUniv ctx t
  return (Lift c, VU (us l), us (us l))
infer ctx (SLiftTerm t) = do
  (c, ty, u) <- infer ctx t
  return (LiftTerm c, VLift ty, us u)
infer ctx tm@(SLower t) = do
  (c, ty, u) <- infer ctx t
  case force ty of
    VLift ty' -> return (Lower c, ty', u)
    _ -> error $ "expected lift type in " ++ show tm ++ " but got " ++ showV ctx ty
infer ctx (SHole x) = do
  u <- UMeta <$> newUMeta
  a <- eval (vs ctx) <$> freshMeta ctx (VU u) (us u)
  t <- freshMeta ctx a u
  maybe (return ()) (\x -> addHole x ctx t a) x
  return (t, a, u)
infer ctx (SAbs x (Right i) ma b) = do
  (a, u1) <- first (eval (vs ctx)) <$> case ma of
    Just a -> inferUniv ctx a
    Nothing -> do
      u1 <- UMeta <$> newUMeta
      a <- freshMeta ctx (VU u1) (us u1)
      return (a, u1)
  (cb, rty, u2) <- insert ctx $ infer (bind x i a u1 ctx) b
  return (Abs x i cb, VPi x i a u1 (closeVal ctx rty) u2, umax u1 u2)
infer ctx s = error $ "unable to infer " ++ show s

includeMetas :: [MetaVar] -> Core -> Core
includeMetas order t = go [] order
  where
    go :: [MetaVar] -> [MetaVar] -> Core
    go partial [] = expandMetas order t
    go partial (m : ms) =
      case lookupMeta m of
        Unsolved _ _ -> error $ "unsolved meta: ?" ++ show m
        Solved _ ct _ c _ ->
          let expandedType = expandMetas partial ct in
          let expandedValue = expandMetas partial c in
          Let ("?" ++ show m) expandedType expandedValue (go (partial ++ [m]) ms)

showMetaEntry :: Int -> MetaEntry -> String
showMetaEntry x (Unsolved ct vt) = "?" ++ show x ++ " : " ++ showC empty ct
showMetaEntry x (Solved _ ct vt c v) = "?" ++ show x ++ " : " ++ showC empty ct ++ " = " ++ showC empty c

showMetas :: IO ()
showMetas = do
  ms <- readIORef mcxt
  putStrLn $ intercalate "\n" $ map (uncurry showMetaEntry) $ IM.assocs ms
  return ()

showHoles :: HoleMap -> IO ()
showHoles [] = showMetas
showHoles ((x, HoleEntry ctx tm ty) : t) = do
  showHoles t
  putStrLn ""
  putStrLn $ "hole _" ++ x ++ " : " ++ showV ctx ty ++ " = " ++ showC ctx tm
  putStrLn $ showLocal ctx

elaborate :: Ctx -> Surface -> IO (Core, Core, Univ)
elaborate ctx s = do
  reset
  resetHoles
  resetUMetas
  (c, ty, u) <- infer ctx s
  hs <- readIORef holes
  showHoles hs
  test (null hs) $ "\nholes found: " ++ show (map fst $ reverse hs)
  ums <- getUMetas
  test (allUMetasSolved ums) $ "\nunsolved universe metas:\n" ++ showUMetaMap ums
  order <- orderMetas
  let c' = includeMetas order c
  let ty' = nf $ includeMetas order (quote 0 ty)
  verify c'
  return (c', ty', normalizeUniv u)

elaborateDefDef :: Maybe String -> Name -> Maybe Surface -> Surface -> IO GlobalEntry
elaborateDefDef mod x ty tm =
  case getGlobal x of
    Just e | x /= "_" ->
      error $ "cannot redefine global " ++ maybe "" (++ ".") (gmodule e) ++ x ++ " as " ++ maybe "" (++ ".") mod ++ x
    _ -> do
      (etm, ety, u) <- elaborate empty (SLet x ty tm (SVar x 0))
      return $ GlobalEntry x etm ety (eval [] etm) (eval [] ety) u mod

elaborateDef :: Maybe String -> Def -> IO Defs
elaborateDef _ (Import x) = return []
elaborateDef mod d@(Def x ty tm) = do
  entry <- elaborateDefDef mod x ty tm
  addGlobal entry
  return [d]

elaborateDefs :: Maybe String -> Defs -> IO Defs
elaborateDefs mod [] = return []
elaborateDefs mod (hd : tl) = do
  ds <- elaborateDef mod hd
  nextds <- elaborateDefs mod tl
  return (ds ++ nextds)
