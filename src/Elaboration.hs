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
import Unification
import Data.List (intercalate)

import qualified Data.IntMap as IM
import Data.IORef
import System.IO.Unsafe

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
freshMeta :: Ctx -> Val -> IO Core
freshMeta ctx a = do
  let closed = closeType (path ctx) (quote (lvl ctx) a)
  let closedv = eval [] closed
  m <- newMeta closed closedv
  pure $ AppPruning (Meta m) (pruning ctx)

checkOrInfer :: Ctx -> Surface -> Maybe Surface -> IO (Core, Core, Val)
checkOrInfer ctx v Nothing = do
  (cv, ty) <- infer ctx v
  return (cv, quote (lvl ctx) ty, ty)
checkOrInfer ctx v (Just t) = do
  (ct, _) <- inferUniv ctx t
  let ty = eval (vs ctx) ct
  cv <- check ctx v ty
  return (cv, ct, ty)

check :: Ctx -> Surface -> Val -> IO Core
check ctx tm ty = do
  let fty = force ty
  case (tm, {-trace ("check (" ++ show tm ++ ") : " ++ showV ctx ty ++ " ~> " ++ showV ctx fty) $ -}fty) of
    (SPos p s, _) -> check (enter p ctx) s ty
    (SHole x, _) -> do
      tm <- freshMeta ctx ty
      maybe (return ()) (\x -> addHole x ctx tm ty) x
      return tm
    (SAbs x b, VPi x' ty b') -> do
      cb <- check (bind x ty ctx) b (vinst b' $ vvar (lvl ctx))
      return $ Abs x cb
    (SPair a b, VSigma x ty b') -> do
      ta <- check ctx a ty
      tb <- check ctx b (vinst b' $ eval (vs ctx) ta)
      return $ Pair ta tb
    (SLet x t v b, _) -> do
      (cv, ct, pty) <- checkOrInfer ctx v t
      cb <- check (define x ct pty cv (eval (vs ctx) cv) ctx) b ty
      return $ Let x ct cv cb
    (SLift t, VU l) | l > 0 -> do
      c <- check ctx t (VU (l - 1))
      return $ Lift c
    (SLiftTerm t, VLift ty) -> do
      c <- check ctx t ty
      return $ LiftTerm c
    (SLower t, ty) -> do
      c <- check ctx t (VLift ty)
      return $ Lower c
    (SCon t, x@(VData l d)) -> do
      c <- check ctx t (vel l 0 d x)
      return $ Con c

    -- some cumulativity
    -- Void^l : Type^k ~> Void^k (if l <= k)
    -- UnitType^l : Type^k ~> Void^k (if l <= k)
    -- Bool^l : Type^k ~> Void^k (if l <= k)
    --
    -- Unit^l : UnitType^k ~> Unit^k (if l <= k)
    -- True/False^l : Bool^k ~> True/False^k (if l <= k)
    (SVar x l, VU k) | toPrimName x == Just PVoid && l <= k -> return $ Prim PVoid k
    (SVar x l, VU k) | toPrimName x == Just PUnitType && l <= k -> return $ Prim PUnitType k
    (SVar x l, VU k) | toPrimName x == Just PBool && l <= k -> return $ Prim PBool k

    (SVar x l, VNe (HPrim PUnitType k) []) | toPrimName x == Just PUnit && l <= k -> return $ Prim PUnit k
    (SVar x l, VNe (HPrim PBool k) []) | toPrimName x == Just PTrue && l <= k -> return $ Prim PTrue k
    (SVar x l, VNe (HPrim PBool k) []) | toPrimName x == Just PFalse && l <= k -> return $ Prim PFalse k

    (SRefl, VNe (HPrim PHEq _) [EApp y, EApp x, EApp b, EApp a]) -> do
      testIO (unify (lvl ctx) a b) $ \e -> "type mismatch in Refl: " ++ showV ctx ty ++ ": " ++ show e
      testIO (unify (lvl ctx) x y) $ \e -> "value mismatch in Refl: " ++ showV ctx ty ++ ": " ++ show e
      return Refl

    -- infer fallback
    (s, _) -> do
      (c, ty') <- infer ctx s
      testIO (unify (lvl ctx) ty' ty) $ \e -> "check failed " ++ show s ++ " : " ++ showV ctx ty ++ ", got " ++ showV ctx ty' ++ ": " ++ show e
      return c

inferUniv :: Ctx -> Surface -> IO (Core, ULvl)
inferUniv ctx tm = do
  (c, ty) <- infer ctx tm
  case force ty of
    VU l -> return (c, l)
    _ -> error $ "expected a universe but got " ++ showV ctx ty ++ ", while checking " ++ show tm 

infer :: Ctx -> Surface -> IO (Core, Val)
infer ctx (SPos p s) = infer (enter p ctx) s
infer ctx (SU l) = return (U l, VU (l + 1))
infer ctx t@(SVar x l) =
  case toPrimName x of
    Just prim -> return (Prim prim l, primType prim l)
    Nothing -> do
      res <- lookupVarMaybe ctx x
      case res of
        Just (i, ty) -> do
          test (l == 0) $ "cannot lift local var " ++ show t 
          return (Var i, ty)
        Nothing -> do
          e <- lookupGlobal x
          let vt = if l == 0 then gvtype e else eval [] (liftUniv l (gtype e))
          return (Global x l, vt)
infer ctx (SPrimElim x l k) = do
  case toPrimElimName x of
    Just prim -> return (PrimElim prim l k, primElimType prim l k)
    Nothing -> error $ "undefined primitive " ++ x
infer ctx c@(SApp f a) = do
  (cf, fty) <- infer ctx f
  (t, b) <- case force fty of
    VPi x t b -> return (t, b)
    tty -> do
      a <- eval (vs ctx) <$> freshMeta ctx (VU 0) -- TODO: universe metas
      b <- Clos (vs ctx) <$> freshMeta (bind "x" a ctx) (VU 0) -- TODO: universe metas
      unify (lvl ctx) tty (VPi "x" a b)
      return (a, b)
  ca <- check ctx a t
  return (App cf ca, vinst b (eval (vs ctx) ca))
infer ctx (SPi x t b) = do
  (ct, l1) <- inferUniv ctx t
  let ty = eval (vs ctx) ct
  (cb, l2) <- inferUniv (bind x ty ctx) b
  return (Pi x ct cb, VU (max l1 l2))
infer ctx (SSigma x t b) = do
  (ct, l1) <- inferUniv ctx t
  let ty = eval (vs ctx) ct
  (cb, l2) <- inferUniv (bind x ty ctx) b
  return (Sigma x ct cb, VU (max l1 l2))
infer ctx (SPair a b) = do
  (ta, va) <- infer ctx a
  (tb, vb) <- infer ctx b
  let vt = VSigma "_" va (Fun $ const vb)
  return (Let "p" (quote (lvl ctx) vt) (Pair ta tb) (Var 0), vt)
infer ctx c@(SProj t p) = do
  (tm, vt) <- infer ctx t
  case (force vt, p) of
    (VSigma x ty c, Fst) -> return (Proj tm p, ty)
    (VSigma x ty c, Snd) -> return (Proj tm p, vinst c $ vproj (eval (vs ctx) tm) Fst)
    _ -> error $ "not a sigma type in " ++ show c ++ ", got " ++ showV ctx vt
infer ctx (SLet x t v b) = do
  (cv, ct, ty) <- checkOrInfer ctx v t
  (cb, rty) <- infer (define x ct ty cv (eval (vs ctx) cv) ctx) b
  return (Let x ct cv cb, rty)
infer ctx (SLift t) = do
  (c, l) <- inferUniv ctx t
  return (Lift c, VU (l + 1))
infer ctx (SLiftTerm t) = do
  (c, ty) <- infer ctx t
  return (LiftTerm c, VLift ty)
infer ctx tm@(SLower t) = do
  (c, ty) <- infer ctx t
  case force ty of
    VLift ty' -> return (Lower c, ty')
    _ -> error $ "expected lift type in " ++ show tm ++ " but got " ++ showV ctx ty
infer ctx (SHole x) = do
  a <- eval (vs ctx) <$> freshMeta ctx (VU 0) -- TODO: universe metas
  t <- freshMeta ctx a
  maybe (return ()) (\x -> addHole x ctx t a) x
  return (t, a)
infer ctx (SAbs x b) = do
  a <- eval (vs ctx) <$> freshMeta ctx (VU 0) -- TODO: universe metas
  (cb, rty) <- infer (bind x a ctx) b
  return (Abs x cb, VPi x a $ closeVal ctx rty)
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

elaborate :: Ctx -> Surface -> IO (Core, Core)
elaborate ctx s = do
  reset
  resetHoles
  (c, ty) <- infer ctx s
  hs <- readIORef holes
  showHoles hs
  test (null hs) $ "\nholes found: " ++ show (map fst $ reverse hs)
  order <- orderMetas
  let c' = includeMetas order c
  let ty' = nf $ includeMetas order (quote 0 ty)
  verify c'
  return (c', ty')

elaborateDefDef :: Maybe String -> Name -> Maybe Surface -> Surface -> IO GlobalEntry
elaborateDefDef mod x ty tm =
  case getGlobal x of
    Just e | x /= "_" ->
      error $ "cannot redefine global " ++ maybe "" (++ ".") (gmodule e) ++ x ++ " as " ++ maybe "" (++ ".") mod ++ x
    _ -> do
      (etm, ety) <- elaborate empty (SLet x ty tm (SVar x 0))
      return $ GlobalEntry x etm ety (eval [] etm) (eval [] ety) mod

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
