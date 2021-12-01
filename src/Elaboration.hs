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
import Data.Bifunctor (first)
import qualified Data.Set as S

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
freshMeta :: Ctx -> Val -> VLevel -> IO Core
freshMeta ctx a u = do
  let closed = closeType (path ctx) (quote (lvl ctx) a) (quoteLevel (lvl ctx) u)
  let closedv = eval [] closed
  m <- newMeta closed closedv
  pure $ AppPruning (Meta m) (pruning ctx)

insert' :: Ctx -> IO (Core, Val, VLevel) -> IO (Core, Val, VLevel)
insert' ctx act = go =<< act where
  go (t, va, u) = case force va of
    VPi x Impl a u1 b u2 -> do
      m <- freshMeta ctx a u1
      let mv = eval (vs ctx) m
      go (App t m Impl, vinst b mv, vinstlevel u2 mv)
    va -> pure (t, va, u)

insert :: Ctx -> IO (Core, Val, VLevel) -> IO (Core, Val, VLevel)
insert ctx act = act >>= \case
  (t@(Abs _ Impl _), va, u) -> return (t, va, u)
  (t, va, u) -> insert' ctx (return (t, va, u))

insertUntilName :: Ctx -> Name -> IO (Core, Val, VLevel) -> IO (Core, Val, VLevel)
insertUntilName ctx name act = go =<< act where
  go (t, va, u) = case force va of
    va@(VPi x Impl a u1 b u2) -> do
      if x == name then
        return (t, va, u)
      else do
        m <- freshMeta ctx a u1
        let mv = eval (vs ctx) m
        go (App t m Impl, vinst b mv, vinstlevel u2 mv)
    _ -> error $ "name " ++ name ++ " not found in pi"

checkOrInfer :: Ctx -> Surface -> Maybe Surface -> IO (Core, Core, Val, VLevel)
checkOrInfer ctx v Nothing = do
  (cv, ty, u) <- infer ctx v
  return (cv, quote (lvl ctx) ty, ty, u)
checkOrInfer ctx v (Just t) = do
  (ct, u) <- inferUniv ctx t
  let ty = eval (vs ctx) ct
  cv <- check ctx v ty u
  return (cv, ct, ty, u)

check :: Ctx -> Surface -> Val -> VLevel -> IO Core
check ctx tm ty u = do
  let fty = force ty
  let fu = forceLevel u
  case (tm, {-trace ("check (" ++ show tm ++ ") : " ++ showV ctx ty ++ " : " ++ showVLevel ctx fu ++ " ~> " ++ showV ctx fty) $-} fty, fu) of
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
          unifyLevel (lvl ctx) u' u1
          unify (lvl ctx) (eval (vs ctx ) ca) ty
      let vv = vvar (lvl ctx)
      cb <- check (bind x i' ty u1 ctx) b (vinst b' vv) (vinstlevel u2 vv)
      return $ Abs x i' cb
    (t, VPi x Impl a u1 b u2, _) -> do
      let vv = vvar (lvl ctx)
      cb <- check (bindInsert x Impl a u1 ctx) t (vinst b vv) (vinstlevel u2 vv)
      return $ Abs x Impl cb
    (SPair a b, VSigma x ty u1 b' u2, _) -> do
      ta <- check ctx a ty u1
      let vv = eval (vs ctx) ta
      tb <- check ctx b (vinst b' vv) (vinstlevel u2 vv)
      return $ Pair ta tb
    (SLet x t v b, _, _) -> do
      (cv, ct, pty, ua) <- checkOrInfer ctx v t
      cb <- check (define x ct pty ua cv (eval (vs ctx) cv) ctx) b ty u
      return $ Let x ct cv cb
    (s@(SNatLit i), VULevel, _) -> do
      test (i >= 0) $ "negative nat literal: " ++ show s
      check ctx (go i) ty u
      where
        go 0 = SVar "L0"
        go n = SApp (SVar "LS") (go (n - 1)) (Right Expl)

    -- infer fallback
    (s, _, _) -> do
      (c, ty', u') <- insert ctx $ infer ctx s
      testIO (unifyLevel (lvl ctx) u' u) $ \e ->
        "universe check failed " ++ show s ++ " : " ++ showV ctx ty ++ " : " ++ showVLevel ctx u ++ " ~ " ++ showVLevel ctx u' ++ ": " ++ show e
      testIO (unify (lvl ctx) ty' ty) $ \e ->
        "check failed " ++ show s ++ " : " ++ showV ctx ty ++ ", got " ++ showV ctx ty' ++ ": " ++ show e
      return c

inferUniv :: Ctx -> Surface -> IO (Core, VLevel)
inferUniv ctx tm = do
  (ctm, ty, _) <- infer ctx tm
  case force ty of
    VU l -> return (ctm, l)
    _ -> error $ "expected a universe but got " ++ showV ctx ty ++ ", while checking " ++ show tm

infer :: Ctx -> Surface -> IO (Core, Val, VLevel)
infer ctx tm = case {-trace ("synth " ++ show tm)-} tm of
  SPos p s -> infer (enter p ctx) s
  SU l -> do
    cl <- check ctx l VULevel VOmega
    let vl = eval (vs ctx) cl
    return (U (Fin cl), VU (VFin (VLS vl)), VFin (VLS (VLS vl)))
  t@(SVar x) ->
    case toPrimName x of
      Just prim -> do
        let (t, u) = primType prim
        return (Prim (Left prim), t, u)
      Nothing ->
        case toPrimElimName x of
          Just prim -> do
            let (t, u) = primElimType prim
            return (Prim (Right prim), t, u)
          Nothing -> do
            res <- lookupVarMaybe ctx x
            case res of
              Just (i, ty, u) -> return (Var i, ty, u)
              Nothing -> do
                e <- lookupGlobal x
                let vt = gvtype e
                return (Global x, vt, guniv e)    
  c@(SApp f a i) -> do
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
        u1 <- eval (vs ctx) <$> freshMeta ctx VULevel VOmega
        a <- eval (vs ctx) <$> freshMeta ctx (VU (VFin u1)) (VFin $ VLS u1)
        let extctx = bind "x" i a (VFin u1) ctx
        u2 <- eval (vs ctx) <$> freshMeta extctx VULevel VOmega
        b <- Clos (vs ctx) <$> freshMeta extctx (VU $ VFin u2) (VFin $ VLS u2)
        unify (lvl ctx) tty (VPi "x" i a (VFin u1) b (FunLevel $ const $ VFin u2))
        return (a, VFin u1, b, FunLevel $ const $ VFin u2)
    ca <- check ctx a pt u1
    let vv = eval (vs ctx) ca
    return (App cf ca i, vinst rt vv, vinstlevel u2 vv)
  c@(SPi x i t b) -> do
    (ct, l1) <- inferUniv ctx t
    case forceLevel l1 of
      VOmegaSuc -> error $ "omega^ in pi: " ++ show c
      VOmega -> do
        (cb, l2) <- inferUniv (bind x i (eval (vs ctx) ct) l1 ctx) b
        let pi = Pi x i ct (quoteLevel (lvl ctx) l1) cb (quoteLevel (lvl ctx + 1) l2)
        return (pi, VU VOmega, VOmegaSuc)
      u1@(VFin l1) -> do
        (cb, l2a) <- inferUniv (bind x i (eval (vs ctx) ct) u1 ctx) b
        case strLevel (lvl ctx) (lvl ctx) l2a of
          Nothing -> error $ "invalid level dependency in " ++ show c
          Just l2b -> do
            let qu1 = quoteLevel (lvl ctx) u1
            let lmax = vlmax u1 (evallevel (vs ctx) l2b)
            let pi = Pi x i ct qu1 cb (quoteLevel (lvl ctx + 1) l2a)
            let vl = forceLevel lmax
            case vl of
              VOmegaSuc -> error $ "omega^ in pi: " ++ show c
              VOmega -> return (pi, VU lmax, VOmegaSuc)
              VFin l -> return (pi, VU lmax, VFin (VLS l))
  c@(SSigma x t b) -> do
    (ct, l1) <- inferUniv ctx t
    case forceLevel l1 of
      VOmegaSuc -> error $ "omega^ in sigma: " ++ show c
      VOmega -> do
        (cb, l2) <- inferUniv (bind x Expl (eval (vs ctx) ct) l1 ctx) b
        return (Sigma x ct (quoteLevel (lvl ctx) l1) cb (quoteLevel (lvl ctx + 1) l2), VU VOmega, VOmegaSuc)
      u1@(VFin l1) -> do
        (cb, l2a) <- inferUniv (bind x Expl (eval (vs ctx) ct) u1 ctx) b
        case strLevel (lvl ctx) (lvl ctx) l2a of
          Nothing -> error $ "invalid level dependency in " ++ show c
          Just l2b -> do
            let lmax = vlmax u1 (evallevel (vs ctx) l2b)
            let sigma = Sigma x ct (quoteLevel (lvl ctx) u1) cb (quoteLevel (lvl ctx + 1) l2a)
            case forceLevel lmax of
              VOmegaSuc -> error $ "omega^ in sigma: " ++ show c
              VOmega -> return (sigma, VU lmax, VOmegaSuc)
              VFin l -> return (sigma, VU lmax, VFin (VLS l))
  SPair a b -> do
    (ta, va, u1) <- infer ctx a
    (tb, vb, u2) <- infer ctx b
    let vt = VSigma "_" va u1 (Fun $ const vb) (FunLevel $ const u2)
    return (Let "p" (quote (lvl ctx) vt) (Pair ta tb) (Var 0), vt, vlmax u1 u2)
  c@(SProj t p) -> do
    (tm, vt, _) <- infer ctx t
    case (force vt, p) of
      (VSigma x ty u c _, SFst) -> return (Proj tm Fst, ty, u)
      (VSigma x ty _ c u, SSnd) -> do
        let vv = vproj (eval (vs ctx) tm) Fst
        return (Proj tm Snd, vinst c vv, vinstlevel u vv)
      (tty, SIndex i) -> do
        (a, u) <- go (eval (vs ctx) tm) tty i 0
        return (Proj tm (PNamed Nothing i), a, u)
        where
          go :: Val -> Val -> Ix -> Ix -> IO (Val, VLevel)
          go tm ty j j2 = case (force ty, j) of
            (VSigma x ty u1 c u2, 0) -> return (ty, u1)
            (VSigma x ty u1 c u2, j) -> go tm (vinst c (vproj tm (PNamed Nothing j2))) (j - 1) (j2 + 1)
            _ -> error $ "not a sigma type in " ++ show c ++ ": " ++ showV ctx vt
      (tty, SNamed x) -> do
        (a, u, i) <- go (eval (vs ctx) tm) tty 0 S.empty
        return (Proj tm (PNamed (Just x) i), a, u)
        where
          go :: Val -> Val -> Ix -> S.Set Name -> IO (Val, VLevel, Ix)
          go tm ty i xs = case force ty of
            VSigma y ty u1 c u2 | x == y -> return (ty, u1, i)
            VSigma y ty u1 c u2 -> do
              let name = if x == "_" || S.member x xs then Nothing else Just y
              go tm (vinst c (vproj tm (PNamed name i))) (i + 1) (S.insert y xs)
            _ -> error $ "name not found " ++ show c ++ ": " ++ showV ctx vt
      (tty, _) | p == SFst || p == SSnd -> do
        u1 <- eval (vs ctx) <$> freshMeta ctx VULevel VOmega
        a <- eval (vs ctx) <$> freshMeta ctx (VU (VFin u1)) (VFin $ VLS u1)
        let extctx = bind "x" Expl a (VFin u1) ctx
        u2 <- eval (vs ctx) <$> freshMeta extctx VULevel VOmega
        b <- Clos (vs ctx) <$> freshMeta extctx (VU $ VFin u2) (VFin $ VLS u2)
        unify (lvl ctx) tty (VSigma "x" a (VFin u1) b (FunLevel $ const $ VFin u2))
        case p of
          SFst -> return (Proj tm Fst, a, VFin u1) 
          SSnd -> return (Proj tm Snd, vinst b (vproj (eval (vs ctx) tm) Fst), VFin u2)
          _ -> undefined
      _ -> error $ "not a sigma type in " ++ show c ++ ": " ++ showV ctx vt
  SLet x t v b -> do
    (cv, ct, ty, ut) <- checkOrInfer ctx v t
    (cb, rty, u) <- infer (define x ct ty ut cv (eval (vs ctx) cv) ctx) b
    return (Let x ct cv cb, rty, u)
  SHole x -> do
    u <- eval (vs ctx) <$> freshMeta ctx VULevel VOmega
    a <- eval (vs ctx) <$> freshMeta ctx (VU (VFin u)) (VFin (VLS u))
    t <- freshMeta ctx a (VFin u)
    maybe (return ()) (\x -> addHole x ctx t a) x
    return (t, a, VFin u)
  SAbs x (Right i) ma b -> do
    (a, u1) <- first (eval (vs ctx)) <$> case ma of
      Just a -> inferUniv ctx a
      Nothing -> do
        u1 <- eval (vs ctx) <$> freshMeta ctx VULevel VOmega
        a <- freshMeta ctx (VU (VFin u1)) (VFin (VLS u1))
        return (a, VFin u1)
    (cb, rty, u2) <- insert ctx $ infer (bind x i a u1 ctx) b
    return (Abs x i cb, VPi x i a u1 (closeVal ctx rty) (closeVLevel ctx u2), vlmax u1 u2)
  s@(SNatLit i) -> do
    test (i >= 0) $ "negative nat literal: " ++ show s
    infer ctx (go i)
    where
      go :: Int -> Surface
      go 0 = SVar "Z"
      go n = SApp (SVar "S") (go (n - 1)) (Right Expl)
  s -> error $ "unable to infer " ++ show s

includeMetas :: (Ctx, Val, VLevel) -> [MetaVar] -> Core -> Core
includeMetas (ctx, ty, u) order t = go [] order
  where
    go :: [MetaVar] -> [MetaVar] -> Core
    go partial [] = expandMetas order t
    go partial (m : ms) =
      case lookupMeta m of
        Unsolved _ _ -> error $ "unsolved meta: ?" ++ show m ++ "\ntype: " ++ showV ctx ty ++ "\nuniv: " ++ showVLevel ctx u
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
  putStrLn $ "hole\n_" ++ x ++ " : " ++ showVZ ctx ty ++ " = " ++ showCZ ctx tm
  putStrLn $ showLocal ctx

elaborate :: Ctx -> Surface -> IO (Core, Core, VLevel)
elaborate ctx s = do
  reset
  resetHoles
  (xc, ty, u) <- infer ctx s
  let c = zonkCtx ctx xc
  hs <- readIORef holes
  onlyIf (not $ null hs) $ showHoles hs
  test (null hs) $ "\nholes found:\ntype: " ++ showVZ ctx ty ++ "\nuniv: " ++ showVZ ctx (VU u) ++ "\n" ++ show (map fst $ reverse hs)
  order <- orderMetas
  let c' = {- includeMetas (ctx, ty, u) order -} c
  let ty' = {- nf $ includeMetas (ctx, ty, u) order -} zonkCtx ctx (quote 0 ty)
  let cu = zonkLevelCtx ctx (quoteLevel (lvl ctx) u)
  let u' = evallevel (vs ctx) cu
  verify c'
  return (c', ty', u')

elaborateDefDef :: Maybe String -> Name -> Maybe Surface -> Surface -> IO GlobalEntry
elaborateDefDef mod x ty tm =
  case getGlobal x of
    Just e | x /= "_" ->
      error $ "cannot redefine global " ++ maybe "" (++ ".") (gmodule e) ++ x ++ " as " ++ maybe "" (++ ".") mod ++ x
    _ -> do
      (etm, ety, u) <- elaborate empty (SLet x ty tm (SVar x))
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
