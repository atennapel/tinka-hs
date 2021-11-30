module Unification (unify, unifyLevel) where

import Common
import Core
import Val
import Evaluation
import Metas
import Prims

import qualified Data.IntMap as IM
import qualified Data.Set as S
import Data.IORef
import Control.Exception (catch, try, SomeException)
import Control.Monad (guard)

-- import Debug.Trace (trace)

data PR = PR {
  occ :: Maybe MetaVar,
  dom :: Lvl,
  cod :: Lvl,
  ren :: IM.IntMap Lvl
}

lift :: PR -> PR
lift (PR occ dom cod ren) = PR occ (dom + 1) (cod + 1) (IM.insert cod dom ren)

skip :: PR -> PR
skip (PR occ dom cod ren) = PR occ dom (cod + 1) ren

invert :: Lvl -> Spine -> IO (PR, Maybe Pruning)
invert gamma sp = do
  (dom, ren, pr, isLinear) <- go sp
  return (PR Nothing dom gamma ren, pr <$ guard isLinear)
  where
    go :: Spine -> IO (Lvl, IM.IntMap Lvl, Pruning, Bool)
    go [] = return (0, mempty, [], True)
    go (EApp t i : sp) = do
      (dom, ren, pr, isLinear) <- go sp
      case force t of
        VVar x | IM.member x ren -> return (dom + 1, IM.delete x ren, Nothing : pr, False)
        VVar x -> return (dom + 1, IM.insert x dom ren, Just i : pr, isLinear)
        _ -> error "failed to unify"
    go (_ : sp) = error "elim in spine"

pruneTy :: RevPruning -> Val -> IO Core
pruneTy (RevPruning pr) a = go pr (PR Nothing 0 0 mempty) a
  where
    go :: Pruning -> PR -> Val -> IO Core
    go pr pren a = case (pr, force a) of
      ([], a) -> rename pren a
      (Just _ : pr, VPi x i a u1 b u2) ->
        Pi x i <$> rename pren a <*> renameLevel pren u1 <*> go pr (lift pren) (vinst b (VVar (cod pren))) <*> renameClosLevel pren u2
      (Nothing : pr, VPi x i a u1 b u2) -> go pr (skip pren) (vinst b (VVar (cod pren)))
      _ -> error "impossible"

getUnsolved :: MetaVar -> (Core, Val)
getUnsolved m = case lookupMeta m of
  Unsolved c a -> (c, a)
  _ -> error "impossible"

pruneMeta :: Pruning -> MetaVar -> IO MetaVar
pruneMeta pr m = do
  let (cty, mty) = getUnsolved m
  prunedty <- pruneTy (revPruning pr) mty
  let prunedtyv = eval [] prunedty
  m' <- newMeta prunedty prunedtyv
  let solution = lams (length pr) mty $ AppPruning (Meta m') pr
  let solutionv = eval [] solution
  let deps = S.union (allMetas solution) (allMetas prunedty)  
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved deps cty mty solution solutionv)
  return m'

data SpineStatus
  = OKRenaming
  | OKNonRenaming
  | NeedsPruning

pruneFlex :: PR -> MetaVar -> Spine -> IO Core
pruneFlex pren m sp = do
  (sp, status) <- go sp
  m' <- case status of
    NeedsPruning -> pruneMeta (map (\(mt, i) -> i <$ mt) sp) m
    OKRenaming -> case lookupMeta m of
      Unsolved _ _ -> return m
      _ -> error "impossible"
    OKNonRenaming -> case lookupMeta m of
      Unsolved _ _ -> return m
      _ -> error "impossible"
  return $ foldr (\(mu, i) t -> maybe t (\u -> App t u i) mu) (Meta m') sp
  where
    go :: Spine -> IO ([(Maybe Core, Icit)], SpineStatus)
    go [] = return ([], OKRenaming)
    go (EApp t i : sp) = do
      (sp, status) <- go sp
      case force t of
        VVar x -> case (IM.lookup x (ren pren), status) of
          (Just x, _) ->
            return ((Just (Var $ dom pren - x - 1), i) : sp, status)
          (Nothing, OKNonRenaming) -> error "pruneFlex failure"
          (Nothing, _) -> return ((Nothing, i) : sp, NeedsPruning)
        t -> case status of
          NeedsPruning -> error "pruneFlex failure"
          _ -> do
            t <- rename pren t
            return ((Just t, i) : sp, OKNonRenaming)
    go _ = error "pruneFlex failure: eliminator in spine"

renameLevel :: PR -> VLevel -> IO Level
renameLevel pren VOmega = return Omega
renameLevel pren (VFin a) = Fin <$> rename pren a

renameClosLevel :: PR -> ClosLevel -> IO Level
renameClosLevel pren u = renameLevel (lift pren) (vinstlevel u (VVar (cod pren)))

rename :: PR -> Val -> IO Core
rename pren v = go pren v
  where
    goSp :: PR -> Core -> Spine -> IO Core
    goSp pren t [] = return t
    goSp pren t (EApp u i : sp) = App <$> goSp pren t sp <*> go pren u <*> return i
    goSp pren t (ELower : sp) = Lower <$> goSp pren t sp
    goSp pren t (EProj p : sp) = flip Proj p <$> goSp pren t sp
    goSp pren t (EPrimElim x as : sp) = do
      let h = PrimElim x
      qas <- mapM (\(v, i) -> go pren v >>= \v -> return (v, i)) as
      t' <- goSp pren t sp
      return $ case primElimPosition x of
        PEPLast -> App (foldl (\a (b, i) -> App a b i) h qas) t' (primElimIcit x)
        PEPFirst -> foldl (\a (b, i) -> App a b i) (App h t' (primElimIcit x)) qas

    go :: PR -> Val -> IO Core
    go pren t = case force t of
      VNe (HMeta m') sp | occ pren == Just m' ->
        error "occurs check failed"
      VNe (HMeta m') sp -> pruneFlex pren m' sp
      VNe (HVar x) sp -> case IM.lookup x (ren pren) of
        Nothing -> error "scope error"
        Just x' -> goSp pren (Var $ dom pren - x' - 1) sp
      VNe (HPrim x) sp -> goSp pren (Prim x) sp
      VGlobal x sp _ -> goSp pren (Global x) sp
      VAbs x i t -> Abs x i <$> go (lift pren) (vinst t (VVar (cod pren)))
      VPi x i a u1 b u2 -> Pi x i <$> go pren a <*> renameLevel pren u1 <*> go (lift pren) (vinst b (VVar (cod pren))) <*> renameLevel (lift pren) (vinstlevel u2 (VVar (cod pren)))
      VSigma x a u1 b u2 -> Sigma x <$> go pren a <*> renameLevel pren u1 <*> go (lift pren) (vinst b (VVar (cod pren))) <*> renameLevel (lift pren) (vinstlevel u2 (VVar (cod pren)))
      VPair a b -> Pair <$> go pren a <*> go pren b
      VU i -> U <$> renameLevel pren i
      VULevel -> return ULevel
      VL0 -> return L0
      VLS a -> LS <$> go pren a
      VLMax a b -> LMax <$> go pren a <*> go pren b
      VRefl -> return Refl
      VLift t -> Lift <$> go pren t
      VLiftTerm t -> LiftTerm <$> go pren t

lams :: Lvl -> Val -> Core -> Core
lams l a t = go a 0
  where
    go a l' | l' == l = t
    go a l' = case force a of
      VPi "_" i _ _ b _ -> Abs ("x" ++ show l') i $ go (vinst b (VVar l')) (l' + 1)
      VPi x i a _ b _ -> Abs x i $ go (vinst b (VVar l')) (l' + 1)
      _ -> error "impossible"

solveWithPR :: MetaVar -> (PR, Maybe Pruning) -> Val -> IO ()
solveWithPR m (pren, pruneNonLinear) rhs = do
  let (cty, mty) = getUnsolved m
  
  case pruneNonLinear of
    Nothing -> return ()
    Just pr -> () <$ pruneTy (revPruning pr) mty
  
  rhs <- rename (pren {occ = Just m}) rhs
  let solution = lams (dom pren) mty rhs
  let solutionv = eval [] solution
  let deps = S.union (allMetas solution) (allMetas cty) 
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved deps cty mty solution solutionv)

solve :: Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  pren <- invert gamma sp
  solveWithPR m pren rhs

unifyLift :: Lvl -> Clos -> Clos -> IO ()
unifyLift k c c' = let v = vvar k in unify (k + 1) (vinst c v) (vinst c' v)

unifyElim :: Lvl -> Elim -> Elim -> IO ()
unifyElim k (EApp v i) (EApp v' i') = unify k v v'
unifyElim k ELower ELower = return ()
unifyElim k (EProj p) (EProj p') | eqvProj p p' = return ()
unifyElim k (EPrimElim x as) (EPrimElim x' as') | x == x' =
  go (map fst as) (map fst as')
  where
    go :: [Val] -> [Val] -> IO ()
    go [] [] = return ()
    go (v : sp) (v' : sp') = unify k v v' >> go sp sp'
    go _ _ = error "prim elim args mismatch"
unifyElim _ _ _ = error "elim mismatch"

unifySpProj :: Lvl -> Spine -> Spine -> Ix -> IO ()
unifySpProj k sp sp' 0 = unifySp k sp sp'
unifySpProj k (EProj Snd : sp) sp' n = unifySpProj k sp sp' (n - 1)
unifySpProj _ _ _ _ = error "spine proj mismatch"

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp k [] [] = return ()
unifySp k (EProj Fst : sp) (EProj (PNamed j n) : sp') = unifySpProj k sp sp' n
unifySp k (EProj (PNamed j n) : sp) (EProj Fst : sp') = unifySpProj k sp' sp n
unifySp k (t : sp) (t' : sp') = unifySp k sp sp' >> unifyElim k t t'
unifySp _ _ _ = error "spine mismatch"

flexFlex :: Lvl -> MetaVar -> Spine -> MetaVar -> Spine -> IO ()
flexFlex gamma m sp m' sp' = if length sp < length sp' then go m' sp' m sp else go m sp m' sp'
  where
    go :: MetaVar -> Spine -> MetaVar -> Spine -> IO ()
    go m sp m' sp' = try (invert gamma sp) >>= \case
      Left (e :: SomeException) -> solve gamma m' sp' (VNe (HMeta m) sp)
      Right pren -> solveWithPR m pren (VNe (HMeta m') sp')

intersect :: Lvl -> MetaVar -> Spine -> Spine -> IO ()
intersect l m sp sp' = case go sp sp' of
  Nothing -> unifySp l sp sp'
  Just pr | Nothing `elem` pr -> () <$ pruneMeta pr m
  Just _ -> return ()
  where
    go :: Spine -> Spine -> Maybe Pruning
    go [] [] = Just []
    go (EApp t i : sp) (EApp t' _ : sp') =
      case (force t, force t') of
        (VVar x, VVar x') -> ((i <$ guard (x == x')) :) <$> go sp sp'
        _ -> Nothing
    go _ _ = error "impossible"

unifyLevel :: Lvl -> VLevel -> VLevel -> IO ()
unifyLevel k VOmega VOmega = return ()
unifyLevel k (VFin a) (VFin b) = unify k a b
unifyLevel k a b = error $ "level unification failed: " ++ show (quoteLevel k a) ++ " ~ " ++ show (quoteLevel k b)

unifyLiftLevel :: Lvl -> ClosLevel -> ClosLevel -> IO ()
unifyLiftLevel k c c' = let v = vvar k in unifyLevel (k + 1) (vinstlevel c v) (vinstlevel c' v)

unify :: Lvl -> Val -> Val -> IO ()
unify k a b = -- trace ("unify " ++ show (quote k a) ++ " ~ " ++ show (quote k b)) $ do
  case (force a, force b) of
    (VU l1, VU l2) -> unifyLevel k l1 l2
    (VULevel, VULevel) -> return ()
    (VL0, VL0) -> return ()
    (VLS a, VLS b) -> unify k a b
    (VLMax a b, VLMax a' b') -> unify k a a' >> unify k b b'
    (VLift t1, VLift t2) -> unify k t1 t2
    (VLiftTerm t1, VLiftTerm t2) -> unify k t1 t2
    (VPi _ i t u1 b u2, VPi _ i' t' u3 b' u4) | i == i' ->
      unify k t t' >> unifyLevel k u1 u3 >> unifyLift k b b' >> unifyLiftLevel k u2 u4
    (VSigma _ t u1 b u2, VSigma _ t' u3 b' u4) ->
      unify k t t' >> unifyLevel k u1 u3 >> unifyLift k b b' >> unifyLiftLevel k u2 u4
    (VAbs _ i  b, VAbs _ i' b') -> unifyLift k b b'
    (VAbs _ i b, x) -> let v = vvar k in unify (k + 1) (vinst b v) (vapp x v i)
    (x, VAbs _ i b) -> let v = vvar k in unify (k + 1) (vapp x v i) (vinst b v)
    (VPair a b, VPair c d) -> unify k a c >> unify k b d
    (VPair a b, x) -> unify k a (vfst x) >> unify k b (vsnd x)
    (x, VPair a b) -> unify k (vfst x) a >> unify k (vsnd x) b

    (VNe (HMeta m) sp, VNe (HMeta m') sp') | m == m' -> intersect k m sp sp'
    (VNe (HMeta m) sp, VNe (HMeta m') sp') -> flexFlex k m sp m' sp'
    (VNe h sp, VNe h' sp') | h == h' -> unifySp k sp sp'
    
    (VNe (HPrim PUnit) [], v) -> return ()
    (v, VNe (HPrim PUnit) []) -> return ()
    
    (VRefl, v) -> return () -- is this safe?
    (v, VRefl) -> return () -- is this safe?

    (VNe (HMeta m) sp, t) -> solve k m sp t
    (t, VNe (HMeta m) sp) -> solve k m sp t

    (VGlobal x sp v, VGlobal x' sp' v') | x == x' ->
      catch (unifySp k sp sp') $ \(_ :: SomeException) -> unify k v v'
    (VGlobal _ _ v, VGlobal _ _ v') -> unify k v v'
    (VGlobal _ _ v, v') -> unify k v v'
    (v, VGlobal _ _ v') -> unify k v v'
    (_, _) -> error $ "failed to unify: " ++ show (quote k a) ++ " ~ " ++ show (quote k b)
