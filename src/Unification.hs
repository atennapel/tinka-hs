module Unification (unify) where

import Common
import Core
import Val
import Evaluation
import Metas

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
    go (EApp t : sp) = do
      (dom, ren, pr, isLinear) <- go sp
      case force t of
        VVar x | IM.member x ren -> return (dom + 1, IM.delete x ren, Nothing : pr, False)
        VVar x -> return (dom + 1, IM.insert x dom ren, Just () : pr, isLinear)
        _ -> error "failed to unify"
    go (_ : sp) = error "elim in spine"

pruneTy :: RevPruning -> Val -> IO Core
pruneTy (RevPruning pr) a = go pr (PR Nothing 0 0 mempty) a
  where
    go :: Pruning -> PR -> Val -> IO Core
    go pr pren a = case (pr, force a) of
      ([], a) -> rename pren a
      (Just () : pr, VPi x a b) -> Pi x <$> rename pren a <*> go pr (lift pren) (vinst b (VVar (cod pren)))
      (Nothing : pr, VPi x a b) -> go pr (skip pren) (vinst b (VVar (cod pren)))
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
    NeedsPruning -> pruneMeta (map (() <$) sp) m
    OKRenaming -> case lookupMeta m of
      Unsolved _ _ -> return m
      _ -> error "impossible"
    OKNonRenaming -> case lookupMeta m of
      Unsolved _ _ -> return m
      _ -> error "impossible"
  return $ foldr (\mu t -> maybe t (App t) mu) (Meta m') sp
  where
    go :: Spine -> IO ([Maybe Core], SpineStatus)
    go [] = return ([], OKRenaming)
    go (EApp t : sp) = do
      (sp, status) <- go sp
      case force t of
        VVar x -> case (IM.lookup x (ren pren), status) of
          (Just x, _) ->
            return (Just (Var $ dom pren - x - 1) : sp, status)
          (Nothing, OKNonRenaming) -> error "pruneFlex failure"
          (Nothing, _) -> return (Nothing : sp, NeedsPruning)
        t -> case status of
          NeedsPruning -> error "pruneFlex failure"
          _ -> do
            t <- rename pren t
            return (Just t : sp, OKNonRenaming)
    go _ = error "pruneFlex failure: eliminator in spine"

rename :: PR -> Val -> IO Core
rename pren v = go pren v
  where
    goSp :: PR -> Core -> Spine -> IO Core
    goSp pren t [] = return t
    goSp pren t (EApp u : sp) = App <$> goSp pren t sp <*> go pren u
    goSp pren t (ELower : sp) = Lower <$> goSp pren t sp
    goSp pren t (EProj p : sp) = flip Proj p <$> goSp pren t sp
    goSp pren t (EPrimElim x l k as : sp) = do
      let h = PrimElim x l k
      qas <- mapM (go pren) as
      t' <- goSp pren t sp
      return $ case primElimPosition x of
        PEPLast -> App (foldl App h qas) t'
        PEPFirst -> foldl App (App h t') qas

    go :: PR -> Val -> IO Core
    go pren t = case force t of
      VNe (HMeta m') sp | occ pren == Just m' ->
        error "occurs check failed"
      VNe (HMeta m') sp -> pruneFlex pren m' sp
      VNe (HVar x) sp -> case IM.lookup x (ren pren) of
        Nothing -> error "scope error"
        Just x' -> goSp pren (Var $ dom pren - x' - 1) sp
      VNe (HPrim x l) sp -> goSp pren (Prim x l) sp
      VGlobal x l sp _ -> goSp pren (Global x l) sp
      VAbs x t -> Abs x <$> go (lift pren) (vinst t (VVar (cod pren)))
      VPi x a b -> Pi x <$> go pren a <*> go (lift pren) (vinst b (VVar (cod pren)))
      VSigma x a b -> Sigma x <$> go pren a <*> go (lift pren) (vinst b (VVar (cod pren)))
      VPair a b -> Pair <$> go pren a <*> go pren b
      VU i -> return $ U i
      VRefl -> return Refl
      VLift t -> Lift <$> go pren t
      VLiftTerm t -> LiftTerm <$> go pren t
      VCon t -> Con <$> go pren t

lams :: Lvl -> Val -> Core -> Core
lams l a t = go a 0
  where
    go a l' | l' == l = t
    go a l' = case force a of
      VPi "_" a b -> Abs ("x" ++ show l') $ go (vinst b (VVar l')) (l' + 1)
      VPi x a b -> Abs x $ go (vinst b (VVar l')) (l' + 1)
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
unifyElim k (EApp v) (EApp v') = unify k v v'
unifyElim k ELower ELower = return ()
unifyElim k (EProj p) (EProj p') | p == p' = return ()
unifyElim k (EPrimElim x l1 l1' as) (EPrimElim x' l2 l2' as') | x == x' && l1 == l2 && l1' == l2' =
  go as as'
  where
    go :: [Val] -> [Val] -> IO ()
    go [] [] = return ()
    go (v : sp) (v' : sp') = unify k v v' >> go sp sp'
    go _ _ = error "prim elim args mismatch"
unifyElim _ _ _ = error "elim mismatch"

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp k [] [] = return ()
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
    go (EApp t : sp) (EApp t' : sp') =
      case (force t, force t') of
        (VVar x, VVar x') -> (guard (x == x') :) <$> go sp sp'
        _ -> Nothing
    go _ _ = error "impossible"

unify :: Lvl -> Val -> Val -> IO ()
unify k a b = -- trace ("unify " ++ show (quote k a) ++ " ~ " ++ show (quote k b)) $ do
  case (force a, force b) of
    (VU l1, VU l2) | l1 == l2 -> return ()
    (VLift t1, VLift t2) -> unify k t1 t2
    (VLiftTerm t1, VLiftTerm t2) -> unify k t1 t2
    (VCon t1, VCon t2) -> unify k t1 t2
    (VPi _ t b, VPi _ t' b') -> unify k t t' >> unifyLift k b b'
    (VSigma _ t b, VSigma _ t' b') -> unify k t t' >> unifyLift k b b'
    (VAbs _ b, VAbs _ b') -> unifyLift k b b'
    (VAbs _ b, x) -> let v = vvar k in unify (k + 1) (vinst b v) (vapp x v)
    (x, VAbs _ b) -> let v = vvar k in unify (k + 1) (vapp x v) (vinst b v)
    (VPair a b, VPair c d) -> unify k a c >> unify k b d
    (VPair a b, x) -> unify k a (vfst x) >> unify k b (vsnd x)
    (x, VPair a b) -> unify k (vfst x) a >> unify k (vsnd x) b

    (VNe (HMeta m) sp, VNe (HMeta m') sp') | m == m' -> intersect k m sp sp'
    (VNe (HMeta m) sp, VNe (HMeta m') sp') -> flexFlex k m sp m' sp'
    (VNe h sp, VNe h' sp') | h == h' -> unifySp k sp sp'
    
    (VNe (HPrim PUnit _) [], v) -> return ()
    (v, VNe (HPrim PUnit _) []) -> return ()
    
    (VRefl, v) -> return () -- is this safe?
    (v, VRefl) -> return () -- is this safe?

    (VNe (HMeta m) sp, t) -> solve k m sp t
    (t, VNe (HMeta m) sp) -> solve k m sp t

    (VGlobal x l sp v, VGlobal x' l' sp' v') | x == x' && l == l' ->
      catch (unifySp k sp sp') $ \(_ :: SomeException) -> unify k v v'
    (VGlobal _ _ _ v, VGlobal _ _ _ v') -> unify k v v'
    (VGlobal _ _ _ v, v') -> unify k v v'
    (v, VGlobal _ _ _ v') -> unify k v v'
    (_, _) -> error $ "failed to unify: " ++ show (quote k a) ++ " ~ " ++ show (quote k b)
