module Unification (unify) where

import Common
import Core
import Val
import Evaluation
import Metas

import qualified Data.IntMap as IM
import Data.IORef
import Control.Exception (catch, SomeException)

data PR = PR {
  dom :: Lvl,
  cod :: Lvl,
  ren :: IM.IntMap Lvl
}

lift :: PR -> PR
lift (PR dom cod ren) = PR (dom + 1) (cod + 1) (IM.insert cod dom ren)

invert :: Lvl -> Spine -> IO PR
invert gamma sp = do
  (dom, ren) <- go sp
  return $ PR dom gamma ren
  where
    go :: Spine -> IO (Lvl, IM.IntMap Lvl)
    go [] = return (0, mempty)
    go (EApp t : sp) = do
      (dom, ren) <- go sp
      case force t of
        VVar x | IM.notMember x ren -> return (dom + 1, IM.insert x dom ren)
        _ -> error "failed to unify"
    go (_ : sp) = error "elim in spine"

rename :: MetaVar -> PR -> Val -> IO Core
rename m pren v = go pren v
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
      VNe (HMeta m') sp | m == m' -> error "occurs check failed"
      VNe (HMeta m') sp -> goSp pren (Meta m') sp
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

lams :: Lvl -> Core -> Core
lams l = go 0
  where
    go x t | x == l = t
    go x t = Abs ("x" ++ show x) $ go (x + 1) t

solve :: Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  pren <- invert gamma sp
  rhs <- rename m pren rhs
  let core = lams (dom pren) rhs
  let deps = allMetas core
  let solution = eval [] core
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved deps core solution)

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
