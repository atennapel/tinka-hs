module Unification (unify) where

import qualified Data.IntMap as IM
import Data.Coerce (coerce)
import Control.Exception (throwIO, catch)
import Control.Monad (zipWithM_)

import Common
import Val
import Core
import Evaluation
import Errors
import Metas
import Levels
import Prims

data PR = PR {
  dom :: Lvl,
  cod :: Lvl,
  ren :: IM.IntMap Lvl
}

lift :: PR -> PR
lift (PR dom cod ren) = PR (dom + 1) (cod + 1) (IM.insert (coerce cod) dom ren)

invert :: Lvl -> Sp -> IO PR
invert gamma sp = do
  (dom, ren) <- go sp
  return $ PR dom gamma ren
  where
    go :: Sp -> IO (Lvl, IM.IntMap Lvl)
    go [] = return (0, mempty)
    go (EApp t _ : sp) = do
      (dom, ren) <- go sp
      case force t of
        VVar (Lvl x) | IM.notMember x ren -> return (dom + 1, IM.insert x dom ren)
        VVar x -> throwIO $ UnifyError $ "duplicate var in spine: " ++ show x
        _ -> throwIO $ UnifyError $ "non-var application in spine"
    go (EAppLvl (VFL 0 xs) : sp) = do
      (dom, ren) <- go sp
      let lvls = IM.keys xs
      if length lvls == 1 then do
        let x = head lvls
        if IM.notMember x ren then
          return (dom + 1, IM.insert x dom ren)
        else
          throwIO $ UnifyError $ "duplicate var in spine: " ++ show x
      else
        throwIO $ UnifyError $ "non-var application in spine"
    go (_ : sp) = throwIO $ UnifyError $ "non-var in spine"

rename :: MetaVar -> PR -> Val -> IO Tm
rename m pren v = go pren v
  where
    goVar :: PR -> Lvl -> IO Ix
    goVar pren x = case IM.lookup (coerce x) (ren pren) of
      Nothing -> throwIO $ UnifyError $ "escaping variable '" ++ show x
      Just x' -> return $ lvlToIx (dom pren) x'

    goFinLevel :: PR -> VFinLevel -> IO FinLevel
    goFinLevel pren (VFL n xs) =
      IM.foldlWithKey
        (\i x n -> do
          i' <- i
          v <- FLVar <$> goVar pren (Lvl x)
          return $ flmax i' (addToFinLevel n v))
        (return $ addToFinLevel n FLZ)
        xs

    goLevel :: PR -> VLevel -> IO Level
    goLevel pren VOmega = return Omega
    goLevel pren VOmega1 = return Omega1
    goLevel pren (VFinLevel l) = FinLevel <$> goFinLevel pren l

    goSp :: PR -> Tm -> Sp -> IO Tm
    goSp pren t [] = return t
    goSp pren t (EApp v i : sp) = App <$> goSp pren t sp <*> go pren v <*> return i
    goSp pren t (EAppLvl l : sp) = AppLvl <$> goSp pren t sp <*> goFinLevel pren l
    goSp pren t (EProj p : sp) = Proj <$> goSp pren t sp <*> return p
    goSp pren t (EPrimElim x as : sp) = do
      let h = Prim (Right x)
      qas <- mapM renameArg as
      t' <- goSp pren t sp
      return $ case primElimPosition x of
        PEPLast -> App (foldl app h qas) t' (primElimIcit x)
        PEPFirst -> foldl app (App h t' (primElimIcit x)) qas
      where
        renameArg :: Either VFinLevel (Val, Icit) -> IO (Either FinLevel (Tm, Icit))
        renameArg (Left l) = Left <$> goFinLevel pren l
        renameArg (Right (v, i)) = Right . (, i) <$> go pren v

        app :: Tm -> Either FinLevel (Tm, Icit) -> Tm
        app a (Left lv) = AppLvl a lv
        app a (Right (b, i)) = App a b i

    goLift :: PR -> Clos Val -> IO Tm
    goLift pren b = go (lift pren) (vinst b (VVar (cod pren)))

    goLiftLevel :: PR -> Clos VFinLevel -> IO Tm
    goLiftLevel pren b = go (lift pren) (vinstLevel b (vFinLevelVar (cod pren)))

    go :: PR -> Val -> IO Tm
    go pren t = case force t of
      VNe (HMeta m') sp | m == m' -> throwIO $ UnifyError $ "occurs check failed ?" ++ show m
      VNe (HMeta m') sp -> goSp pren (Meta m') sp
      VNe (HVar x) sp -> do
        t <- Var <$> goVar pren x
        goSp pren t sp
      VNe (HPrim x) sp -> goSp pren (Prim (Left x)) sp
      VGlobal x sp _ -> goSp pren (Global x) sp
      VLam x i b -> Lam x i <$> goLift pren b
      VPi x i t b -> Pi x i <$> go pren t <*> goLift pren b
      VLamLvl x b -> LamLvl x <$> goLiftLevel pren b
      VPiLvl x b -> PiLvl x <$> goLiftLevel pren b
      VPair a b -> Pair <$> go pren a <*> go pren b
      VSigma x t b -> Sigma x <$> go pren t <*> goLift pren b
      VType i -> Type <$> goLevel pren i

lams :: Sp -> Tm -> Tm
lams sp t = go 0 sp
  where
    go :: Int -> Sp -> Tm
    go _ [] = t
    go l (EApp _ i : sp) = Lam ("x" ++ show l) i $ go (l + 1) sp
    go l (EAppLvl _ : sp) = LamLvl ("x" ++ show l) $ go (l + 1) sp
    go _ _ = undefined

solve :: Lvl -> MetaVar -> Sp -> Val -> IO ()
solve gamma m sp rhs = do
  pren <- invert gamma sp
  rhs <- rename m pren rhs
  let solution = lams sp rhs
  solveMeta m (eval [] solution) solution

unifyElim :: Lvl -> Elim -> Elim -> IO ()
unifyElim k (EApp v _) (EApp v' _) = unify k v v'
unifyElim k (EProj p) (EProj p') | eqvProj p p' = return ()
unifyElim k (EPrimElim x1 as1) (EPrimElim x2 as2) | x1 == x2 =
  zipWithM_ (go k) as1 as2
  where
    go _ (Left l) (Left l') | l == l' = return ()
    go k (Right (v, _)) (Right (v', _)) = unify k v v'
    go _ _ _ = throwIO $ UnifyError $ "prim elim spine mismatch: " ++ show x1
unifyElim k _ _ = throwIO $ UnifyError $ "elim mismatch"

unifySpProj :: Lvl -> Sp -> Sp -> Ix -> IO ()
unifySpProj k sp sp' 0 = unifySp k sp sp'
unifySpProj k (EProj Snd : sp) sp' n = unifySpProj k sp sp' (n - 1)
unifySpProj _ _ _ _ = throwIO $ UnifyError $ "proj spine mismatch"

unifySp :: Lvl -> Sp -> Sp -> IO ()
unifySp k [] [] = return ()
unifySp k (EProj Fst : sp) (EProj (PNamed j n) : sp') = unifySpProj k sp sp' n
unifySp k (EProj (PNamed j n) : sp) (EProj Fst : sp') = unifySpProj k sp' sp n
unifySp k (e : sp) (e' : sp') = unifySp k sp sp' >> unifyElim k e e'
unifySp _ _ _ = throwIO $ UnifyError $ "spine mismatch"

unifyClos :: Lvl -> Clos Val -> Clos Val -> IO ()
unifyClos l b b' = let v = VVar l in unify (l + 1) (vinst b v) (vinst b' v)

unifyClosLevel :: Lvl -> Clos VFinLevel -> Clos VFinLevel -> IO ()
unifyClosLevel l b b' = let v = vFinLevelVar l in unify (l + 1) (vinstLevel b v) (vinstLevel b' v)

unify :: Lvl -> Val -> Val -> IO ()
unify l a b = case (a, b) of
  (VType i, VType i') | i == i' -> return ()

  (VPi _ i t b, VPi _ i' t' b') | i == i' -> unify l t t' >> unifyClos l b b'
  (VPiLvl _ b, VPiLvl _ b') -> unifyClosLevel l b b'
  (VSigma _ t b, VSigma _ t' b') -> unify l t t' >> unifyClos l b b'

  (VLam _ _ b, VLam _ _ b') -> unifyClos l b b'
  (VLam _ i b, b') -> let v = VVar l in unify (l + 1) (vinst b v) (vapp b' v i)
  (b', VLam _ i b) -> let v = VVar l in unify (l + 1) (vapp b' v i) (vinst b v)
  
  (VLamLvl _ b, VLamLvl _ b') -> unifyClosLevel l b b'
  (VLamLvl _ b, b') -> let v = vFinLevelVar l in unify (l + 1) (vinstLevel b v) (vappLevel b' v)
  (b', VLamLvl _ b) -> let v = vFinLevelVar l in unify (l + 1) (vappLevel b' v) (vinstLevel b v)

  (VPair a b, VPair c d) -> unify l a c >> unify l b d
  (VPair a b, x) -> unify l a (vfst x) >> unify l b (vsnd x)
  (x, VPair a b) -> unify l (vfst x) a >> unify l (vsnd x) b

  (VUnit, v) -> return ()
  (v, VUnit) -> return ()

  (VLiftTerm lv k a x, y) -> unify l x (vlower lv k a y)
  (y, VLiftTerm lv k a x) -> unify l (vlower lv k a y) x

  (VNe (HMeta m) sp, t) -> solve l m sp t
  (t, VNe (HMeta m) sp) -> solve l m sp t

  (VNe h sp, VNe h' sp') | h == h' -> unifySp l sp sp'
  (VGlobal x sp v, VGlobal x' sp' v') | x == x' ->
    catch (unifySp l sp sp') $ \(_ :: Error) -> unify l v v'
  (VGlobal _ _ v, VGlobal _ _ v') -> unify l v v'
  (VGlobal _ _ v, v') -> unify l v v'
  (v, VGlobal _ _ v') -> unify l v v'
  _ -> throwIO $ UnifyError $ "failed to unify " ++ show (quote l a) ++ " ~ " ++ show (quote l b)
