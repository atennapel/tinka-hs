module Unification (unify, unifyLevel, unifyFinLevel) where

import qualified Data.IntMap as IM
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Coerce (coerce)
import Control.Exception (throwIO, catch)
import Control.Monad (zipWithM_)
import Data.Maybe (fromJust)

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
  ren :: IM.IntMap Lvl,
  apx :: M.Map (Either PrimName Name) Lvl
}

lift :: PR -> PR
lift (PR dom cod ren approx) = PR (dom + 1) (cod + 1) (IM.insert (coerce cod) dom ren) approx

invert :: Lvl -> Sp -> IO PR
invert gamma sp = do
  (dom, ren, approx) <- go sp
  return $ PR dom gamma ren approx
  where
    go :: Sp -> IO (Lvl, IM.IntMap Lvl, M.Map (Either PrimName Name) Lvl)
    go [] = return (0, mempty, mempty)
    go (EApp t _ : sp) = do
      (dom, ren, approx) <- go sp
      case forceMetas t of
        VVar (Lvl x) | IM.notMember x ren -> return (dom + 1, IM.insert x dom ren, approx)
        VVar x -> throwIO $ UnifyError $ "duplicate var in spine: " ++ show x

        -- approx solutions
        VGlobal x [] _ | M.notMember (Right x) approx -> return (dom + 1, ren, M.insert (Right x) dom approx)
        VGlobal x [] _ -> throwIO $ UnifyError $ "duplicate global in spine: " ++ x
        VPrim x | M.notMember (Left x) approx -> return (dom + 1, ren, M.insert (Left x) dom approx)
        VPrim x -> throwIO $ UnifyError $ "duplicate primitive in spine: " ++ show x

        _ -> throwIO $ UnifyError $ "non-var application in spine"
    go (EAppLvl (VFL 0 xs ys) : sp) = do
      (dom, ren, approx) <- go sp
      let lvls = IM.keys xs
      if IM.null ys && length lvls == 1 then do
        let x = head lvls
        if IM.notMember x ren then
          return (dom + 1, IM.insert x dom ren, approx)
        else
          throwIO $ UnifyError $ "duplicate var in spine: " ++ show x
      else
        throwIO $ UnifyError $ "complex level application in spine"
    go (_ : sp) = throwIO $ UnifyError $ "non-var in spine"

rename :: MetaVar -> PR -> Val -> IO Tm
rename m pren v = go pren v
  where
    goVar :: PR -> Lvl -> IO Ix
    goVar pren x = case IM.lookup (coerce x) (ren pren) of
      Nothing -> throwIO $ UnifyError $ "escaping variable '" ++ show x
      Just x' -> return $ lvlToIx (dom pren) x'

    goFinLevel :: PR -> VFinLevel -> IO FinLevel
    goFinLevel pren (VFL n xs ys) = do
      IM.foldlWithKey (\i x n -> do
        i' <- i
        return $ flmax i' (addToFinLevel n (FLMeta (LMetaVar x)))) vars ys
      where
        vars = IM.foldlWithKey
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
        PEPThird -> case qas of
          (a : b : rest) -> foldl app (App (app (app (Prim (Right x)) a) b) t (primElimIcit x)) rest
          _ -> undefined
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
    go pren t = case forceMetas t of
      VNe (HMeta m') sp | m == m' -> throwIO $ UnifyError $ "occurs check failed ?" ++ show m
      VNe (HMeta m') sp -> goSp pren (Meta m') sp
      VNe (HVar x) sp -> do
        t <- Var <$> goVar pren x
        goSp pren t sp
      VNe (HPrim x) sp ->
        case M.lookup (Left x) (apx pren) of
          Just x' -> goSp pren (Var $ lvlToIx (dom pren) x') sp
          Nothing -> goSp pren (Prim (Left x)) sp
      VGlobal x sp _ ->
        case M.lookup (Right x) (apx pren) of
          Just x' -> goSp pren (Var $ lvlToIx (dom pren) x') sp
          Nothing -> goSp pren (Global x) sp
      VLam x i b -> Lam x i <$> goLift pren b
      VPi x i t u1 b u2 -> Pi x i <$> go pren t <*> goLevel pren u1 <*> goLift pren b <*> goLevel pren u2
      VLamLvl x b -> LamLvl x <$> goLiftLevel pren b
      VPiLvl x b u -> PiLvl x <$> goLiftLevel pren b <*> goLevel (lift pren) (vinstCL u (vFinLevelVar (cod pren)))
      VPair a b -> Pair <$> go pren a <*> go pren b
      VSigma x t u1 b u2 -> Sigma x <$> go pren t <*> goLevel pren u1 <*> goLift pren b <*> goLevel pren u2
      VLabelLit x -> return $ LabelLit x
      VRefl -> return Refl
      VType i -> Type <$> goLevel pren i

lams :: Sp -> Tm -> Tm
lams sp t = go 0 (reverse sp)
  where
    go :: Int -> Sp -> Tm
    go _ [] = t
    go l (EApp _ i : sp) = Lam ("x" ++ show l) i $ go (l + 1) sp
    go l (EAppLvl _ : sp) = LamLvl ("x" ++ show l) $ go (l + 1) sp
    go _ _ = undefined

solve :: Lvl -> MetaVar -> Sp -> Val -> IO ()
solve gamma m sp rhs = do
  debug $ "solve ?" ++ show m ++ "[...] := " ++ show (quote gamma rhs)
  pren <- invert gamma sp
  rhs <- rename m pren rhs
  let solution = lams sp rhs
  debug $ "solution: " ++ show solution
  solveMeta m (eval [] solution) solution

unifyElim :: Lvl -> Elim -> Elim -> IO ()
unifyElim k (EApp v _) (EApp v' _) = unify k v v'
unifyElim k (EAppLvl l) (EAppLvl l') = unifyFinLevel k l l'
unifyElim k (EProj p) (EProj p') | eqvProj p p' = return ()
unifyElim k (EPrimElim x1 as1) (EPrimElim x2 as2) | x1 == x2 =
  zipWithM_ (go k) as1 as2
  where
    go _ (Left l) (Left l') = unifyFinLevel k l l'
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
unify l a b = do
  debug $ "unify " ++ show (quote l a) ++ " ~ " ++ show (quote l b)
  case (forceMetas a, forceMetas b) of
    (VType i, VType i') -> unifyLevel l i i'

    (VLabelLit x, VLabelLit y) | x == y -> return ()

    (VPi _ i t u1 b u2, VPi _ i' t' u1' b' u2') | i == i' ->
      unifyLevel l u1 u1' >> unify l t t' >> unifyLevel l u2 u2' >> unifyClos l b b'
    (VPiLvl _ b u, VPiLvl _ b' u') ->
      (let v = vFinLevelVar l in unifyLevel (l + 1) (vinstCL u v) (vinstCL u' v)) >> unifyClosLevel l b b'
    (VSigma _ t u1 b u2, VSigma _ t' u1' b' u2') ->
      unifyLevel l u1 u1' >> unify l t t' >> unifyLevel l u2 u2' >> unifyClos l b b'

    (VLam _ _ b, VLam _ _ b') -> unifyClos l b b'
    (VLam _ i b, b') -> let v = VVar l in unify (l + 1) (vinst b v) (vapp b' v i)
    (b', VLam _ i b) -> let v = VVar l in unify (l + 1) (vapp b' v i) (vinst b v)
    
    (VLamLvl _ b, VLamLvl _ b') -> unifyClosLevel l b b'
    (VLamLvl _ b, b') -> let v = vFinLevelVar l in unify (l + 1) (vinstLevel b v) (vappLevel b' v)
    (b', VLamLvl _ b) -> let v = vFinLevelVar l in unify (l + 1) (vappLevel b' v) (vinstLevel b v)

    (VPair a b, VPair c d) -> unify l a c >> unify l b d
    (VPair a b, x) -> unify l a (vfst x) >> unify l b (vsnd x)
    (x, VPair a b) -> unify l (vfst x) a >> unify l (vsnd x) b

    (VLiftTerm lv k a x, y) -> unify l x (vlower lv k a y)
    (y, VLiftTerm lv k a x) -> unify l (vlower lv k a y) x

    (VNe (HMeta m) sp, t) -> solve l m sp t
    (t, VNe (HMeta m) sp) -> solve l m sp t

    (VRefl, v) -> return ()
    (v, VRefl) -> return ()

    (VTZ _ VENil, v) -> return ()
    (v, VTZ _ VENil) -> return ()

    (VNe h sp, VNe h' sp') | h == h' -> unifySp l sp sp'

    (VGlobal x sp v, VGlobal x' sp' v') | x == x' ->
      catch (unifySp l sp sp') $ \(_ :: Error) -> unify l v v'
    (VGlobal _ _ v, VGlobal _ _ v') -> unify l v v'
    (VGlobal _ _ v, v') -> unify l v v'
    (v, VGlobal _ _ v') -> unify l v v'

    _ -> throwIO $ UnifyError $ "failed to unify " ++ show (quote l a) ++ " ~ " ++ show (quote l b)

-- level unification
solveFinLevel :: Lvl -> LMetaVar -> VFinLevel -> IO ()
solveFinLevel l m b@(VFL n xs ys) = do
  debug $ "solveLevel (" ++ show l ++ ") ?l" ++ show m ++ " := " ++ show (quoteFinLevel l b)
  case lookupLMeta m of
    LSolved a -> unifyFinLevel l a b
    LUnsolved gamma scope -> do
      debug $ "?l" ++ show m ++ " " ++ show gamma ++ " " ++ show scope ++ " " ++ show (IM.keys xs)
      throwUnless (IM.notMember (coerce m) ys) $ UnifyError $ "occurs check failed in level: ?l" ++ show m ++ " := " ++ show (quoteFinLevel l b)
      throwUnless (all (\x -> S.member (coerce x) scope) (IM.keys xs)) $ UnifyError $ "scope check failed in level: ?l" ++ show m ++ " := " ++ show (quoteFinLevel l b)
      debug $ "solution: " ++ show (quoteFinLevel gamma b)
      solveLMeta m b

unifyFinLevel :: Lvl -> VFinLevel -> VFinLevel -> IO ()
unifyFinLevel l a b = do
  debug $ "unifyFinLevel (" ++ show l ++ ") " ++ show (quoteFinLevel l a) ++ " ~ " ++ show (quoteFinLevel l b)
  case (forceFinLevel a, forceFinLevel b) of
    (a, b) | a == b -> return ()
    (a, b) ->
      case (isMeta a, isMeta b, a, b) of
        (Just (m, 0), _, _, _) -> solveFinLevel l m b
        (_, Just (m, 0), _, _) -> solveFinLevel l m a
        (Just (m, n), Just (m', n'), _, _) | n' >= n ->
          solveFinLevel l m (VFL 0 mempty (IM.singleton (coerce m') (n' - n)))
        (Just (m, n), Nothing, _, VFL 0 xs ys) | all (>= n) (IM.elems xs) && all (>= n) (IM.elems ys) ->
          solveFinLevel l m (subVFinLevel n b)
        (Just (m, n), Nothing, _, VFL n' xs ys) | n' >= n && all (>= n) (IM.elems xs) && all (>= n) (IM.elems ys) ->
          solveFinLevel l m (subVFinLevel n b)
        (Nothing, Just (m, n), VFL 0 xs ys, _) | all (>= n) (IM.elems xs) && all (>= n) (IM.elems ys) ->
          solveFinLevel l m (subVFinLevel n a)
        (Nothing, Just (m, n), VFL n' xs ys, _) | n' >= n && all (>= n) (IM.elems xs) && all (>= n) (IM.elems ys) ->
          solveFinLevel l m (subVFinLevel n a)
        (_, _, VFL 0 xs ys, VFL 0 xs' ys') | IM.null xs && IM.null ys && IM.null xs' && all (== 0) (IM.elems ys') ->
          mapM_ (\m -> solveFinLevel l (LMetaVar m) mempty) (IM.keys ys')
        (_, _, VFL 0 xs' ys', VFL 0 xs ys) | IM.null xs && IM.null ys && IM.null xs' && all (== 0) (IM.elems ys') ->
          mapM_ (\m -> solveFinLevel l (LMetaVar m) mempty) (IM.keys ys')
        (_, _, VFL 0 xs ys, VFL 0 xs' ys') -> do
          let m = minimum (IM.elems xs ++ IM.elems ys ++ IM.elems xs' ++ IM.elems ys')
          if m > 0 then
            unifyFinLevel l (subVFinLevel m a) (subVFinLevel m b)
          else
            throwIO $ UnifyError $ "failed to unify " ++ show (quoteFinLevel l a) ++ " ~ " ++ show (quoteFinLevel l b)
        (_, _, VFL n xs ys, VFL n' xs' ys') -> do
          let m = minimum ([n] ++ IM.elems xs ++ IM.elems ys ++ [n'] ++ IM.elems xs' ++ IM.elems ys')
          if m > 0 then
            unifyFinLevel l (subVFinLevel m a) (subVFinLevel m b)
          else
            throwIO $ UnifyError $ "failed to unify " ++ show (quoteFinLevel l a) ++ " ~ " ++ show (quoteFinLevel l b)
      where
        isMeta :: VFinLevel -> Maybe (LMetaVar, Int)
        isMeta (VFL 0 xs ys) | IM.null xs =
          let ks = IM.keys ys in
          if length ks == 1 then
            let k = head ks in
            Just (LMetaVar k, fromJust $ IM.lookup k ys)
          else
            Nothing
        isMeta _ = Nothing

unifyLevel :: Lvl -> VLevel -> VLevel -> IO ()
unifyLevel l a b = do
  debug $ "unifyLevel (" ++ show l ++ ") " ++ show (quoteLevel l a) ++ " ~ " ++ show (quoteLevel l b)
  case (forceLevel a, forceLevel b) of
    (VOmega1, VOmega1) -> return ()
    (VOmega, VOmega) -> return ()
    (VFinLevel f, VFinLevel f') -> unifyFinLevel l f f'
    (a, b) -> throwIO $ UnifyError $ "failed to unify " ++ show (quoteLevel l a) ++ " ~ " ++ show (quoteLevel l b)
