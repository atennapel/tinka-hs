module Evaluation where

import Data.Either (fromLeft, fromRight)
import Data.Coerce (coerce)
import Data.Bifunctor (first)
import qualified Data.IntMap as M

import Common
import Core
import Levels
import Val
import Prims

-- eval
force :: Val -> Val
force (VGlobal _ _ v) = force v
force v = v

vinst :: Clos Val -> Val -> Val
vinst (Clos e t) v = eval (Right v : e) t
vinst (Fun f) v = f v

vinstLevel :: Clos VFinLevel -> VFinLevel -> Val
vinstLevel (Clos e t) v = eval (Left v : e) t
vinstLevel (Fun f) v = f v

finLevel :: Env -> FinLevel -> VFinLevel
finLevel e = \case
  FLZ -> mempty
  FLS i -> addToVFinLevel 1 (finLevel e i)
  FLMax i j -> finLevel e i <> finLevel e j
  FLVar i -> fromLeft undefined (e !! coerce i)

level :: Env -> Level -> VLevel
level e = \case
  Omega -> VOmega
  Omega1 -> VOmega1
  FinLevel i -> VFinLevel (finLevel e i)

vapp :: Val -> Val -> Icit -> Val
vapp (VLam _ _ b) v _ = vinst b v
vapp (VNe h sp) v i = VNe h (EApp v i : sp)
vapp (VGlobal x sp w) v i = VGlobal x (EApp v i : sp) (vapp w v i)
vapp _ _ _ = undefined

vappLevel :: Val -> VFinLevel -> Val
vappLevel (VLamLvl _ b) v = vinstLevel b v
vappLevel (VNe h sp) v = VNe h (EAppLvl v : sp)
vappLevel (VGlobal x sp w) v = VGlobal x (EAppLvl v : sp) (vappLevel w v)
vappLevel _ _ = undefined

vproj :: Val -> ProjType -> Val
vproj (VPair a b) Fst = a
vproj (VPair a b) Snd = b
vproj (VPair a b) (PNamed _ 0) = a
vproj (VPair a b) (PNamed j n) = vproj b (PNamed j (n - 1))
vproj (VNe h sp) p = VNe h (EProj p : sp)
vproj (VGlobal x sp v) p = VGlobal x (EProj p : sp) (vproj v p)
vproj _ _ = undefined

vfst, vsnd :: Val -> Val
vfst v = vproj v Fst
vsnd v = vproj v Snd

eval :: Env -> Tm -> Val
eval e = \case
  Var i -> fromRight undefined (e !! coerce i)
  Global x -> undefined -- TODO
  Prim x -> undefined -- TODO
  App a b i -> vapp (eval e a) (eval e b) i
  Lam x i b -> VLam x i (Clos e b)
  Pi x i t b -> VPi x i (eval e t) (Clos e b)
  AppLvl t l -> vappLevel (eval e t) (finLevel e l)
  LamLvl x b -> VLamLvl x (Clos e b)
  PiLvl x b -> VPiLvl x (Clos e b)
  Proj t p -> vproj (eval e t) p
  Pair a b -> VPair (eval e a) (eval e b)
  Sigma x t b -> VSigma x (eval e t) (Clos e b)
  Let x _ v b -> eval (Right (eval e v) : e) b
  Type l -> VType (level e l)

-- quote
quoteFinLevel :: Lvl -> VFinLevel -> FinLevel
quoteFinLevel l (VFL n xs) =
  M.foldlWithKey
    (\i x n -> FLMax i (addToFinLevel n (FLVar (lvlToIx l (Lvl x)))))
    (addToFinLevel n FLZ)
    xs

quoteLevel :: Lvl -> VLevel -> Level
quoteLevel l = \case
  VOmega -> Omega
  VOmega1 -> Omega1
  VFinLevel i -> FinLevel (quoteFinLevel l i)

quoteHead :: Lvl -> Head -> Tm
quoteHead l (HVar k) = Var (lvlToIx l k)
quoteHead k (HPrim x) = Prim (Left x)

quoteElim :: Lvl -> Elim -> Tm -> Tm
quoteElim l (EApp v i) t = App t (quote l v) i
quoteElim l (EAppLvl k) t = AppLvl t (quoteFinLevel l k)
quoteElim l (EProj p) t = Proj t p
quoteElim l (EPrimElim x as) t =
  case primElimPosition x of
    PEPLast -> App (foldl (\a (b, i) -> App a b i) (Prim (Right x)) (map (first (quote l)) as)) t (primElimIcit x)
    PEPFirst -> foldl (\a (b, i) -> App a b i) (App (Prim (Right x)) t (primElimIcit x)) (map (first (quote l)) as)

quote :: Lvl -> Val -> Tm
quote l = \case
  VNe h sp -> foldr (quoteElim l) (quoteHead l h) sp
  VGlobal h sp v -> quote l v -- TODO
  VLam x i b -> Lam x i (quote (l + 1) (vinst b (VVar l)))
  VPi x i t b -> Pi x i (quote l t) (quote (l + 1) (vinst b (VVar l)))
  VLamLvl x b -> LamLvl x (quote (l + 1) (vinstLevel b (vFinLevelVar l)))
  VPiLvl x b -> PiLvl x (quote (l + 1) (vinstLevel b (vFinLevelVar l)))
  VPair a b -> Pair (quote l a) (quote l b)
  VSigma x t b -> Sigma x (quote l t) (quote (l + 1) (vinst b (VVar l)))
  VType i -> Type (quoteLevel l i)

nf :: Tm -> Tm
nf = quote 0 . eval []

-- conv
eqvProj :: ProjType -> ProjType -> Bool
eqvProj (PNamed _ i) (PNamed _ i') = i == i'
eqvProj Fst (PNamed _ 0) = True
eqvProj (PNamed _ 0) Fst = True
eqvProj p p' = p == p'

convElim :: Lvl -> Elim -> Elim -> Bool
convElim k (EApp v _) (EApp v' _) = conv k v v'
convElim k (EProj p) (EProj p') = eqvProj p p'
convElim k (EPrimElim x1 as1) (EPrimElim x2 as2) =
  x1 == x2 && and (zipWith (conv k) (map fst as1) (map fst as2))
convElim k _ _ = False

convSpProj :: Lvl -> Sp -> Sp -> Ix -> Bool
convSpProj k sp sp' 0 = convSp k sp sp'
convSpProj k (EProj Snd : sp) sp' n = convSpProj k sp sp' (n - 1)
convSpProj _ _ _ _ = False

convSp :: Lvl -> Sp -> Sp -> Bool
convSp k [] [] = True
convSp k (EProj Fst : sp) (EProj (PNamed j n) : sp') = convSpProj k sp sp' n
convSp k (EProj (PNamed j n) : sp) (EProj Fst : sp') = convSpProj k sp' sp n
convSp k (e : sp) (e' : sp') = convSp k sp sp' && convElim k e e'
convSp _ _ _ = False

convClos :: Lvl -> Clos Val -> Clos Val -> Bool
convClos l b b' = let v = VVar l in conv (l + 1) (vinst b v) (vinst b' v)

convClosLevel :: Lvl -> Clos VFinLevel -> Clos VFinLevel -> Bool
convClosLevel l b b' = let v = vFinLevelVar l in conv (l + 1) (vinstLevel b v) (vinstLevel b' v)

conv :: Lvl -> Val -> Val -> Bool
conv l a b = case (a, b) of
  (VType i, VType i') -> i == i'

  (VPi _ i t b, VPi _ i' t' b') | i == i' -> conv l t t' && convClos l b b'
  (VPiLvl _ b, VPiLvl _ b') -> convClosLevel l b b'
  (VSigma _ t b, VSigma _ t' b') -> conv l t t' && convClos l b b'

  (VLam _ _ b, VLam _ _ b') -> convClos l b b'
  (VLam _ i b, b') -> let v = VVar l in conv (l + 1) (vinst b v) (vapp b' v i)
  (b', VLam _ i b) -> let v = VVar l in conv (l + 1) (vapp b' v i) (vinst b v)
  
  (VLamLvl _ b, VLamLvl _ b') -> convClosLevel l b b'
  (VLamLvl _ b, b') -> let v = vFinLevelVar l in conv (l + 1) (vinstLevel b v) (vappLevel b' v)
  (b', VLamLvl _ b) -> let v = vFinLevelVar l in conv (l + 1) (vappLevel b' v) (vinstLevel b v)

  (VPair a b, VPair c d) -> conv l a c && conv l b d
  (VPair a b, x) -> conv l a (vfst x) && conv l b (vsnd x)
  (x, VPair a b) -> conv l (vfst x) a && conv l (vsnd x) b

  (VNe h sp, VNe h' sp') | h == h' -> convSp l sp sp'
  (VGlobal x sp v, VGlobal x' sp' v') | x == x' -> convSp l sp sp' || conv l v v'
  (VGlobal _ _ v, VGlobal _ _ v') -> conv l v v'
  (VGlobal _ _ v, v') -> conv l v v'
  (v, VGlobal _ _ v') -> conv l v v'
  _ -> False
