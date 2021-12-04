module Evaluation where

import Data.Either (fromLeft, fromRight)
import Data.Coerce (coerce)
import qualified Data.IntMap as M

import Common
import Core
import Levels
import Val

-- eval
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

vapp :: Val -> Val -> Val
vapp (VLam _ b) v = vinst b v
vapp (VNe h sp) v = VNe h (EApp v : sp)
vapp _ _ = undefined

vappLevel :: Val -> VFinLevel -> Val
vappLevel (VLamLvl _ b) v = vinstLevel b v
vappLevel (VNe h sp) v = VNe h (EAppLvl v : sp)
vappLevel _ _ = undefined

eval :: Env -> Tm -> Val
eval e = \case
  Var i -> fromRight undefined (e !! coerce i)
  App a b -> vapp (eval e a) (eval e b)
  Lam x b -> VLam x (Clos e b)
  Pi x t b -> VPi x (eval e t) (Clos e b)
  AppLvl t l -> vappLevel (eval e t) (finLevel e l)
  LamLvl x b -> VLamLvl x (Clos e b)
  PiLvl x b -> VPiLvl x (Clos e b)
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

quoteElim :: Lvl -> Elim -> Tm -> Tm
quoteElim l (EApp v) t = App t (quote l v)
quoteElim l (EAppLvl k) t = AppLvl t (quoteFinLevel l k)

quote :: Lvl -> Val -> Tm
quote l = \case
  VNe h sp -> foldr (quoteElim l) (quoteHead l h) sp
  VLam x b -> Lam x (quote (l + 1) (vinst b (VVar l)))
  VPi x t b -> Pi x (quote l t) (quote (l + 1) (vinst b (VVar l)))
  VLamLvl x b -> LamLvl x (quote (l + 1) (vinstLevel b (vFinLevelVar l)))
  VPiLvl x b -> PiLvl x (quote (l + 1) (vinstLevel b (vFinLevelVar l)))
  VType i -> Type (quoteLevel l i)

nf :: Tm -> Tm
nf = quote 0 . eval []

-- conv
convElim :: Lvl -> Elim -> Elim -> Bool
convElim l (EApp v) (EApp v') = conv l v v'
convElim l (EAppLvl k) (EAppLvl k') = k == k'
convElim _ _ _ = False

convClos :: Lvl -> Clos Val -> Clos Val -> Bool
convClos l b b' = let v = VVar l in conv (l + 1) (vinst b v) (vinst b' v)

convClosLevel :: Lvl -> Clos VFinLevel -> Clos VFinLevel -> Bool
convClosLevel l b b' = let v = vFinLevelVar l in conv (l + 1) (vinstLevel b v) (vinstLevel b' v)

conv :: Lvl -> Val -> Val -> Bool
conv l a b = case (a, b) of
  (VType i, VType i') -> i == i'

  (VPi _ t b, VPi _ t' b') -> conv l t t' && convClos l b b'
  (VPiLvl _ b, VPiLvl _ b') -> convClosLevel l b b'

  (VLam _ b, VLam _ b') -> convClos l b b'
  (VLam _ b, b') -> let v = VVar l in conv (l + 1) (vinst b v) (vapp b' v)
  (b', VLam _ b) -> let v = VVar l in conv (l + 1) (vapp b' v) (vinst b v)
  
  (VLamLvl _ b, VLamLvl _ b') -> convClosLevel l b b'
  (VLamLvl _ b, b') -> let v = vFinLevelVar l in conv (l + 1) (vinstLevel b v) (vappLevel b' v)
  (b', VLamLvl _ b) -> let v = vFinLevelVar l in conv (l + 1) (vappLevel b' v) (vinstLevel b v)

  (VNe h sp, VNe h' sp') | h == h' -> and $ zipWith (convElim l) sp sp'
  _ -> False
