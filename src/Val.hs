module Val where

import Common
import Core

type Head = Lvl
type Spine = [Elim]
type Env = [Val]

data Clos
  = Clos Env Core
  | Fun (Val -> Val)

data Elim
  = EApp Val
  | EProj ProjType

data Val
  = VNe Head Spine
  | VAbs Name Val Clos
  | VPi Name Val Clos
  | VSigma Name Val Clos
  | VPair Val Val Val
  | VU

vvar :: Lvl -> Val
vvar k = VNe k []

vinst :: Clos -> Val -> Val
vinst (Clos e c) v = eval (v : e) c
vinst (Fun f) v = f v

vapp :: Val -> Val -> Val
vapp (VAbs _ _ b) v = vinst b v
vapp (VNe h sp) v = VNe h (EApp v : sp)
vapp _ _ = undefined

vproj :: Val -> ProjType -> Val
vproj (VPair a b _) Fst = a
vproj (VPair a b _) Snd = b
vproj (VNe h sp) p = VNe h (EProj p : sp)
vproj _ _ = undefined

eval :: Env -> Core -> Val
eval e (Var i) = e !! i
eval e (App f a) = vapp (eval e f) (eval e a)
eval e (Abs x t b) = VAbs x (eval e t) (Clos e b)
eval e (Pi x t b) = VPi x (eval e t) (Clos e b)
eval e (Sigma x t b) = VSigma x (eval e t) (Clos e b)
eval e (Pair a b t) = VPair (eval e a) (eval e b) (eval e t)
eval e (Proj t p) = vproj (eval e t) p
eval e U = VU
eval e (Let x t v b) = eval (eval e v : e) b

quoteHead :: Lvl -> Head -> Core
quoteHead k l = Var (k - l - 1)

quoteElim :: Lvl -> Elim -> Core -> Core
quoteElim k (EApp v) t = App t (quote k v)
quoteElim k (EProj p) t = Proj t p

quoteClos :: Lvl -> Clos -> Core
quoteClos k c = quote (k + 1) $ vinst c (vvar k)

quote :: Lvl -> Val -> Core
quote k VU = U
quote k (VNe h sp) = foldr (quoteElim k) (quoteHead k h) sp
quote k (VAbs x t b) = Abs x (quote k t) (quoteClos k b)
quote k (VPi x t b) = Pi x (quote k t) (quoteClos k b)
quote k (VSigma x t b) = Sigma x (quote k t) (quoteClos k b)
quote k (VPair a b t) = Pair (quote k a) (quote k b) (quote k t)

nf :: Core -> Core
nf = quote 0 . eval []

convLift :: Lvl -> Clos -> Clos -> Bool
convLift k c c' = let v = vvar k in conv (k + 1) (vinst c v) (vinst c' v)

convElim :: Lvl -> Elim -> Elim -> Bool
convElim k (EApp v) (EApp v') = conv k v v'
convElim k (EProj p) (EProj p') = p == p'
convElim k _ _ = False

conv :: Lvl -> Val -> Val -> Bool
conv k VU VU = True
conv k (VPi _ t b) (VPi _ t' b') = conv k t t' && convLift k b b'
conv k (VSigma _ t b) (VSigma _ t' b') = conv k t t' && convLift k b b'
conv k (VAbs _ _ b) (VAbs _ _ b') = convLift k b b'
conv k (VAbs _ _ b) x = let v = vvar k in conv (k + 1) (vinst b v) (vapp x v)
conv k x (VAbs _ _ b) = let v = vvar k in conv (k + 1) (vapp x v) (vinst b v)
conv k (VPair a b _) (VPair c d _) = conv k a c && conv k b d
conv k (VNe h sp) (VNe h' sp') | h == h' = and $ zipWith (convElim k) sp sp'
conv k _ _ = False
