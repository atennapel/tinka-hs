module Val where

import Common
import Core

type Head = Lvl
type Spine = [Elim]
type Env = [Val]

data Clos = Clos Env Core

newtype Elim = EApp Val

data Val
  = VNe Head Spine
  | VAbs Name Val Clos
  | VPi Name Val Clos
  | VU

vvar :: Lvl -> Val
vvar k = VNe k []

vinst :: Clos -> Val -> Val
vinst (Clos e c) v = eval (v : e) c

vapp :: Val -> Val -> Val
vapp (VAbs _ _ b) v = vinst b v
vapp (VNe h sp) v = VNe h (EApp v : sp)
vapp _ _ = undefined

eval :: Env -> Core -> Val
eval e (Var i) = e !! i
eval e (App f a) = vapp (eval e f) (eval e a)
eval e (Abs x t b) = VAbs x (eval e t) (Clos e b)
eval e (Pi x t b) = VPi x (eval e t) (Clos e b)
eval e U = VU
eval e (Let x t v b) = eval (eval e v : e) b

quoteHead :: Lvl -> Head -> Core
quoteHead k l = Var (k - l - 1)

quoteElim :: Lvl -> Elim -> Core -> Core
quoteElim k (EApp v) t = App t (quote k v)

quoteClos :: Lvl -> Clos -> Core
quoteClos k c = quote (k + 1) $ vinst c (vvar k)

quote :: Lvl -> Val -> Core
quote k VU = U
quote k (VNe h sp) = foldr (quoteElim k) (quoteHead k h) sp
quote k (VAbs x t b) = Abs x (quote k t) (quoteClos k b)
quote k (VPi x t b) = Pi x (quote k t) (quoteClos k b)

nf :: Core -> Core
nf = quote 0 . eval []

convLift :: Lvl -> Clos -> Clos -> Bool
convLift k c c' = let v = vvar k in conv (k + 1) (vinst c v) (vinst c' v)

convElim :: Lvl -> Elim -> Elim -> Bool
convElim k (EApp v) (EApp v') = conv k v v'

conv :: Lvl -> Val -> Val -> Bool
conv k VU VU = True
conv k (VPi _ t b) (VPi _ t' b') = conv k t t' && convLift k b b'
conv k (VAbs _ _ b) (VAbs _ _ b') = convLift k b b'
conv k (VAbs _ _ b) x = let v = vvar k in conv (k + 1) (vinst b v) (vapp x v)
conv k x (VAbs _ _ b) = let v = vvar k in conv (k + 1) (vapp x v) (vinst b v)
conv k (VNe h sp) (VNe h' sp') | h == h' = and $ zipWith (convElim k) sp sp'
conv k _ _ = False
