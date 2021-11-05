module Val where

import Common
import Core

-- context for global definitions, it's in here because of cyclic modules
data GlobalEntry = GlobalEntry {
  gname :: Name,
  gcore :: Core,
  gtype :: Core,
  gval :: Val,
  gvtype :: Val
}

type GlobalCtx = [GlobalEntry]

getGlobal :: GlobalCtx -> Name -> Maybe GlobalEntry
getGlobal gs x = go gs
  where
    go [] = Nothing
    go (e : ts) | gname e == x = return e
    go (_ : ts) = go ts
-- globals end

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
  | VGlobal Name ULvl Spine Val
  | VAbs Name Val Clos
  | VPi Name Val Clos
  | VSigma Name Val Clos
  | VPair Val Val Val
  | VU ULvl

vvar :: Lvl -> Val
vvar k = VNe k []

vinst :: GlobalCtx -> Clos -> Val -> Val
vinst gs (Clos e c) v = eval gs (v : e) c
vinst _ (Fun f) v = f v

vapp :: GlobalCtx -> Val -> Val -> Val
vapp gs (VAbs _ _ b) v = vinst gs b v
vapp gs (VNe h sp) v = VNe h (EApp v : sp)
vapp gs (VGlobal x l sp w) v = VGlobal x l (EApp v : sp) (vapp gs w v)
vapp _ _ _ = undefined

vproj :: Val -> ProjType -> Val
vproj (VPair a b _) Fst = a
vproj (VPair a b _) Snd = b
vproj (VNe h sp) p = VNe h (EProj p : sp)
vproj (VGlobal x l sp v) p = VGlobal x l (EProj p : sp) (vproj v p)
vproj _ _ = undefined

vfst :: Val -> Val
vfst v = vproj v Fst

vsnd :: Val -> Val
vsnd v = vproj v Snd

force :: Val -> Val
force (VGlobal _ _ _ v) = v
force v = v

eval :: GlobalCtx -> Env -> Core -> Val
eval gs e (Var i) = e !! i
eval gs e (Global x l) =
  case getGlobal gs x of
    Just e | l == 0 -> VGlobal x 0 [] $ gval e
    Just e -> VGlobal x l [] $ eval gs [] (liftUniv l (gcore e))
    Nothing -> undefined
eval gs e (App f a) = vapp gs (eval gs e f) (eval gs e a)
eval gs e (Abs x t b) = VAbs x (eval gs e t) (Clos e b)
eval gs e (Pi x t b) = VPi x (eval gs e t) (Clos e b)
eval gs e (Sigma x t b) = VSigma x (eval gs e t) (Clos e b)
eval gs e (Pair a b t) = VPair (eval gs e a) (eval gs e b) (eval gs e t)
eval gs e (Proj t p) = vproj (eval gs e t) p
eval gs e (U l) = VU l
eval gs e (Let x t v b) = eval gs (eval gs e v : e) b

quoteHead :: Lvl -> Head -> Core
quoteHead k l = Var (k - l - 1)

quoteElim :: GlobalCtx -> Lvl -> Elim -> Core -> Core
quoteElim gs k (EApp v) t = App t (quote gs k v)
quoteElim gs k (EProj p) t = Proj t p

quoteClos :: GlobalCtx -> Lvl -> Clos -> Core
quoteClos gs k c = quote gs (k + 1) $ vinst gs c (vvar k)

quote :: GlobalCtx -> Lvl -> Val -> Core
quote gs k (VU l) = U l
quote gs k (VNe h sp) = foldr (quoteElim gs k) (quoteHead k h) sp
quote gs k (VGlobal x l sp _) = foldr (quoteElim gs k) (Global x l) sp -- TODO: unfold parameter
quote gs k (VAbs x t b) = Abs x (quote gs k t) (quoteClos gs k b)
quote gs k (VPi x t b) = Pi x (quote gs k t) (quoteClos gs k b)
quote gs k (VSigma x t b) = Sigma x (quote gs k t) (quoteClos gs k b)
quote gs k (VPair a b t) = Pair (quote gs k a) (quote gs k b) (quote gs k t)

nf :: GlobalCtx -> Core -> Core
nf gs = quote gs 0 . eval gs []

convLift :: GlobalCtx -> Lvl -> Clos -> Clos -> Bool
convLift gs k c c' = let v = vvar k in conv gs (k + 1) (vinst gs c v) (vinst gs c' v)

convElim :: GlobalCtx -> Lvl -> Elim -> Elim -> Bool
convElim gs k (EApp v) (EApp v') = conv gs k v v'
convElim gs k (EProj p) (EProj p') = p == p'
convElim gs k _ _ = False

conv :: GlobalCtx -> Lvl -> Val -> Val -> Bool
conv gs k (VU l1) (VU l2) | l1 == l2 = True
conv gs k (VPi _ t b) (VPi _ t' b') = conv gs k t t' && convLift gs k b b'
conv gs k (VSigma _ t b) (VSigma _ t' b') = conv gs k t t' && convLift gs k b b'
conv gs k (VAbs _ _ b) (VAbs _ _ b') = convLift gs k b b'
conv gs k (VAbs _ _ b) x = let v = vvar k in conv gs (k + 1) (vinst gs b v) (vapp gs x v)
conv gs k x (VAbs _ _ b) = let v = vvar k in conv gs (k + 1) (vapp gs x v) (vinst gs b v)
conv gs k (VPair a b _) (VPair c d _) = conv gs k a c && conv gs k b d
conv gs k (VPair a b _) x = conv gs k a (vfst x) && conv gs k b (vsnd x)
conv gs k x (VPair a b _) = conv gs k (vfst x) a && conv gs k (vsnd x) b
conv gs k (VNe h sp) (VNe h' sp') | h == h' = and $ zipWith (convElim gs k) sp sp'
conv gs k (VGlobal x l sp v) (VGlobal x' l' sp' v') | x == x' && l == l' =
  and (zipWith (convElim gs k) sp sp') || conv gs k v v'
conv gs k (VGlobal _ _ _ v) (VGlobal _ _ _ v') = conv gs k v v'
conv gs k (VGlobal _ _ _ v) v' = conv gs k v v'
conv gs k v (VGlobal _ _ _ v') = conv gs k v v'
conv gs k _ _ = False
