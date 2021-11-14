module Val where

import Common
import Core

-- import Debug.Trace (trace)

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

type Spine = [Elim]
type Env = [Val]

data Clos
  = Clos Env Core
  | Fun (Val -> Val)

data Head = HVar Lvl | HPrim PrimName ULvl
  deriving (Eq)

data Elim
  = EApp Val
  | EProj ProjType
  | EPrimElim PrimElimName ULvl ULvl [Val]
  | ELower

data Val
  = VNe Head Spine
  | VGlobal Name ULvl Spine Val
  | VAbs Name Val Clos
  | VPi Name Val Clos
  | VSigma Name Val Clos
  | VPair Val Val Val
  | VU ULvl
  | VLift Val
  | VLiftTerm Val

vpi :: Name -> Val -> (Val -> Val) -> Val
vpi x a b = VPi x a (Fun b)

vsigma :: Name -> Val -> (Val -> Val) -> Val
vsigma x a b = VSigma x a (Fun b)

vfun :: Val -> Val -> Val
vfun a b = VPi "_" a (Fun $ const b)

vpairty :: Val -> Val -> Val
vpairty a b = VSigma "_" a (Fun $ const b)

vabs :: Name -> Val -> (Val -> Val) -> Val
vabs x a b = VAbs x a (Fun b)

vvar :: Lvl -> Val
vvar k = VNe (HVar k) []

vprim :: PrimName -> ULvl -> Val
vprim x l = VNe (HPrim x l) []

vvoid, vunittype, vunit, vbool, vtrue, vfalse, vdesc, vend :: ULvl -> Val
vvoid = vprim PVoid
vunittype = vprim PUnitType
vunit = vprim PUnit
vbool = vprim PBool
vtrue = vprim PTrue
vfalse = vprim PFalse
vdesc = vprim PDesc
vend = vprim PEnd

varg :: ULvl -> Val -> Val -> Val
varg l a k = VNe (HPrim PArg l) [EApp k, EApp a]

vind :: ULvl -> Val -> Val
vind l k = VNe (HPrim PInd l) [EApp k]

vhind :: ULvl -> Val -> Val -> Val
vhind l a k = VNe (HPrim PHInd l) [EApp k, EApp a]

vcon :: ULvl -> Val -> Val -> Val
vcon l d c = VNe (HPrim PCon l) [EApp c, EApp d]

vheq :: ULvl -> Val -> Val -> Val -> Val -> Val
vheq l a b x y = VNe (HPrim PHEq l) [EApp y, EApp x, EApp b, EApp a]

vhrefl :: ULvl -> Val -> Val -> Val
vhrefl l a x = VNe (HPrim PHRefl l) [EApp x, EApp a]

vdata :: ULvl -> Val -> Val
vdata l v = VNe (HPrim PData l) [EApp v]

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

vfst, vsnd :: Val -> Val
vfst v = vproj v Fst
vsnd v = vproj v Snd

vlower :: Val -> Val
vlower (VLiftTerm v) = v
vlower (VNe h sp) = VNe h (ELower : sp)
vlower (VGlobal x l sp v) = VGlobal x l (ELower : sp) (vlower v)
vlower _ = undefined

vliftterm :: Val -> Val
vliftterm (VNe h (ELower : sp)) = VNe h sp
vliftterm (VGlobal x l (ELower : sp) v) = VGlobal x l sp (vliftterm v)
vliftterm v = VLiftTerm v

vprimelim :: GlobalCtx -> PrimElimName -> ULvl -> ULvl -> [Val] -> Val -> Val
vprimelim gs PEBool l k [p, t, f] (VNe (HPrim PTrue _) []) = t
vprimelim gs PEBool l k [p, t, f] (VNe (HPrim PFalse _) []) = f

vprimelim gs PEHEq l k [ta, a, tp, h, b] (VNe (HPrim PHRefl _) _) = h

vprimelim gs PEDesc l k [p, end, arg, ind, hind] (VNe (HPrim PEnd _) []) = end
vprimelim gs PEDesc l k [p, end, arg, ind, hind] (VNe (HPrim PArg _) [EApp kk, EApp a]) =
  vapp gs (vapp gs (vapp gs arg a) kk) (vabs "x" a $ \x -> vprimelim gs PEDesc l k [p, end, arg, ind, hind] (vapp gs kk x))
vprimelim gs PEDesc l k [p, end, arg, ind, hind] (VNe (HPrim PInd _) [EApp kk]) =
  vapp gs (vapp gs ind kk) (vprimelim gs PEDesc l k [p, end, arg, ind, hind] kk)
vprimelim gs PEDesc l k [p, end, arg, ind, hind] (VNe (HPrim PHInd _) [EApp kk, EApp a]) =
  vapp gs (vapp gs (vapp gs hind a) kk) (vprimelim gs PEDesc l k [p, end, arg, ind, hind] kk)

-- El X End^l = UnitType^(l + k)
vprimelim gs PEEl l k [x] (VNe (HPrim PEnd _) []) = vunittype (l + k)
-- El X (Arg^l A K) = (x : A) ** El X (K x)
vprimelim gs PEEl l k [x] (VNe (HPrim PArg _) [EApp kk, EApp a]) =
  vsigma "x" a $ \xx -> vprimelim gs PEEl l k [x] (vapp gs kk xx)
-- El X (Ind^l K) = X ** El X K
vprimelim gs PEEl l k [x] (VNe (HPrim PInd _) [EApp kk]) = vpairty x $ vprimelim gs PEEl l k [x] kk
-- El X (HInd^l A K) = (A -> X) ** El K X
vprimelim gs PEEl l k [x] (VNe (HPrim PHInd _) [EApp kk, EApp a]) = vpairty (vfun a x) $ vprimelim gs PEEl l k [x] kk

-- All End X P _ = UnitType
vprimelim gs PEAll l k [x, p, xs] (VNe (HPrim PEnd _) []) = vunittype (l + k)
-- All (Arg A K) X P xs = All (K (fst xs)) X P (snd xs)
vprimelim gs PEAll l k [x, p, xs] (VNe (HPrim PArg _) [EApp kk, EApp a]) =
  vprimelim gs PEAll l k [x, p, vsnd xs] (vapp gs kk (vfst xs))
-- All (Ind K) X P xs = P (fst xs) ** All K X P (snd xs)
vprimelim gs PEAll l k [x, p, xs] (VNe (HPrim PInd _) [EApp kk]) =
  vpairty (vapp gs p (vfst xs)) $ vprimelim gs PEAll l k [x, p, vsnd xs] kk
-- All (HInd A K) X P xs = ((x : A) -> P ((fst xs) x)) ** All K X P (snd xs)
vprimelim gs PEAll l k [x, p, xs] (VNe (HPrim PHInd _) [EApp kk, EApp a]) =
  vpairty (vpi "x" a $ \x -> vapp gs p (vapp gs (vfst xs) x)) $ vprimelim gs PEAll l k [x, p, vsnd xs] kk

-- all End X P p _ = Unit
vprimelim gs PEall l k [x, p, pp, xs] (VNe (HPrim PEnd _) []) = vunit (l + k)
-- all (Arg A K) X P p xs = all (K (fst xs)) X P p (snd xs)
vprimelim gs PEall l k [x, p, pp, xs] (VNe (HPrim PArg _) [EApp kk, EApp a]) =
  vprimelim gs PEall l k [x, p, pp, vsnd xs] (vapp gs kk (vfst xs))
-- all (Ind K) X P p xs = (p (fst xs), all K X P p (snd xs))
vprimelim gs PEall l k [x, p, pp, xs] d@(VNe (HPrim PInd _) [EApp kk]) =
  VPair (vapp gs pp (vfst xs)) (vprimelim gs PEall l k [x, p, pp, vsnd xs] kk) (vAll gs l k d x p xs)
-- all (HInd A K) X P p xs = (\h. p ((fst xs) h), all K X P p (snd xs))
vprimelim gs PEall l k [x, p, pp, xs] d@(VNe (HPrim PHInd _) [EApp kk, EApp a]) =
  VPair (vabs "h" a $ \h -> vapp gs p (vapp gs (vfst xs) h)) (vprimelim gs PEall l k [x, p, pp, vsnd xs] kk) (vAll gs l k d x p xs)

-- (elim Data) D P p (Con _ x) = p x (all D (Data D) P ((elim Data) D P p) x)
vprimelim gs PEData l k [d, p, pp] (VNe (HPrim PCon _) [EApp x, EApp _]) =
  vapp gs (vapp gs pp x) (vall gs l k d (vdata l d) p (vabs "y" (vdata l d) $ vprimelim gs PEData l k [d, p, pp]) x)

vprimelim gs x l k as (VNe h sp) = VNe h (EPrimElim x l k as : sp)
vprimelim gs p l k as (VGlobal x kk sp v) = VGlobal x kk (EPrimElim p l k as : sp) (vprimelim gs p l k as v)
vprimelim gs x l k as _ = undefined

vel :: GlobalCtx -> ULvl -> ULvl -> Val -> Val -> Val
vel gs l k d x = vprimelim gs PEEl l k [x] d

vAll :: GlobalCtx -> ULvl -> ULvl -> Val -> Val -> Val -> Val -> Val
vAll gs l k d x p xs = vprimelim gs PEAll l k [x, p, xs] d

vall :: GlobalCtx -> ULvl -> ULvl -> Val -> Val -> Val -> Val -> Val -> Val
vall gs l k d x p pp xs = vprimelim gs PEall l k [x, p, pp, xs] d

force :: Val -> Val
force (VGlobal _ _ _ v) = force v
force v = v

eval :: GlobalCtx -> Env -> Core -> Val
eval gs e (Var i) = e !! i
eval gs e (Global x l) =
  case getGlobal gs x of
    Just e | l == 0 -> VGlobal x 0 [] $ gval e
    Just e -> VGlobal x l [] $ eval gs [] (liftUniv l (gcore e))
    Nothing -> undefined
eval gs e (Prim x l) = vprim x l
eval gs e (PrimElim x l1 l2) = evalprimelim gs x l1 l2
eval gs e (App f a) = vapp gs (eval gs e f) (eval gs e a)
eval gs e (Abs x t b) = VAbs x (eval gs e t) (Clos e b)
eval gs e (Pi x t b) = VPi x (eval gs e t) (Clos e b)
eval gs e (Sigma x t b) = VSigma x (eval gs e t) (Clos e b)
eval gs e (Pair a b t) = VPair (eval gs e a) (eval gs e b) (eval gs e t)
eval gs e (Proj t p) = vproj (eval gs e t) p
eval gs e (U l) = VU l
eval gs e (Let x t v b) = eval gs (eval gs e v : e) b
eval gs e (Lift t) = VLift (eval gs e t)
eval gs e (LiftTerm t) = vliftterm (eval gs e t)
eval gs e (Lower t) = vlower (eval gs e t)

evalprimelim :: GlobalCtx -> PrimElimName -> ULvl -> ULvl -> Val
evalprimelim gs PEBool l k =
  vabs "P" (vfun (vbool l) (VU (l + k))) $ \p ->
  vabs "t" (vapp gs p (vtrue l)) $ \t ->
  vabs "f" (vapp gs p (vfalse l)) $ \f ->
  vabs "b" (vbool l) $ \b ->
  vprimelim gs PEBool l k [p, t, f] b
evalprimelim gs PEHEq l k =
  vabs "A" (VU l) $ \ta ->
  vabs "a" ta $ \a ->
  vabs "P" (vpi "b" ta $ \b -> vfun (vheq l ta ta a b) (VU (l + k))) $ \tp ->
  vabs "h" (vapp gs (vapp gs tp ta) (vhrefl l ta a)) $ \h ->
  vabs "b" ta $ \b ->
  vabs "p" (vheq l ta ta a b) $ \p ->
  vprimelim gs PEHEq l k [ta, a, tp, h, b] p
evalprimelim gs PEVoid l k =
  vabs "A" (VU (l + k)) $ \a ->
  vabs "v" (vvoid l) $ \v ->
  vprimelim gs PEVoid l k [a] v
evalprimelim gs PEDesc l k =
  vabs "P" (vfun (vdesc l) (VU (l + k))) $ \p ->
  vabs "end" (vapp gs p (vend l)) $ \end ->
  vabs "arg" (vpi "A" (VU l) $ \a -> vpi "K" (vfun a (vdesc l)) $ \kk -> vfun (vpi "x" a $ \x -> vapp gs p (vapp gs kk x)) (vapp gs p (varg l a kk))) $ \arg ->
  vabs "ind" (vpi "K" (vdesc l) $ \kk -> vfun (vapp gs p kk) (vapp gs p (vind l kk))) $ \ind ->
  vabs "hind" (vpi "A" (VU l) $ \a -> vpi "K" (vdesc l) $ \kk -> vfun (vapp gs p kk) (vapp gs p (vhind l a kk))) $ \hind ->
  vabs "d" (vdesc l) $ \d ->
  vprimelim gs PEDesc l k [p, end, arg, ind, hind] d
evalprimelim gs PEEl l k =
  vabs "X" (VU (l + k)) $ \x ->
  vabs "D" (vdesc l) $ \d ->
  vprimelim gs PEEl l k [x] d
evalprimelim gs PEAll l k =
  vabs "D" (vdesc l) $ \d ->
  vabs "X" (VU (l + k)) \x ->
  vabs "P" (vfun x (VU (l + k))) $ \p ->
  vabs "xs" (vel gs l k d x) $ \xs ->
  vprimelim gs PEAll l k [x, p, xs] d
evalprimelim gs PEall l k =
  vabs "D" (vdesc l) $ \d ->
  vabs "X" (VU (l + k)) $ \x ->
  vabs "P" (vfun x (VU (l + k))) $ \p ->
  vabs "p" (vpi "x" x $ \xx -> vapp gs p xx) $ \pp ->
  vabs "xs" (vel gs l k d x) $ \xs ->
  vprimelim gs PEall l k [x, p, pp, xs] d
evalprimelim gs PEData l k =
  vabs "D" (vdesc l) $ \d ->
  vabs "P" (vfun (vdata l d) (VU (l + k))) $ \p ->
  vabs "p" (
    vpi "d" (vel gs l 0 d (vdata l d)) $ \dd ->
    vfun (vAll gs l 0 d (vdata l d) p dd) $
    vapp gs p (vcon l d dd)
  ) $ \pp ->
  vabs "x" (vdata l d) $ \x ->
  vprimelim gs PEData l k [d, p, pp] x

data QuoteLevel = KeepGlobals | Full

quoteHead :: Lvl -> Head -> Core
quoteHead k (HVar l) = Var (k - l - 1)
quoteHead k (HPrim x l) = Prim x l 

quoteElim :: QuoteLevel -> GlobalCtx -> Lvl -> Elim -> Core -> Core
quoteElim ql gs k (EApp v) t = App t (quoteWith ql gs k v)
quoteElim ql gs k (EProj p) t = Proj t p
quoteElim ql gs k (EPrimElim x l1 l2 as) t =
  case primElimPosition x of
    PEPLast -> App (foldl App (PrimElim x l1 l2) (map (quoteWith ql gs k) as)) t
    PEPFirst -> foldl App (App (PrimElim x l1 l2) t) (map (quoteWith ql gs k) as)
quoteElim ql gs k ELower t = Lower t

quoteClos :: QuoteLevel -> GlobalCtx -> Lvl -> Clos -> Core
quoteClos ql gs k c = quoteWith ql gs (k + 1) $ vinst gs c (vvar k)

quoteWith :: QuoteLevel -> GlobalCtx -> Lvl -> Val -> Core
quoteWith ql gs k (VU l) = U l
quoteWith ql gs k (VNe h sp) = foldr (quoteElim ql gs k) (quoteHead k h) sp
quoteWith ql gs k (VGlobal x l sp v) =
  case ql of
    KeepGlobals -> foldr (quoteElim ql gs k) (Global x l) sp
    Full -> quoteWith ql gs k v
quoteWith ql gs k (VAbs x t b) = Abs x (quoteWith ql gs k t) (quoteClos ql gs k b)
quoteWith ql gs k (VPi x t b) = Pi x (quoteWith ql gs k t) (quoteClos ql gs k b)
quoteWith ql gs k (VSigma x t b) = Sigma x (quoteWith ql gs k t) (quoteClos ql gs k b)
quoteWith ql gs k (VPair a b t) = Pair (quoteWith ql gs k a) (quoteWith ql gs k b) (quoteWith ql gs k t)
quoteWith ql gs k (VLift t) = Lift (quoteWith ql gs k t)
quoteWith ql gs k (VLiftTerm t) = LiftTerm (quoteWith ql gs k t)

quote :: GlobalCtx -> Lvl -> Val -> Core
quote = quoteWith KeepGlobals

nfWith :: QuoteLevel -> GlobalCtx -> Core -> Core
nfWith ql gs = quoteWith ql gs 0 . eval gs []

nf :: GlobalCtx -> Core -> Core
nf = nfWith KeepGlobals

convLift :: GlobalCtx -> Lvl -> Clos -> Clos -> Bool
convLift gs k c c' = let v = vvar k in conv gs (k + 1) (vinst gs c v) (vinst gs c' v)

convElim :: GlobalCtx -> Lvl -> Elim -> Elim -> Bool
convElim gs k ELower ELower = True
convElim gs k (EApp v) (EApp v') = conv gs k v v'
convElim gs k (EProj p) (EProj p') = p == p'
convElim gs k (EPrimElim x1 l1 k1 as1) (EPrimElim x2 l2 k2 as2) =
  x1 == x2 && l1 == l2 && k1 == k2 && and (zipWith (conv gs k) as1 as2)
convElim gs k _ _ = False

conv :: GlobalCtx -> Lvl -> Val -> Val -> Bool
conv gs k a b = -- trace ("conv " ++ show (quote gs k a) ++ " ~ " ++ show (quote gs k b)) $ do
  case (a, b) of
    (VU l1, VU l2) | l1 == l2 -> True
    (VLift t1, VLift t2) -> conv gs k t1 t2
    (VLiftTerm t1, VLiftTerm t2) -> conv gs k t1 t2
    (VPi _ t b, VPi _ t' b') -> conv gs k t t' && convLift gs k b b'
    (VSigma _ t b, VSigma _ t' b') -> conv gs k t t' && convLift gs k b b'
    (VAbs _ _ b, VAbs _ _ b') -> convLift gs k b b'
    (VAbs _ _ b, x) -> let v = vvar k in conv gs (k + 1) (vinst gs b v) (vapp gs x v)
    (x, VAbs _ _ b) -> let v = vvar k in conv gs (k + 1) (vapp gs x v) (vinst gs b v)
    (VPair a b _, VPair c d _) -> conv gs k a c && conv gs k b d
    (VPair a b _, x) -> conv gs k a (vfst x) && conv gs k b (vsnd x)
    (x, VPair a b _) -> conv gs k (vfst x) a && conv gs k (vsnd x) b
    (VNe h sp, VNe h' sp') | h == h' -> and $ zipWith (convElim gs k) sp sp'
    (VNe (HPrim PUnit _) [], v) -> True
    (v, VNe (HPrim PUnit _) []) -> True
    (VNe (HPrim PHRefl _) _, v) -> True -- is this safe?
    (v, VNe (HPrim PHRefl _) _) -> True -- is this safe?
    (VGlobal x l sp v, VGlobal x' l' sp' v') | x == x' && l == l' ->
      and (zipWith (convElim gs k) sp sp') || conv gs k v v'
    (VGlobal _ _ _ v, VGlobal _ _ _ v') -> conv gs k v v'
    (VGlobal _ _ _ v, v') -> conv gs k v v'
    (v, VGlobal _ _ _ v') -> conv gs k v v'
    (_, _) -> False

primType :: GlobalCtx -> PrimName -> ULvl -> Val
primType gs PVoid l = VU l
primType gs PUnitType l = VU l
primType gs PUnit l = vunittype l
primType gs PBool l = VU l
primType gs PTrue l = vbool l
primType gs PFalse l = vbool l
-- (A B : Type^l) -> A -> B -> Type^l
primType gs PHEq l = vpi "A" (VU l) $ \a -> vpi "B" (VU l) $ \b -> vfun a $ vfun b $ VU l
-- (A : Type^l) -> (x : A) -> HEq^l A A x x
primType gs PHRefl l = vpi "A" (VU l) $ \a -> vpi "x" a $ \x -> vheq l a a x x
primType gs PDesc l = VU (l + 1)
primType gs PEnd l = vdesc l
primType gs PArg l = vpi "A" (VU l) $ \a -> vfun (vfun a (vdesc l)) (vdesc l)
primType gs PInd l = vfun (vdesc l) (vdesc l)
primType gs PHInd l = vfun (VU l) $ vfun (vdesc l) (vdesc l)
primType gs PData l = vfun (vdesc l) (VU l)
-- (D : Desc^l) -> El^l 0 D (Data^l D) -> Data^l D
primType gs PCon l =
  vpi "D" (vdesc l) $ \d -> vfun (vel gs l 0 d (vdata l d)) (vdata l d)

primElimType :: GlobalCtx -> PrimElimName -> ULvl -> ULvl -> Val
-- (A : Type^(l + k)) -> Void^l -> A
primElimType gs PEVoid l k = vpi "A" (VU (l + k)) $ vfun (vvoid l)
-- (P : Bool^l -> Type^(l + k)) -> P True^l -> P False^l -> (b : Bool^l) -> P b
primElimType gs PEBool l k =
  vpi "P" (vfun (vbool l) (VU (l + k))) $ \p ->
  vfun (vapp gs p (vtrue l)) $
  vfun (vapp gs p (vfalse l)) $
  vpi "b" (vbool l) (vapp gs p)
{-
(A : Type^l)
-> (a : A)
-> (P : (b : A) -> HEq^l A A a b -> Type^(l + k))
-> P a (HRefl^l A a)
-> (b : A)
-> (p : HEq^l A A a b)
-> P b p
-}
primElimType gs PEHEq l k =
  vpi "A" (VU l) $ \ta ->
  vpi "a" ta $ \a ->
  vpi "P" (vpi "b" ta $ \b -> vfun (vheq l ta ta a b) (VU (l + k))) $ \tp ->
  vfun (vapp gs (vapp gs tp ta) (vhrefl l ta a)) $
  vpi "b" ta $ \b ->
  vpi "p" (vheq l ta ta a b) $ \p ->
  vapp gs (vapp gs tp b) p
{-
(P : Desc^l -> Type^(l + k))
-> P End^l
-> ((A : Type^l) -> (K : A -> Desc^l) -> ((x : A) -> P (K x)) -> P (Arg^l A K))
-> ((K : Desc^l) -> P K -> P (Ind^l K))
-> ((A : Type^l) -> (K : Desc^l) -> P K -> P (HInd^l A K))
-> (d : Desc^l)
-> P d
-}
primElimType gs PEDesc l k =
  vpi "P" (vfun (vdesc l) (VU (l + k))) $ \p ->
  vfun (vapp gs p (vend l)) $
  vfun (vpi "A" (VU l) $ \a -> vpi "K" (vfun a (vdesc l)) $ \kk -> vfun (vpi "x" a $ \x -> vapp gs p (vapp gs kk x)) (vapp gs p (varg l a kk))) $
  vfun (vpi "K" (vdesc l) $ \kk -> vfun (vapp gs p kk) (vapp gs p (vind l kk))) $
  vfun (vpi "A" (VU l) $ \a -> vpi "K" (vdesc l) $ \kk -> vfun (vapp gs p kk) (vapp gs p (vhind l a kk))) $
  vpi "d" (vdesc l) $ \d ->
  vapp gs p d
{- El : Type^(l + k) -> Desc^l -> Type^(l + k) -}
primElimType gs PEEl l k = vfun (VU (l + k)) $ vfun (vdesc l) (VU (l + k))
{- All : (D : Desc^l) -> (X : Type^(l + k)) -> (P : X -> Type^(l + k)) -> (xs : El^l k D X) -> Type^(l + k) -}
primElimType gs PEAll l k =
  vpi "D" (vdesc l) $ \d ->
  vpi "X" (VU (l + k)) \x ->
  vfun (vfun x (VU (l + k))) $
  vfun (vel gs l k d x) $
  VU (l + k)
{- all : (D : Desc^l) -> (X : Type^(l + k)) -> (P : X -> Type^(l + k)) -> ((x : X) -> P x) -> (xs : El^l k D X) -> All^l k D X P xs -}
primElimType gs PEall l k =
  vpi "D" (vdesc l) $ \d ->
  vpi "X" (VU (l + k)) $ \x ->
  vpi "P" (vfun x (VU (l + k))) $ \p ->
  vfun (vpi "x" x $ \xx -> vapp gs p xx) $
  vpi "xs" (vel gs l k d x) $ \xs ->
  vAll gs l k d x p xs
{-
(D : Desc^l)
(P : Data^l D -> Type^(l + k))
((d : El^l 0 D (Data^l D)) -> All^l 0 D (Data^l D) P d -> P (Con^l D d))
(x : Data^l D)
-> P x
-}
primElimType gs PEData l k =
  vpi "D" (vdesc l) $ \d ->
  vpi "P" (vfun (vdata l d) (VU (l + k))) $ \p ->
  vfun (
    vpi "d" (vel gs l 0 d (vdata l d)) $ \dd ->
    vfun (vAll gs l 0 d (vdata l d) p dd) $
    vapp gs p (vcon l d dd)
  ) $
  vpi "x" (vdata l d) $ \x ->
  vapp gs p x
