module Evaluation where

import Common
import Core
import Val
import Globals
import Metas

-- import Debug.Trace (trace)

vinst :: Clos -> Val -> Val
vinst (Clos e c) v = eval (v : e) c
vinst (Fun f) v = f v

vapp :: Val -> Val -> Val
vapp (VAbs _ b) v = vinst b v
vapp (VNe h sp) v = VNe h (EApp v : sp)
vapp (VGlobal x l sp w) v = VGlobal x l (EApp v : sp) (vapp w v)
vapp _ _ = undefined

velim :: Val -> Elim -> Val
velim v (EApp a) = vapp v a
velim v ELower = vlower v
velim v (EProj p) = vproj v p
velim v (EPrimElim x l k as) = vprimelim  x l k as v

vappSp :: Val -> Spine -> Val
vappSp v [] = v
vappSp v (a : as) = velim (vappSp v as) a

vproj :: Val -> ProjType -> Val
vproj (VPair a b) Fst = a
vproj (VPair a b) Snd = b
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

pattern VTrue l = VNe (HPrim PTrue l) []
pattern VFalse l = VNe (HPrim PFalse l) []
pattern VData l d = VNe (HPrim PData l) [EApp d]

vprimelim :: PrimElimName -> ULvl -> ULvl -> [Val] -> Val -> Val
vprimelim PEBool l k [p, t, f] (VNe (HPrim PTrue _) []) = t
vprimelim PEBool l k [p, t, f] (VNe (HPrim PFalse _) []) = f
vprimelim PEBoolDesc l k [t, f] (VNe (HPrim PTrue _) []) = t
vprimelim PEBoolDesc l k [t, f] (VNe (HPrim PFalse _) []) = f

vprimelim PEHEq l k [ta, a, tp, h, b] VRefl = h

-- El X End^l = UnitType^(l + k)
vprimelim PEEl l k [x] (VCon (VPair (VTrue _) _)) = vunittype (l + k)
-- El X (Arg^l A K) = (x : A) ** El X (K (lift x))
vprimelim PEEl l k [x] (VCon (VPair (VFalse _) (VPair (VTrue _) (VPair a (VPair kk _))))) =
  vsigma "x" a $ \xx -> vprimelim PEEl l k [x] (vapp kk (vliftterm xx))
-- El X (Ind^l K) = X ** El X K
vprimelim PEEl l k [x] (VCon (VPair (VFalse _) (VPair (VFalse _) (VPair (VTrue _) (VPair kk _))))) =
  vpairty x $ vprimelim PEEl l k [x] kk
-- El X (HInd^l A K) = (A -> X) ** El K X
vprimelim PEEl l k [x] (VCon (VPair (VFalse _) (VPair (VFalse _) (VPair (VFalse _) (VPair a (VPair kk _)))))) =
  vpairty (vfun a x) $ vprimelim PEEl l k [x] kk

-- All End X P _ = UnitType
vprimelim PEAll l k [x, p, xs] (VCon (VPair (VTrue _) _)) = vunittype (l + k)
-- All (Arg A K) X P xs = All (K (fst xs)) X P (snd xs)
vprimelim PEAll l k [x, p, xs] (VCon (VPair (VFalse _) (VPair (VTrue _) (VPair a (VPair kk _))))) =
  vprimelim PEAll l k [x, p, vsnd xs] (vapp kk (vliftterm (vfst xs)))
-- All (Ind K) X P xs = P (fst xs) ** All K X P (snd xs)
vprimelim PEAll l k [x, p, xs] (VCon (VPair (VFalse _) (VPair (VFalse _) (VPair (VTrue _) (VPair kk _))))) =
  vpairty (vapp p (vfst xs)) $ vprimelim PEAll l k [x, p, vsnd xs] kk
-- All (HInd A K) X P xs = ((x : A) -> P ((fst xs) x)) ** All K X P (snd xs)
vprimelim PEAll l k [x, p, xs] (VCon (VPair (VFalse _) (VPair (VFalse _) (VPair (VFalse _) (VPair a (VPair kk _)))))) =
  vpairty (vpi "x" a $ \x -> vapp p (vapp (vfst xs) x)) $ vprimelim PEAll l k [x, p, vsnd xs] kk

-- all End X P p _ = Unit
vprimelim PEall l k [x, p, pp, xs] (VCon (VPair (VTrue _) _)) = vunit (l + k)
-- all (Arg A K) X P p xs = all (K (fst xs)) X P p (snd xs)
vprimelim PEall l k [x, p, pp, xs] (VCon (VPair (VFalse _) (VPair (VTrue _) (VPair a (VPair kk _))))) =
  vprimelim PEall l k [x, p, pp, vsnd xs] (vapp kk (vliftterm (vfst xs)))
-- all (Ind K) X P p xs = (p (fst xs), all K X P p (snd xs))
vprimelim PEall l k [x, p, pp, xs] (VCon (VPair (VFalse _) (VPair (VFalse _) (VPair (VTrue _) (VPair kk _))))) =
  VPair (vapp pp (vfst xs)) (vprimelim PEall l k [x, p, pp, vsnd xs] kk)
-- all (HInd A K) X P p xs = (\h. p ((fst xs) h), all K X P p (snd xs))
vprimelim PEall l k [x, p, pp, xs] (VCon (VPair (VFalse _) (VPair (VFalse _) (VPair (VFalse _) (VPair a (VPair kk _)))))) =
  VPair (vabs "h" $ \h -> vapp p (vapp (vfst xs) h)) (vprimelim PEall l k [x, p, pp, vsnd xs] kk)

-- (elim Data) D P p (Con _ x) = p x (all D (Data D) P ((elim Data) D P p) x)
vprimelim PEData l k [d, p, pp] (VCon x) =
  vapp (vapp pp x) (vall l k d (vdata l d) p (vabs "y" $ vprimelim PEData l k [d, p, pp]) x)

vprimelim x l k as (VNe h sp) = VNe h (EPrimElim x l k as : sp)
vprimelim p l k as (VGlobal x kk sp v) = VGlobal x kk (EPrimElim p l k as : sp) (vprimelim p l k as v)
vprimelim x l k as _ = undefined

vel :: ULvl -> ULvl -> Val -> Val -> Val
vel l k d x = vprimelim PEEl l k [x] d

vAll :: ULvl -> ULvl -> Val -> Val -> Val -> Val -> Val
vAll l k d x p xs = vprimelim PEAll l k [x, p, xs] d

vall :: ULvl -> ULvl -> Val -> Val -> Val -> Val -> Val -> Val
vall l k d x p pp xs = vprimelim PEall l k [x, p, pp, xs] d

force :: Val -> Val
force m@(VNe (HMeta x) sp) =
  case lookupMeta x of
    Solved v -> force (vappSp v sp)
    Unsolved -> m
force (VGlobal _ _ _ v) = force v
force v = v

vAppBDs :: Env -> Val -> [BD] -> Val
vAppBDs env v bds = case (env, bds) of
  ([], []) -> v
  (t : env, Bound : bds) -> vAppBDs env v bds `vapp` t
  (t : env, Defined : bds) -> vAppBDs env v bds
  _ -> error "impossible"

eval :: Env -> Core -> Val
eval e (Var i) = e !! i
eval e (Global x l) =
  case getGlobal x of
    Just e | l == 0 -> VGlobal x 0 [] $ gval e
    Just e -> VGlobal x l [] $ eval [] (liftUniv l (gcore e))
    Nothing -> undefined
eval e (Prim x l) = vprim x l
eval e (PrimElim x l1 l2) = evalprimelim x l1 l2
eval e (App f a) = vapp (eval e f) (eval e a)
eval e (Abs x b) = VAbs x (Clos e b)
eval e (Pi x t b) = VPi x (eval e t) (Clos e b)
eval e (Sigma x t b) = VSigma x (eval e t) (Clos e b)
eval e (Pair a b) = VPair (eval e a) (eval e b)
eval e (Proj t p) = vproj (eval e t) p
eval e (U l) = VU l
eval e (Let x t v b) = eval (eval e v : e) b
eval e (Lift t) = VLift (eval e t)
eval e (LiftTerm t) = vliftterm (eval e t)
eval e (Lower t) = vlower (eval e t)
eval e (Con t) = VCon (eval e t)
eval e Refl = VRefl
eval e (Meta x) = VMeta x
eval e (InsertedMeta x bds) = vAppBDs e (VMeta x) bds

evalprimelim :: PrimElimName -> ULvl -> ULvl -> Val
evalprimelim PEBool l k =
  vabs "P" $ \p ->
  vabs "t" $ \t ->
  vabs "f" $ \f ->
  vabs "b" $ \b ->
  vprimelim PEBool l k [p, t, f] b
evalprimelim PEBoolDesc l k =
  vabs "t" $ \t ->
  vabs "f" $ \f ->
  vabs "b" $ \b ->
  vprimelim PEBoolDesc l k [t, f] b
evalprimelim PEHEq l k =
  vabs "A" $ \ta ->
  vabs "a" $ \a ->
  vabs "P" $ \tp ->
  vabs "h" $ \h ->
  vabs "b" $ \b ->
  vabs "p" $ \p ->
  vprimelim PEHEq l k [ta, a, tp, h, b] p
evalprimelim PEVoid l k =
  vabs "A" $ \a ->
  vabs "v" $ \v ->
  vprimelim PEVoid l k [a] v
evalprimelim PEEl l k =
  vabs "X" $ \x ->
  vabs "D" $ \d ->
  vprimelim PEEl l k [x] d
evalprimelim PEAll l k =
  vabs "D" $ \d ->
  vabs "X" $ \x ->
  vabs "P" $ \p ->
  vabs "xs" $ \xs ->
  vprimelim PEAll l k [x, p, xs] d
evalprimelim PEall l k =
  vabs "D" $ \d ->
  vabs "X" $ \x ->
  vabs "P" $ \p ->
  vabs "p" $ \pp ->
  vabs "xs" $ \xs ->
  vprimelim PEall l k [x, p, pp, xs] d
evalprimelim PEData l k =
  vabs "D" $ \d ->
  vabs "P" $ \p ->
  vabs "p" $ \pp ->
  vabs "x" $ \x ->
  vprimelim PEData l k [d, p, pp] x

data QuoteLevel = KeepGlobals | Full

quoteHead :: Lvl -> Head -> Core
quoteHead k (HVar l) = Var (k - l - 1)
quoteHead k (HPrim x l) = Prim x l
quoteHead k (HMeta x) = Meta x

quoteElim :: QuoteLevel -> Lvl -> Elim -> Core -> Core
quoteElim ql k (EApp v) t = App t (quoteWith ql k v)
quoteElim ql k (EProj p) t = Proj t p
quoteElim ql k (EPrimElim x l1 l2 as) t =
  case primElimPosition x of
    PEPLast -> App (foldl App (PrimElim x l1 l2) (map (quoteWith ql k) as)) t
    PEPFirst -> foldl App (App (PrimElim x l1 l2) t) (map (quoteWith ql k) as)
quoteElim ql k ELower t = Lower t

quoteClos :: QuoteLevel -> Lvl -> Clos -> Core
quoteClos ql k c = quoteWith ql (k + 1) $ vinst c (vvar k)

quoteWith :: QuoteLevel -> Lvl -> Val -> Core
quoteWith ql k (VU l) = U l
quoteWith ql k (VNe h sp) = foldr (quoteElim ql k) (quoteHead k h) sp
quoteWith ql k (VGlobal x l sp v) =
  case ql of
    KeepGlobals -> foldr (quoteElim ql k) (Global x l) sp
    Full -> quoteWith ql k v
quoteWith ql k (VAbs x b) = Abs x (quoteClos ql k b)
quoteWith ql k (VPi x t b) = Pi x (quoteWith ql k t) (quoteClos ql k b)
quoteWith ql k (VSigma x t b) = Sigma x (quoteWith ql k t) (quoteClos ql k b)
quoteWith ql k (VPair a b) = Pair (quoteWith ql k a) (quoteWith ql k b)
quoteWith ql k (VLift t) = Lift (quoteWith ql k t)
quoteWith ql k (VLiftTerm t) = LiftTerm (quoteWith ql k t)
quoteWith ql k (VCon t) = Con (quoteWith ql k t)
quoteWith _ _ VRefl = Refl

quote :: Lvl -> Val -> Core
quote = quoteWith KeepGlobals

nfWith :: QuoteLevel -> Core -> Core
nfWith ql = quoteWith ql 0 . eval []

nf :: Core -> Core
nf = nfWith KeepGlobals

convLift :: Lvl -> Clos -> Clos -> Bool
convLift k c c' = let v = vvar k in conv (k + 1) (vinst c v) (vinst c' v)

convElim :: Lvl -> Elim -> Elim -> Bool
convElim k ELower ELower = True
convElim k (EApp v) (EApp v') = conv k v v'
convElim k (EProj p) (EProj p') = p == p'
convElim k (EPrimElim PEBoolDesc l1 k1 [t1, f1]) (EPrimElim PEBool l2 k2 [p, t2, f2]) =
  l1 == l2 && k1 + 1 == k2 && conv k (vabs "_" $ \_ -> vDesc l1) p && conv k t1 t2 && conv k f1 f2
convElim k (EPrimElim PEBool l2 k2 [p, t2, f2]) (EPrimElim PEBoolDesc l1 k1 [t1, f1]) =
  l1 == l2 && k1 + 1 == k2 && conv k p (vabs "_" $ \_ -> vDesc l1) && conv k t2 t1 && conv k f2 f1
convElim k (EPrimElim x1 l1 k1 as1) (EPrimElim x2 l2 k2 as2) =
  x1 == x2 && l1 == l2 && k1 == k2 && and (zipWith (conv k) as1 as2)
convElim k _ _ = False

conv :: Lvl -> Val -> Val -> Bool
conv k a b = -- trace ("conv " ++ show (quote k a) ++ " ~ " ++ show (quote k b)) $ do
  case (a, b) of
    (VU l1, VU l2) | l1 == l2 -> True
    (VLift t1, VLift t2) -> conv k t1 t2
    (VLiftTerm t1, VLiftTerm t2) -> conv k t1 t2
    (VCon t1, VCon t2) -> conv k t1 t2
    (VPi _ t b, VPi _ t' b') -> conv k t t' && convLift k b b'
    (VSigma _ t b, VSigma _ t' b') -> conv k t t' && convLift k b b'
    (VAbs _ b, VAbs _ b') -> convLift k b b'
    (VAbs _ b, x) -> let v = vvar k in conv (k + 1) (vinst b v) (vapp x v)
    (x, VAbs _ b) -> let v = vvar k in conv (k + 1) (vapp x v) (vinst b v)
    (VPair a b, VPair c d) -> conv k a c && conv k b d
    (VPair a b, x) -> conv k a (vfst x) && conv k b (vsnd x)
    (x, VPair a b) -> conv k (vfst x) a && conv k (vsnd x) b
    (VNe h sp, VNe h' sp') | h == h' -> and $ zipWith (convElim k) sp sp'
    
    (VNe (HPrim PUnit _) [], v) -> True
    (v, VNe (HPrim PUnit _) []) -> True
    
    (VRefl, v) -> True -- is this safe?
    (v, VRefl) -> True -- is this safe?

    (VGlobal x l sp v, VGlobal x' l' sp' v') | x == x' && l == l' ->
      and (zipWith (convElim k) sp sp') || conv k v v'
    (VGlobal _ _ _ v, VGlobal _ _ _ v') -> conv k v v'
    (VGlobal _ _ _ v, v') -> conv k v v'
    (v, VGlobal _ _ _ v') -> conv k v v'
    (_, _) -> False

primType :: PrimName -> ULvl -> Val
primType PVoid l = VU l
primType PUnitType l = VU l
primType PUnit l = vunittype l
primType PBool l = VU l
primType PTrue l = vbool l
primType PFalse l = vbool l
-- (A B : Type^l) -> A -> B -> Type^l
primType PHEq l = vpi "A" (VU l) $ \a -> vpi "B" (VU l) $ \b -> vfun a $ vfun b $ VU l
primType PData l = vfun (vDesc l) (VU l)

primElimType :: PrimElimName -> ULvl -> ULvl -> Val
-- (A : Type^(l + k)) -> Void^l -> A
primElimType PEVoid l k = vpi "A" (VU (l + k)) $ vfun (vvoid l)
-- (P : Bool^l -> Type^(l + k)) -> P True^l -> P False^l -> (b : Bool^l) -> P b
primElimType PEBool l k =
  vpi "P" (vfun (vbool l) (VU (l + k))) $ \p ->
  vfun (vapp p (vtrue l)) $
  vfun (vapp p (vfalse l)) $
  vpi "b" (vbool l) (vapp p)
-- Desc^(l + k) -> Desc^(l + k) -> Bool^l -> Desc^(l + k)
primElimType PEBoolDesc l k =
  vfun (vDesc (l + k)) $
  vfun (vDesc (l + k)) $
  vfun (vbool l) $
  vDesc (l + k)
{-
(A : Type^l)
-> (a : A)
-> (P : (b : A) -> HEq^l A A a b -> Type^(l + k))
-> P a (HRefl^l A a)
-> (b : A)
-> (p : HEq^l A A a b)
-> P b p
-}
primElimType PEHEq l k =
  vpi "A" (VU l) $ \ta ->
  vpi "a" ta $ \a ->
  vpi "P" (vpi "b" ta $ \b -> vfun (vheq l ta ta a b) (VU (l + k))) $ \tp ->
  vfun (vapp (vapp tp ta) VRefl) $
  vpi "b" ta $ \b ->
  vpi "p" (vheq l ta ta a b) $ \p ->
  vapp (vapp tp b) p
{- El : Type^(l + k) -> Desc^l -> Type^(l + k) -}
primElimType PEEl l k = vfun (VU (l + k)) $ vfun (vDesc l) (VU (l + k))
{- All : (D : Desc^l) -> (X : Type^(l + k)) -> (P : X -> Type^(l + k)) -> (xs : El^l k D X) -> Type^(l + k) -}
primElimType PEAll l k =
  vpi "D" (vDesc l) $ \d ->
  vpi "X" (VU (l + k)) \x ->
  vfun (vfun x (VU (l + k))) $
  vfun (vel l k d x) $
  VU (l + k)
{- all : (D : Desc^l) -> (X : Type^(l + k)) -> (P : X -> Type^(l + k)) -> ((x : X) -> P x) -> (xs : El^l k D X) -> All^l k D X P xs -}
primElimType PEall l k =
  vpi "D" (vDesc l) $ \d ->
  vpi "X" (VU (l + k)) $ \x ->
  vpi "P" (vfun x (VU (l + k))) $ \p ->
  vfun (vpi "x" x $ \xx -> vapp p xx) $
  vpi "xs" (vel l k d x) $ \xs ->
  vAll l k d x p xs
{-
(D : Desc^l)
(P : Data^l D -> Type^(l + k))
((d : El^l 0 D (Data^l D)) -> All^l 0 D (Data^l D) P d -> P (Con^l D d))
(x : Data^l D)
-> P x
-}
primElimType PEData l k =
  vpi "D" (vDesc l) $ \d ->
  vpi "P" (vfun (vdata l d) (VU (l + k))) $ \p ->
  vfun (
    vpi "d" (vel l 0 d (vdata l d)) $ \dd ->
    vfun (vAll l 0 d (vdata l d) p dd) $
    vapp p (VCon dd)
  ) $
  vpi "x" (vdata l d) $ \x ->
  vapp p x

-- levitation follows
-- SumD : Desc -> Desc -> Desc = \A B. Arg^l Bool^l ((elim BoolDesc^l) A B)
vSumD :: ULvl -> Val -> Val -> Val
vSumD l a b = vArg l (vbool l) (vabs "tag" $ vprimelim PEBoolDesc l 0 [a, b])

-- End = Con (True^(l + 1), Unit^(l + 1))
vEnd :: ULvl -> Val
vEnd l = VCon (VPair (vtrue (l + 1)) (vunit (l + 1)))

-- Arg A K = Con (False^(l + 1), True^(l + 1), A, \x. K (lower x), Unit^(l + 1))
vArg :: ULvl -> Val -> Val -> Val
vArg l a k =
  VCon $
  VPair (vfalse (l + 1)) $
  VPair (vtrue (l + 1)) $
  VPair a $
  VPair (vabs "x" $ \x -> vapp k (vlower x)) $
  vunit (l + 1)

-- Ind K = Con (False^(l + 1), False^(l + 1), True^(l + 1), K, Unit^(l + 1))
vInd :: ULvl -> Val -> Val
vInd l k =
  VCon $
  VPair (vfalse (l + 1)) $
  VPair (vfalse (l + 1)) $
  VPair (vtrue (l + 1)) $
  VPair k $
  vunit (l + 1)

-- HInd A K = Con (False^(l + 1), False^(l + 1), False^(l + 1), A, K, Unit^(l + 1))
vHInd :: ULvl -> Val -> Val -> Val
vHInd l a k =
  VCon $
  VPair (vfalse (l + 1)) $
  VPair (vfalse (l + 1)) $
  VPair (vfalse (l + 1)) $
  VPair a $
  VPair k $
  vunit (l + 1)

{- DescD =
  SumD^(l + 1) End^(l + 1) (
  SumD^(l + 1) (Arg^(l + 1) Type^l (\(A : Type^l). HInd^(l + 1) (Lift A) End^(l + 1))) (
  SumD^(l + 1) (Ind^(l + 1) End^(l + 1))
  (Arg^(l + 1) Type^l (\(_ : Type^l). Ind^(l + 1) End^(l + 1)))))
-}
vDescD :: ULvl -> Val
vDescD l =
  vSumD (l + 1) (vEnd (l + 1)) $
  vSumD (l + 1) (vArg (l + 1) (VU l) (vabs "A" $ \a -> vHInd (l + 1) (VLift a) (vEnd (l + 1)))) $
  vSumD (l + 1) (vInd (l + 1) (vEnd (l + 1))) $
  vArg (l + 1) (VU l) (vabs "_" $ \_ -> vInd (l + 1) (vEnd (l + 1)))

-- Desc : Type1 = Data^(l + 1) DescD^l
vDesc :: ULvl -> Val
vDesc l = vdata (l + 1) (vDescD l)
