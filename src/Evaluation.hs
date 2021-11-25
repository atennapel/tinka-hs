module Evaluation where

import Common
import Core
import Val
import Globals
import Metas
import Universes

-- import Debug.Trace (trace)

vinst :: Clos -> Val -> Val
vinst (Clos e c) v = eval (v : e) c
vinst (Fun f) v = f v

vapp :: Val -> Val -> Icit -> Val
vapp (VAbs _ _ b) v _ = vinst b v
vapp (VNe h sp) v i = VNe h (EApp v i : sp)
vapp (VGlobal x l sp w) v i = VGlobal x l (EApp v i : sp) (vapp w v i)
vapp _ _ _ = undefined

vappe :: Val -> Val -> Val
vappe a b = vapp a b Expl

velim :: Val -> Elim -> Val
velim v (EApp a i) = vapp v a i
velim v ELower = vlower v
velim v (EProj p) = vproj v p
velim v (EPrimElim x l k as) = vprimelim  x l k as v

velimSp :: Val -> Spine -> Val
velimSp v [] = v
velimSp v (e : as) = velim (velimSp v as) e

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
pattern VData l d = VNe (HPrim PData l) [EApp d Expl]

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
  vsigma "x" a (UConst l) (UConst $ l + k) $ \xx -> vprimelim PEEl l k [x] (vappe kk (vliftterm xx))
-- El X (Ind^l K) = X ** El X K
vprimelim PEEl l k [x] (VCon (VPair (VFalse _) (VPair (VFalse _) (VPair (VTrue _) (VPair kk _))))) =
  vpairty x (UConst l) (UConst $ l + k) $ vprimelim PEEl l k [x] kk
-- El X (HInd^l A K) = (A -> X) ** El K X
vprimelim PEEl l k [x] (VCon (VPair (VFalse _) (VPair (VFalse _) (VPair (VFalse _) (VPair a (VPair kk _)))))) =
  vpairty (vfun a (UConst l) (UConst l) x) (UConst l) (UConst $ l + k) $ vprimelim PEEl l k [x] kk

-- All End X P _ = UnitType
vprimelim PEAll l k [x, p, xs] (VCon (VPair (VTrue _) _)) = vunittype (l + k)
-- All (Arg A K) X P xs = All (K (fst xs)) X P (snd xs)
vprimelim PEAll l k [x, p, xs] (VCon (VPair (VFalse _) (VPair (VTrue _) (VPair a (VPair kk _))))) =
  vprimelim PEAll l k [x, p, vsnd xs] (vappe kk (vliftterm (vfst xs)))
-- All (Ind K) X P xs = P (fst xs) ** All K X P (snd xs)
vprimelim PEAll l k [x, p, xs] (VCon (VPair (VFalse _) (VPair (VFalse _) (VPair (VTrue _) (VPair kk _))))) =
  vpairty (vappe p (vfst xs)) (UConst $ l + k) (UConst $ l + k) $ vprimelim PEAll l k [x, p, vsnd xs] kk
-- All (HInd A K) X P xs = ((x : A) -> P ((fst xs) x)) ** All K X P (snd xs)
vprimelim PEAll l k [x, p, xs] (VCon (VPair (VFalse _) (VPair (VFalse _) (VPair (VFalse _) (VPair a (VPair kk _)))))) =
  vpairty (vpi "x" a (UConst l) (UConst $ l + k) $ \x -> vappe p (vappe (vfst xs) x)) (UConst $ l + k) (UConst $ l + k) $ vprimelim PEAll l k [x, p, vsnd xs] kk

-- all End X P p _ = Unit
vprimelim PEall l k [x, p, pp, xs] (VCon (VPair (VTrue _) _)) = vunit (l + k)
-- all (Arg A K) X P p xs = all (K (fst xs)) X P p (snd xs)
vprimelim PEall l k [x, p, pp, xs] (VCon (VPair (VFalse _) (VPair (VTrue _) (VPair a (VPair kk _))))) =
  vprimelim PEall l k [x, p, pp, vsnd xs] (vappe kk (vliftterm (vfst xs)))
-- all (Ind K) X P p xs = (p (fst xs), all K X P p (snd xs))
vprimelim PEall l k [x, p, pp, xs] (VCon (VPair (VFalse _) (VPair (VFalse _) (VPair (VTrue _) (VPair kk _))))) =
  VPair (vappe pp (vfst xs)) (vprimelim PEall l k [x, p, pp, vsnd xs] kk)
-- all (HInd A K) X P p xs = (\h. p ((fst xs) h), all K X P p (snd xs))
vprimelim PEall l k [x, p, pp, xs] (VCon (VPair (VFalse _) (VPair (VFalse _) (VPair (VFalse _) (VPair a (VPair kk _)))))) =
  VPair (vabs "h" $ \h -> vappe p (vappe (vfst xs) h)) (vprimelim PEall l k [x, p, pp, vsnd xs] kk)

-- (elim Data) D P p (Con _ x) = p x (all D (Data D) P ((elim Data) D P p) x)
vprimelim PEData l k [d, p, pp] (VCon x) =
  vappe (vappe pp x) (vall l k d (vdata l d) p (vabs "y" $ vprimelim PEData l k [d, p, pp]) x)

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
force (VU u) = VU (normalizeUniv u)
force m@(VNe (HMeta x) sp) =
  case lookupMeta x of
    Solved _ _ _ _ v -> force (velimSp v sp)
    Unsolved _ _ -> m
force (VGlobal _ _ _ v) = force v
force v = v

vappPruning :: Env -> Val -> Pruning -> Val
vappPruning e v p = case (e, p) of
  ([], []) -> v
  (t : e, Just i : p) -> vapp (vappPruning e v p) t i
  (t : e, Nothing : p) -> vappPruning e v p
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
eval e (App f a i) = vapp (eval e f) (eval e a) i
eval e (Abs x i b) = VAbs x i (Clos e b)
eval e (Pi x i t u1 b u2) = VPi x i (eval e t) u1 (Clos e b) u2
eval e (Sigma x t u1 b u2) = VSigma x (eval e t) u1 (Clos e b) u2
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
eval e (AppPruning t p) = vappPruning e (eval e t) p

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
quoteElim ql k (EApp v i) t = App t (quoteWith ql k v) i
quoteElim ql k (EProj p) t = Proj t p
quoteElim ql k (EPrimElim x l1 l2 as) t =
  case primElimPosition x of
    PEPLast -> App (foldl (\a b -> App a b Expl) (PrimElim x l1 l2) (map (quoteWith ql k) as)) t Expl
    PEPFirst -> foldl (\a b -> App a b Expl) (App (PrimElim x l1 l2) t Expl) (map (quoteWith ql k) as)
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
quoteWith ql k (VAbs x i b) = Abs x i (quoteClos ql k b)
quoteWith ql k (VPi x i t u1 b u2) = Pi x i (quoteWith ql k t) u1 (quoteClos ql k b) u2
quoteWith ql k (VSigma x t u1 b u2) = Sigma x (quoteWith ql k t) u1 (quoteClos ql k b) u2
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
convElim k (EApp v _) (EApp v' _) = conv k v v'
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
    (VPi _ i t u1 b u2, VPi _ i' t' u3 b' u4) ->
      i == i' && conv k t t' && u1 == u3 && convLift k b b' && u2 == u4
    (VSigma _ t u1 b u2, VSigma _ t' u3 b' u4) ->
      conv k t t' && u1 == u3 && convLift k b b' && u2 == u4
    (VAbs _ _ b, VAbs _ _ b') -> convLift k b b'
    (VAbs _ i b, x) -> let v = vvar k in conv (k + 1) (vinst b v) (vapp x v i)
    (x, VAbs _ i b) -> let v = vvar k in conv (k + 1) (vapp x v i) (vinst b v)
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

primType :: PrimName -> ULvl -> (Val, Univ)
primType PVoid l = (VType l, UConst (l + 1))
primType PUnitType l = (VType l, UConst (l + 1))
primType PUnit l = (vunittype l, UConst l)
primType PBool l = (VType l, UConst (l + 1))
primType PTrue l = (vbool l, UConst l)
primType PFalse l = (vbool l, UConst l)
-- (A B : Type^l) -> A -> B -> Type^l
primType PHEq l =
  let c = UConst in
  (vpi "A" (VType l) (c $ l + 1) (c $ l + 1) $ \a -> vpi "B" (VType l) (c $ l + 1) (c $ l + 1) $ \b -> vfun a (c l) (c $ l + 1) $ vfun b (c l) (c $ l + 1) $ VType l, c $ l + 1)
primType PData l =
  let c = UConst in
  (vfun (vDesc l) (c $ l + 1) (c $ l + 1) (VType l), c $ l + 1)

primElimType :: PrimElimName -> ULvl -> ULvl -> (Val, Univ)
-- (A : Type^(l + k)) -> Void^l -> A
primElimType PEVoid l k =
  let c = UConst in
  (vpi "A" (VType (l + k)) (c $ l + k + 1) (c $ l + k) $ vfun (vvoid l) (c l) (c $ l + k), c $ l + k + 1)
-- (P : Bool^l -> Type^(l + k)) -> P True^l -> P False^l -> (b : Bool^l) -> P b
primElimType PEBool l k =
  let c = UConst in
  (vpi "P" (vfun (vbool l) (c l) (c $ l + k + 1) (VType (l + k))) (c $ l + k + 1) (c $ l + k + 1) $ \p ->
  vfun (vappe p (vtrue l)) (c $ l + k) (c $ l + k) $
  vfun (vappe p (vfalse l)) (c $ l + k) (c $ l + k) $
  vpi "b" (vbool l) (c l) (c $ l + k) (vappe p), c $ l + k + 1)
-- Desc^(l + k) -> Desc^(l + k) -> Bool^l -> Desc^(l + k)
primElimType PEBoolDesc l k =
  let c = UConst in
  (vfun (vDesc (l + k)) (c $ l + k + 1) (c $ l + k + 1) $
  vfun (vDesc (l + k)) (c $ l + k + 1) (c $ l + k + 1) $
  vfun (vbool l) (c l) (c $ l + k + 1) $
  vDesc (l + k), c $ l + k + 1)
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
  let c = UConst in
  (vpi "A" (VType l) (c $ l + 1) (c $ l + k + 1) $ \ta ->
  vpi "a" ta (c l) (c $ l + k + 1) $ \a ->
  vpi "P" (vpi "b" ta (c l) (c $ l + k + 1) $ \b -> vfun (vheq l ta ta a b) (c l) (c $ l + k + 1) (VType (l + k))) (c $ l + k + 1) (c $ l + k) $ \tp ->
  vfun (vappe (vappe tp ta) VRefl) (c $ l + k) (c $ l + k) $
  vpi "b" ta (c l) (c $ l + k) $ \b ->
  vpi "p" (vheq l ta ta a b) (c l) (c $ l + k) $ \p ->
  vappe (vappe tp b) p, c $ l + k + 1)
{- El : Type^(l + k) -> Desc^l -> Type^(l + k) -}
primElimType PEEl l k =
  let c = UConst in
  (vfun (VType (l + k)) (c $ l + k + 1) (c $ l + k + 1) $ vfun (vDesc l) (c $ l + 1) (c $ l + k + 1) (VType (l + k)), c $ l + k + 1)
{- All : (D : Desc^l) -> (X : Type^(l + k)) -> (P : X -> Type^(l + k)) -> (xs : El^l k D X) -> Type^(l + k) -}
primElimType PEAll l k =
  let c = UConst in
  (vpi "D" (vDesc l) (c $ l + 1) (c $ l + k + 1) $ \d ->
  vpi "X" (VType (l + k)) (c $ l + k + 1) (c $ l + k + 1) $ \x ->
  vfun (vfun x (c $ l + k) (c $ l + k + 1) (VType (l + k))) (c $ l + k + 1) (c $ l + k + 1) $
  vfun (vel l k d x) (c $ l + k) (c $ l + k + 1) $
  VType (l + k), c $ l + k + 1)
{- all : (D : Desc^l) -> (X : Type^(l + k)) -> (P : X -> Type^(l + k)) -> ((x : X) -> P x) -> (xs : El^l k D X) -> All^l k D X P xs -}
primElimType PEall l k =
  let c = UConst in
  (vpi "D" (vDesc l) (c $ l + 1) (c $ l + k + 1) $ \d ->
  vpi "X" (VType (l + k)) (c $ l + k + 1) (c $ l + k + 1) $ \x ->
  vpi "P" (vfun x (c $ l + k) (c $ l + k + 1) (VType (l + k))) (c $ l + k + 1) (c $ l + k) $ \p ->
  vfun (vpi "x" x (c $ l + k) (c $ l + k) $ \xx -> vappe p xx) (c $ l + k) (c $ l + k) $
  vpi "xs" (vel l k d x) (c $ l + k) (c $ l + k) $ \xs ->
  vAll l k d x p xs, c $ l + k + 1)
{-
(D : Desc^l)
(P : Data^l D -> Type^(l + k))
((d : El^l 0 D (Data^l D)) -> All^l 0 D (Data^l D) P d -> P (Con^l D d))
(x : Data^l D)
-> P x
-}
primElimType PEData l k =
  let c = UConst in
  (vpi "D" (vDesc l) (c $ l + 1) (c $ l + k + 1) $ \d ->
  vpi "P" (vfun (vdata l d) (c l) (c $ l + k + 1) (VType (l + k))) (c $ l + k + 1) (c $ l + k + 1) $ \p ->
  vfun (
    vpi "d" (vel l 0 d (vdata l d)) (c l) (c $ l + k) $ \dd ->
    vfun (vAll l 0 d (vdata l d) p dd) (c $ l + k) (c $ l + k) $
    vappe p (VCon dd)
  ) (c $ l + k + 1) (c $ l + k) $
  vpi "x" (vdata l d) (c l) (c $ l + k) $ \x ->
  vappe p x, c $ l + k + 1)

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
  VPair (vabs "x" $ \x -> vappe k (vlower x)) $
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
  vSumD (l + 1) (vArg (l + 1) (VType l) (vabs "A" $ \a -> vHInd (l + 1) (VLift a) (vEnd (l + 1)))) $
  vSumD (l + 1) (vInd (l + 1) (vEnd (l + 1))) $
  vArg (l + 1) (VType l) (vabs "_" $ \_ -> vInd (l + 1) (vEnd (l + 1)))

-- Desc : Type1 = Data^(l + 1) DescD^l
vDesc :: ULvl -> Val
vDesc l = vdata (l + 1) (vDescD l)
