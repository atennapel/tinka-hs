module Evaluation where

import Common
import Core
import Val
import Globals
import Metas
import Prims

import Data.Foldable (foldrM)
import Data.Bifunctor (first)

-- import Debug.Trace (trace)

vinst :: Clos -> Val -> Val
vinst (Clos e c) v = eval (v : e) c
vinst (Fun f) v = f v

vinstlevel :: ClosLevel -> Val -> VLevel
vinstlevel (ClosLevel e c) v = evallevel (v : e) c
vinstlevel (FunLevel f) v = f v

vfinmax :: Val -> Val -> Val
vfinmax l1 l2 = case (l1, l2) of
  (VL0, l2) -> l2
  (l1, VL0) -> l1
  (VLS l1, VLS l2) -> VLS (vfinmax l1 l2)
  (l1, l2) -> VLMax l1 l2

vlmax :: VLevel -> VLevel -> VLevel
vlmax (VFin t) (VFin t') = VFin (vfinmax t t')
vlmax _ _ = VOmega

vapp :: Val -> Val -> Icit -> Val
vapp (VAbs _ _ b) v _ = vinst b v
vapp (VNe h sp) v i = VNe h (EApp v i : sp)
vapp (VGlobal x sp w) v i = VGlobal x (EApp v i : sp) (vapp w v i)
vapp _ _ _ = undefined

vappe :: Val -> Val -> Val
vappe a b = vapp a b Expl

velim :: Val -> Elim -> Val
velim v (EApp a i) = vapp v a i
velim v ELower = vlower v
velim v (EProj p) = vproj v p
velim v (EPrimElim x as) = vprimelim x as v

velimSp :: Val -> Spine -> Val
velimSp v [] = v
velimSp v (e : as) = velim (velimSp v as) e

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

vindex :: Val -> Ix -> Val
vindex v i = vproj v (PNamed Nothing i)

vnamed :: Val -> Name -> Ix -> Val
vnamed v x i = vproj v (PNamed (Just x) i)

vlower :: Val -> Val
vlower (VLiftTerm v) = v
vlower (VNe h sp) = VNe h (ELower : sp)
vlower (VGlobal x sp v) = VGlobal x (ELower : sp) (vlower v)
vlower _ = undefined

vliftterm :: Val -> Val
vliftterm (VNe h (ELower : sp)) = VNe h sp
vliftterm (VGlobal x (ELower : sp) v) = VGlobal x sp (vliftterm v)
vliftterm v = VLiftTerm v

pattern VTrue = VNe (HPrim PTrue) []
pattern VFalse = VNe (HPrim PFalse) []

vprimelim :: PrimElimName -> [(Val, Icit)] -> Val -> Val
vprimelim x as (VNe h sp) = VNe h (EPrimElim x as : sp)
vprimelim p as (VGlobal x sp v) = VGlobal x (EPrimElim p as : sp) (vprimelim p as v)
vprimelim x as _ = undefined

force :: Val -> Val
force m@(VNe (HMeta x) sp) =
  case lookupMeta x of
    Solved _ _ _ _ v -> force (velimSp v sp)
    Unsolved _ _ -> m
force (VGlobal _ _ v) = force v
force v = v

forceLevel :: VLevel -> VLevel
forceLevel VOmega = VOmega
forceLevel (VFin l) = VFin (force l)

vappPruning :: Env -> Val -> Pruning -> Val
vappPruning e v p = case (e, p) of
  ([], []) -> v
  (t : e, Just i : p) -> vapp (vappPruning e v p) t i
  (t : e, Nothing : p) -> vappPruning e v p
  _ -> error "impossible"

evallevel :: Env -> Level -> VLevel
evallevel e Omega = VOmega
evallevel e (Fin t) = VFin (eval e t)

eval :: Env -> Core -> Val
eval e (Var i) = e !! i
eval e (Global x) =
  case getGlobal x of
    Just e -> VGlobal x [] $ gval e
    Nothing -> undefined
eval e (Prim x) = vprim x
eval e (PrimElim x) = evalprimelim x
eval e (App f a i) = vapp (eval e f) (eval e a) i
eval e (Abs x i b) = VAbs x i (Clos e b)
eval e (Pi x i t u1 b u2) = VPi x i (eval e t) (evallevel e u1) (Clos e b) (ClosLevel e u2)
eval e (Sigma x t u1 b u2) = VSigma x (eval e t) (evallevel e u1) (Clos e b) (ClosLevel e u2)
eval e (Pair a b) = VPair (eval e a) (eval e b)
eval e (Proj t p) = vproj (eval e t) p
eval e (U l) = VU (evallevel e l)
eval e ULevel = VULevel
eval e L0 = VL0
eval e (LS c) = VLS (eval e c)
eval e (LMax a b) = vfinmax (eval e a) (eval e b)
eval e (Let x t v b) = eval (eval e v : e) b
eval e (Lift t) = VLift (eval e t)
eval e (LiftTerm t) = vliftterm (eval e t)
eval e (Lower t) = vlower (eval e t)
eval e Refl = VRefl
eval e (Meta x) = VMeta x
eval e (AppPruning t p) = vappPruning e (eval e t) p

evalprimelim :: PrimElimName -> Val
evalprimelim PEVoid =
  vabsimpl "l" $ \l -> 
  vabsimpl "A" $ \a ->
  vabs "v" $ \v ->
  vprimelim PEVoid [(l, Impl), (a, Impl)] v

data QuoteLevel = KeepGlobals | Full

quoteHead :: Lvl -> Head -> Core
quoteHead k (HVar l) = Var (k - l - 1)
quoteHead k (HPrim x) = Prim x
quoteHead k (HMeta x) = Meta x

quoteElim :: QuoteLevel -> Lvl -> Elim -> Core -> Core
quoteElim ql k (EApp v i) t = App t (quoteWith ql k v) i
quoteElim ql k (EProj p) t = Proj t p
quoteElim ql k (EPrimElim x as) t =
  case primElimPosition x of
    PEPLast -> App (foldl (\a (b, i) -> App a b i) (PrimElim x) (map (first (quoteWith ql k)) as)) t (primElimIcit x)
    PEPFirst -> foldl (\a (b, i) -> App a b i) (App (PrimElim x) t (primElimIcit x)) (map (first (quoteWith ql k)) as)
quoteElim ql k ELower t = Lower t

quoteClos :: QuoteLevel -> Lvl -> Clos -> Core
quoteClos ql k c = quoteWith ql (k + 1) $ vinst c (vvar k)

quoteClosLevel :: QuoteLevel -> Lvl -> ClosLevel -> Level
quoteClosLevel ql k c = quoteLevelWith ql (k + 1) $ vinstlevel c (vvar k)

quoteLevelWith :: QuoteLevel -> Lvl -> VLevel -> Level
quoteLevelWith ql k VOmega = Omega
quoteLevelWith ql k (VFin v) = Fin (quoteWith ql k v)

quoteLevel :: Lvl -> VLevel -> Level
quoteLevel = quoteLevelWith KeepGlobals

quoteWith :: QuoteLevel -> Lvl -> Val -> Core
quoteWith ql k (VU l) = U (quoteLevelWith ql k l)
quoteWith ql k VULevel = ULevel
quoteWith ql k VL0 = L0
quoteWith ql k (VLS v) = LS (quoteWith ql k v)
quoteWith ql k (VLMax a b) = LMax (quoteWith ql k a) (quoteWith ql k b)
quoteWith ql k (VNe h sp) = foldr (quoteElim ql k) (quoteHead k h) sp
quoteWith ql k (VGlobal x sp v) =
  case ql of
    KeepGlobals -> foldr (quoteElim ql k) (Global x) sp
    Full -> quoteWith ql k v
quoteWith ql k (VAbs x i b) = Abs x i (quoteClos ql k b)
quoteWith ql k (VPi x i t u1 b u2) =
  Pi x i (quoteWith ql k t) (quoteLevelWith ql k u1) (quoteClos ql k b) (quoteClosLevel ql k u2)
quoteWith ql k (VSigma x t u1 b u2) =
  Sigma x (quoteWith ql k t) (quoteLevelWith ql k u1) (quoteClos ql k b) (quoteClosLevel ql k u2)
quoteWith ql k (VPair a b) = Pair (quoteWith ql k a) (quoteWith ql k b)
quoteWith ql k (VLift t) = Lift (quoteWith ql k t)
quoteWith ql k (VLiftTerm t) = LiftTerm (quoteWith ql k t)
quoteWith _ _ VRefl = Refl

quote :: Lvl -> Val -> Core
quote = quoteWith KeepGlobals

nfWith :: QuoteLevel -> Core -> Core
nfWith ql = quoteWith ql 0 . eval []

nf :: Core -> Core
nf = nfWith KeepGlobals

convLift :: Lvl -> Clos -> Clos -> Bool
convLift k c c' = let v = vvar k in conv (k + 1) (vinst c v) (vinst c' v)

convLiftLevel :: Lvl -> ClosLevel -> ClosLevel -> Bool
convLiftLevel k c c' = let v = vvar k in convLevel (k + 1) (vinstlevel c v) (vinstlevel c' v)

eqvProj :: ProjType -> ProjType -> Bool
eqvProj (PNamed _ i) (PNamed _ i') = i == i'
eqvProj Fst (PNamed _ 0) = True
eqvProj (PNamed _ 0) Fst = True
eqvProj p p' = p == p'

convElim :: Lvl -> Elim -> Elim -> Bool
convElim k ELower ELower = True
convElim k (EApp v _) (EApp v' _) = conv k v v'
convElim k (EProj p) (EProj p') = eqvProj p p'
convElim k (EPrimElim x1 as1) (EPrimElim x2 as2) =
  x1 == x2 && and (zipWith (conv k) (map fst as1) (map fst as2))
convElim k _ _ = False

convSpProj :: Lvl -> Spine -> Spine -> Ix -> Bool
convSpProj k sp sp' 0 = convSp k sp sp'
convSpProj k (EProj Snd : sp) sp' n = convSpProj k sp sp' (n - 1)
convSpProj _ _ _ _ = False

convSp :: Lvl -> Spine -> Spine -> Bool
convSp k [] [] = True
convSp k (EProj Fst : sp) (EProj (PNamed j n) : sp') = convSpProj k sp sp' n
convSp k (EProj (PNamed j n) : sp) (EProj Fst : sp') = convSpProj k sp' sp n
convSp k (e : sp) (e' : sp') = convSp k sp sp' && convElim k e e'
convSp _ _ _ = False

convLevel :: Lvl -> VLevel -> VLevel -> Bool
convLevel k (VFin l1) (VFin l2) = conv k l1 l2
convLevel k VOmega VOmega = True
convLevel _ _ _ = False

conv :: Lvl -> Val -> Val -> Bool
conv k a b = -- trace ("conv " ++ show (quote k a) ++ " ~ " ++ show (quote k b)) $ do
  case (a, b) of
    (VU l1, VU l2) -> convLevel k l1 l2
    (VULevel, VULevel) -> True
    (VL0, VL0) -> True
    (VLS a, VLS b) -> conv k a b
    (VLMax a b, VLMax a' b') -> conv k a a' && conv k b b'
    (VLift t1, VLift t2) -> conv k t1 t2
    (VLiftTerm t1, VLiftTerm t2) -> conv k t1 t2
    (VPi _ i t u1 b u2, VPi _ i' t' u3 b' u4) ->
      i == i' && conv k t t' && convLevel k u1 u3 && convLift k b b' && convLiftLevel k u2 u4
    (VSigma _ t u1 b u2, VSigma _ t' u3 b' u4) ->
      conv k t t' && convLevel k u1 u3 && convLift k b b' && convLiftLevel k u2 u4
    (VAbs _ _ b, VAbs _ _ b') -> convLift k b b'
    (VAbs _ i b, x) -> let v = vvar k in conv (k + 1) (vinst b v) (vapp x v i)
    (x, VAbs _ i b) -> let v = vvar k in conv (k + 1) (vapp x v i) (vinst b v)
    (VPair a b, VPair c d) -> conv k a c && conv k b d
    (VPair a b, x) -> conv k a (vfst x) && conv k b (vsnd x)
    (x, VPair a b) -> conv k (vfst x) a && conv k (vsnd x) b
    (VNe h sp, VNe h' sp') | h == h' -> convSp k sp sp'
    
    (VNe (HPrim PUnit) [], v) -> True
    (v, VNe (HPrim PUnit) []) -> True
    
    (VRefl, v) -> True -- is this safe?
    (v, VRefl) -> True -- is this safe?

    (VGlobal x sp v, VGlobal x' sp' v') | x == x' ->
      convSp k sp sp' || conv k v v'
    (VGlobal _ _ v, VGlobal _ _ v') -> conv k v v'
    (VGlobal _ _ v, v') -> conv k v v'
    (v, VGlobal _ _ v') -> conv k v v'
    (_, _) -> False

primType :: PrimName -> (Val, VLevel)
primType PVoid = (VType VL0, VFin (VLS VL0))
primType PUnitType = (VType VL0, VFin (VLS VL0))
primType PUnit = (vunittype, VFin VL0)
primType PBool = (VType VL0, VFin (VLS VL0))
primType PTrue = (vbool, VFin VL0)
primType PFalse = (vbool, VFin VL0)
-- (A B : Type 0) -> A -> B -> Type 0
primType PHEq =
  (vpi "A" (VType VL0) (VFin $ VLS VL0) (\_ -> VFin $ VLS VL0) $ \a -> vpi "B" (VType VL0) (VFin $ VLS VL0) (\_ -> VFin $ VLS VL0) $ \b -> vfun a (VFin VL0) (\_ -> VFin $ VLS VL0) $ vfun b (VFin VL0) (\_ -> VFin $ VLS VL0) $ VType VL0, VFin (VLS VL0))

primElimType :: PrimElimName -> (Val, VLevel)
-- {l : Level} {A : Type l} -> Void -> A
primElimType PEVoid =
  (vpimpl "l" VULevel VOmega (VFin . VLS) $ \l -> vpimpl "A" (VType l) (VFin (VLS l)) (\_ -> VFin l) $ \a -> vfun vvoid (VFin VL0) (\_ -> VFin l) a, VOmega)

strLevel :: Lvl -> Lvl -> VLevel -> Maybe Level
strLevel l x = \case
  VOmega -> return Omega
  VFin t -> Fin <$> str l x t

strHead :: Lvl -> Lvl -> Head -> Maybe Core
strHead l x (HPrim x') = return $ Prim x'
strHead l x (HMeta x') = Nothing
strHead l x (HVar x') =
  case compare x' x of
    EQ -> Nothing
    LT -> return (Var (l - x' - 1))
    GT -> return (Var (l - x'))

strElim :: Lvl -> Lvl -> Elim -> Core -> Maybe Core
strElim l x (EApp v i) t = App t <$> str l x v <*> return i
strElim l x (EProj p) t = return $ Proj t p
strElim l x (EPrimElim x' as) t =
  case primElimPosition x' of
    PEPLast -> do
      as' <- mapM (\(v, i) -> str l x v >>= \v -> return (v, i)) as
      return $ App (foldl (\a (b, i) -> App a b i) (PrimElim x') as') t (primElimIcit x')
    PEPFirst -> do
      as' <- mapM (\(v, i) -> str l x v >>= \v -> return (v, i)) as
      return $ foldl (\a (b, i) -> App a b i) (App (PrimElim x') t (primElimIcit x')) as'
strElim l x ELower t = return $ Lower t

strClos :: Lvl -> Lvl -> Clos -> Maybe Core
strClos l x c = str (l + 1) x $ vinst c (vvar l)

strClosLevel :: Lvl -> Lvl -> ClosLevel -> Maybe Level
strClosLevel l x c = strLevel (l + 1) x $ vinstlevel c (vvar l)

str :: Lvl -> Lvl -> Val -> Maybe Core
str l x = \case
  VU u -> U <$> strLevel l x u
  VULevel -> return ULevel
  VL0 -> return L0
  VLS v -> LS <$> str l x v
  VLMax a b -> LMax <$> str l x a <*> str l x b
  VNe h sp -> strHead l x h >>= \h -> foldrM (strElim l x) h sp
  VGlobal x' sp v -> foldrM (strElim l x) (Global x') sp
  VAbs y i b -> Abs y i <$> strClos l x b
  VPi x' i t u1 b u2 ->
    Pi x' i <$> str l x t <*> strLevel l x u1 <*> strClos l x b <*> strClosLevel l x u2
  VSigma x' t u1 b u2 ->
    Sigma x' <$> str l x t <*> strLevel l x u1 <*> strClos l x b <*> strClosLevel l x u2
  VPair a b -> Pair <$> str l x a <*> str l x b
  VLift t -> Lift <$> str l x t
  VLiftTerm t -> LiftTerm <$> str l x t
  VRefl -> return Refl
