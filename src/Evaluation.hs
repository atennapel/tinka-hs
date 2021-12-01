module Evaluation where

import Common
import Core
import Val
import Globals
import Metas
import Prims

import Data.Foldable (foldrM)
import Data.Bifunctor (first)

import Debug.Trace (trace)

vinst :: Clos -> Val -> Val
vinst (Clos e c) v = eval (v : e) c
vinst (Fun f) v = f v

vinstlevel :: ClosLevel -> Val -> VLevel
vinstlevel (ClosLevel e c) v = evallevel (v : e) c
vinstlevel (FunLevel f) v = f v

vapp :: Val -> Val -> Icit -> Val
vapp (VAbs _ _ b) v _ = vinst b v
vapp (VNe h sp) v i = VNe h (EApp v i : sp)
vapp (VGlobal x sp w) v i = VGlobal x (EApp v i : sp) (vapp w v i)
vapp _ _ _ = undefined

vappe :: Val -> Val -> Val
vappe a b = vapp a b Expl

velim :: Val -> Elim -> Val
velim v (EApp a i) = vapp v a i
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

vliftterm :: Val -> Val -> Val -> Val
vliftterm l a (VNe h (EPrimElim PELower _ : sp)) = VNe h sp
vliftterm l a (VGlobal x (EPrimElim PELower _ : sp) v) = VGlobal x sp (vliftterm l a v)
vliftterm l a v = VLiftTerm l a v

vprimelim :: PrimElimName -> [(Val, Icit)] -> Val -> Val
vprimelim PELower _ (VLiftTerm _ _ v) = v

vprimelim PELMax [(b, _)] VL0 = b
vprimelim PELMax [(VL0, _)] a = a
vprimelim PELMax [(VLS b, i)] (VLS a) = vprimelim PELMax [(b, i)] a

vprimelim PEIndBool [(l, _), (p, _), (t, _), (f, _)] VTrue = t
vprimelim PEIndBool [(l, _), (p, _), (t, _), (f, _)] VFalse = f

vprimelim x as (VNe h sp) = VNe h (EPrimElim x as : sp)
vprimelim p as (VGlobal x sp v) = VGlobal x (EPrimElim p as : sp) (vprimelim p as v)
vprimelim x as _ = undefined

vlower :: Val -> Val -> Val -> Val
vlower l a = vprimelim PELower [(l, Impl), (a, Impl)]

vfinmax :: Val -> Val -> Val
vfinmax l1 l2 = vprimelim PELMax [(l2, Expl)] l1

vlmax :: VLevel -> VLevel -> VLevel
vlmax (VFin t) (VFin t') = VFin (vfinmax t t')
vlmax VOmegaSuc _ = VOmegaSuc
vlmax _ VOmegaSuc = VOmegaSuc
vlmax _ _ = VOmega

force :: Val -> Val
force m@(VNe (HMeta x) sp) =
  case lookupMeta x of
    Solved _ _ _ _ v -> force (velimSp v sp)
    Unsolved _ _ -> m
force (VGlobal _ _ v) = force v
force v = v

forceLevel :: VLevel -> VLevel
forceLevel (VFin l) = VFin (force l)
forceLevel l = l

vappPruning :: Env -> Val -> Pruning -> Val
vappPruning e v p = case (e, p) of
  ([], []) -> v
  (t : e, Just i : p) -> vapp (vappPruning e v p) t i
  (t : e, Nothing : p) -> vappPruning e v p
  _ -> error "impossible"

evallevel :: Env -> Level -> VLevel
evallevel e Omega = VOmega
evallevel e OmegaSuc = VOmegaSuc
evallevel e (Fin t) = VFin (eval e t)

vprim :: PrimName -> Val
vprim PLiftTerm =
  vabsimpl "l" $ \l -> vabsimpl "A" $ \a -> vabs "x" $ \x -> vliftterm l a x
vprim x = VNe (HPrim x) []

eval :: Env -> Core -> Val
eval e c = case trace ("eval (" ++ show (length e) ++ ") " ++ show c) c of
  Var i | i < 0 || i >= length e ->
    error $ "eval var out of range: " ++ show i ++ "/" ++ show (length e)
  Var i -> e !! i
  Global x ->
    case getGlobal x of
      Just e -> VGlobal x [] $ gval e
      Nothing -> error $ "undefined global " ++ x ++ " in eval"
  Prim (Left x) -> vprim x
  Prim (Right x) -> evalprimelim x
  App f a i -> vapp (eval e f) (eval e a) i
  Abs x i b -> VAbs x i (Clos e b)
  Pi x i t u1 b u2 -> VPi x i (eval e t) (evallevel e u1) (Clos e b) (ClosLevel e u2)
  Sigma x t u1 b u2 -> VSigma x (eval e t) (evallevel e u1) (Clos e b) (ClosLevel e u2)
  Pair a b -> VPair (eval e a) (eval e b)
  Proj t p -> vproj (eval e t) p
  U l -> VU (evallevel e l)
  Let x t v b -> eval (eval e v : e) b
  Meta x -> VMeta x
  AppPruning t p -> vappPruning e (eval e t) p

evalprimelim :: PrimElimName -> Val
evalprimelim PEAbsurd =
  vabsimpl "l" $ \l -> 
  vabsimpl "A" $ \a ->
  vabs "v" $ \v ->
  vprimelim PEAbsurd [(l, Impl), (a, Impl)] v
evalprimelim PELower =
  vabsimpl "l" $ \l -> vabsimpl "A" $ \a -> vabs "x" $ \x -> vlower l a x
evalprimelim PELMax =
  vabs "a" $ \a -> vabs "b" $ \b -> vfinmax a b
evalprimelim PEIndBool =
  vabsimpl "l" $ \l ->
  vabs "P" $ \p ->
  vabs "t" $ \t ->
  vabs "f" $ \f ->
  vabs "b" $ \b ->
  vprimelim PEIndBool [(l, Impl), (p, Expl), (t, Expl), (f, Expl)] b

data QuoteLevel = KeepGlobals | Full

quoteHead :: Lvl -> Head -> Core
quoteHead k (HVar l) = Var (k - l - 1)
quoteHead k (HPrim x) = Prim (Left x)
quoteHead k (HMeta x) = Meta x

quoteElim :: QuoteLevel -> Lvl -> Elim -> Core -> Core
quoteElim ql k (EApp v i) t = App t (quoteWith ql k v) i
quoteElim ql k (EProj p) t = Proj t p
quoteElim ql k (EPrimElim x as) t =
  case primElimPosition x of
    PEPLast -> App (foldl (\a (b, i) -> App a b i) (Prim (Right x)) (map (first (quoteWith ql k)) as)) t (primElimIcit x)
    PEPFirst -> foldl (\a (b, i) -> App a b i) (App (Prim (Right x)) t (primElimIcit x)) (map (first (quoteWith ql k)) as)

quoteClos :: QuoteLevel -> Lvl -> Clos -> Core
quoteClos ql k c = quoteWith ql (k + 1) $ vinst c (vvar k)

quoteClosLevel :: QuoteLevel -> Lvl -> ClosLevel -> Level
quoteClosLevel ql k c = quoteLevelWith ql (k + 1) $ vinstlevel c (vvar k)

quoteLevelWith :: QuoteLevel -> Lvl -> VLevel -> Level
quoteLevelWith ql k VOmega = Omega
quoteLevelWith ql k VOmegaSuc = OmegaSuc
quoteLevelWith ql k (VFin v) = Fin (quoteWith ql k v)

quoteLevel :: Lvl -> VLevel -> Level
quoteLevel = quoteLevelWith KeepGlobals

quoteWith :: QuoteLevel -> Lvl -> Val -> Core
quoteWith ql k (VU l) = U (quoteLevelWith ql k l)
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
convLevel k VOmegaSuc VOmegaSuc = True
convLevel _ _ _ = False

conv :: Lvl -> Val -> Val -> Bool
conv k a b = -- trace ("conv " ++ show (quote k a) ++ " ~ " ++ show (quote k b)) $ do
  case (a, b) of
    (VU l1, VU l2) -> convLevel k l1 l2
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
    
    (VUnit, v) -> True
    (v, VUnit) -> True

    (VLiftTerm l a x, y) -> conv k x (vlower l a y)
    (y, VLiftTerm l a x) -> conv k (vlower l a y) x

    (VGlobal x sp v, VGlobal x' sp' v') | x == x' ->
      convSp k sp sp' || conv k v v'
    (VGlobal _ _ v, VGlobal _ _ v') -> conv k v v'
    (VGlobal _ _ v, v') -> conv k v v'
    (v, VGlobal _ _ v') -> conv k v v'
    (_, _) -> False

primType :: PrimName -> (Val, VLevel)
primType PVoid = (VType VL0, VFin (VLS VL0))
primType PUnitType = (VType VL0, VFin (VLS VL0))
primType PUnit = (VUnitType, VFin VL0)
primType PBool = (VType VL0, VFin (VLS VL0))
primType PTrue = (VBool, VFin VL0)
primType PFalse = (VBool, VFin VL0)
primType PLevel = (VU VOmega, VOmegaSuc)
primType PL0 = (VULevel, VOmega)
primType PLS = (vfun VULevel VOmega (const VOmega) VULevel, VOmega)
-- {l : Level} -> Type l -> Type (S l)
primType PLift = (vpimpl "l" VULevel VOmega (VFin . VLS . VLS) $ \l -> vfun (VType l) (VFin $ VLS l) (\_ -> VFin $ VLS (VLS l)) (VType $ VLS l), VOmega)
-- {l : Level} {A : Type l} -> A -> Lift {l} A
primType PLiftTerm =
  (vpimpl "l" VULevel VOmega (VFin . VLS) $ \l -> vpimpl "A" (VType l) (VFin $ VLS l) (\_ -> VFin $ VLS l) $ \a -> vfun a (VFin l) (\_ -> VFin $ VLS l) (VLift l a), VOmega)
-- {l : Level} {A : Type l} {B : Type l} -> A -> B -> Type l
primType PHEq =
  (vpimpl "l" VULevel VOmega (VFin . VLS) $ \l ->
   vpimpl "A" (VType l) (VFin $ VLS l) (\_ -> VFin $ VLS l) $ \a ->
   vpimpl "B" (VType l) (VFin $ VLS l) (\_ -> VFin $ VLS l) $ \b ->
   vfun a (VFin l)  (\_ -> VFin $ VLS l) $
   vfun b (VFin l) (\_ -> VFin $ VLS l) (VType l), VOmega)
-- {l : Level} {A : Type l} {x : A} -> HEq {l} {A} {A} x x
primType PHRefl =
  (vpimpl "l" VULevel VOmega (VFin . VLS) $ \l ->
   vpimpl "A" (VType l) (VFin $ VLS l) (\_ -> VFin l) $ \a ->
   vpimpl "x" a (VFin l) (\_ -> VFin l) $ \x ->
   VHEq l a a x x, VOmega)

primElimType :: PrimElimName -> (Val, VLevel)
-- {l : Level} {A : Type l} -> Void -> A
primElimType PEAbsurd =
  (vpimpl "l" VULevel VOmega (VFin . VLS) $ \l -> vpimpl "A" (VType l) (VFin (VLS l)) (\_ -> VFin l) $ \a -> vfun VVoid (VFin VL0) (\_ -> VFin l) a, VOmega)
primElimType PELower =
  (vpimpl "l" VULevel VOmega (VFin . VLS) $ \l -> vpimpl "A" (VType l) (VFin $ VLS l) (\_ -> VFin $ VLS l) $ \a -> vfun (VLift l a) (VFin $ VLS l) (\_ -> VFin l) a, VOmega)
primElimType PELMax =
  (vfun VULevel VOmega (const VOmega) $ vfun VULevel VOmega (const VOmega) VULevel, VOmega)
{-
  {l : Level}
  (P : Bool -> Type l)
  (t : P True)
  (f : P False)
  (b : Bool)
  -> P b
-}
primElimType PEIndBool =
  (vpimpl "l" VULevel VOmega (VFin . VLS) $ \l ->
   vpi "P" (vfun VBool (VFin VL0) (\_ -> VFin (VLS l)) (VType l)) (VFin (VLS l)) (\_ -> VFin l) $ \p ->
   vfun (vapp p VTrue Expl) (VFin l) (\_ -> VFin l) $
   vfun (vapp p VFalse Expl) (VFin l) (\_ -> VFin l) $
   vpi "b" VBool (VFin VL0) (\_ -> VFin l) $ \b -> vapp p b Expl, VOmega)

strLevel :: Lvl -> Lvl -> VLevel -> Maybe Level
strLevel l x = \case
  VOmega -> return Omega
  VOmegaSuc -> return OmegaSuc
  VFin t -> Fin <$> str l x t

strHead :: Lvl -> Lvl -> Head -> Maybe Core
strHead l x (HPrim x') = return $ Prim (Left x')
strHead l x (HMeta x') = return $ Meta x'
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
      return $ App (foldl (\a (b, i) -> App a b i) (Prim $ Right x') as') t (primElimIcit x')
    PEPFirst -> do
      as' <- mapM (\(v, i) -> str l x v >>= \v -> return (v, i)) as
      return $ foldl (\a (b, i) -> App a b i) (App (Prim $ Right x') t (primElimIcit x')) as'

strClos :: Lvl -> Lvl -> Clos -> Maybe Core
strClos l x c = str (l + 1) x $ vinst c (vvar l)

strClosLevel :: Lvl -> Lvl -> ClosLevel -> Maybe Level
strClosLevel l x c = strLevel (l + 1) x $ vinstlevel c (vvar l)

str :: Lvl -> Lvl -> Val -> Maybe Core
str l x = \case
  VU u -> U <$> strLevel l x u
  VNe h sp -> strHead l x h >>= \h -> foldrM (strElim l x) h sp
  VGlobal x' sp v -> foldrM (strElim l x) (Global x') sp
  VAbs y i b -> Abs y i <$> strClos l x b
  VPi x' i t u1 b u2 ->
    Pi x' i <$> str l x t <*> strLevel l x u1 <*> strClos l x b <*> strClosLevel l x u2
  VSigma x' t u1 b u2 ->
    Sigma x' <$> str l x t <*> strLevel l x u1 <*> strClos l x b <*> strClosLevel l x u2
  VPair a b -> Pair <$> str l x a <*> str l x b
