module Evaluation where

import Data.Either (fromLeft, fromRight)
import Data.Coerce (coerce)
import qualified Data.IntMap as M

import Common
import Core
import Levels
import Val
import Prims
import Globals
import Metas

-- eval
vinst :: Clos Val -> Val -> Val
vinst (Clos e t) v = eval (Right v : e) t
vinst (Fun f) v = f v

vinstLevel :: Clos VFinLevel -> VFinLevel -> Val
vinstLevel (Clos e t) v = eval (Left v : e) t
vinstLevel (Fun f) v = f v

vinstCL :: ClosLvl -> VFinLevel -> VLevel
vinstCL (ClosLvl e t) v = level (Left v : e) t
vinstCL (FunLvl f) v = f v

finLevel :: Env -> FinLevel -> VFinLevel
finLevel e = \case
  FLVar i | i < 0 || coerce i >= length e -> error $ "level var out of range: " ++ show i
  FLVar i -> fromLeft undefined (e !! coerce i)
  FLZ -> mempty
  FLS i -> addToVFinLevel 1 (finLevel e i)
  FLMax i j -> finLevel e i <> finLevel e j
  FLMeta m -> vFinMeta m

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

velim :: Val -> Elim -> Val
velim v (EApp a i) = vapp v a i
velim v (EAppLvl a) = vappLevel v a
velim v (EProj p) = vproj v p
velim v (EPrimElim x as) = vprimelim x as v

velimSp :: Val -> Sp -> Val
velimSp v [] = v
velimSp v (e : as) = velim (velimSp v as) e

force :: Val -> Val
force (VNe (HMeta m) sp) | Solved t _ <- lookupMeta m = force (velimSp t sp)
force (VGlobal _ _ v) = force v
force v = v

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

vliftterm :: VFinLevel -> VFinLevel -> Val -> Val -> Val
vliftterm l k a (VNe h (EPrimElim PELower _ : sp)) = VNe h sp
vliftterm l k a (VGlobal x (EPrimElim PELower _ : sp) v) = VGlobal x sp (vliftterm l k a v)
vliftterm l k a v = VLiftTerm l k a v

vprimelim :: PrimElimName -> [Either VFinLevel (Val, Icit)] -> Val -> Val
vprimelim PELower _ (VLiftTerm _ _ _ v) = v

vprimelim PEIndBool [_, _, Right (t, _), _] VTrue = t
vprimelim PEIndBool [_, _, _, Right (f, _)] VFalse = f

vprimelim PEElimHEq [_, _, _, _, _, Right (refl, _), _] (VHRefl _ _ _) = refl

vprimelim x as (VNe h sp) = VNe h (EPrimElim x as : sp)
vprimelim p as (VGlobal x sp v) = VGlobal x (EPrimElim p as : sp) (vprimelim p as v)
vprimelim x as _ = undefined

vlower :: VFinLevel -> VFinLevel -> Val -> Val -> Val
vlower l k a = vprimelim PELower [Left l, Left k, Right (a, Impl)]

vprim :: PrimName -> Val
vprim PLiftTerm =
  vlamlvl "l" $ \l -> vlamlvl "k" $ \k -> vlamimpl "A" $ \a -> vlam "x" $ \x -> vliftterm l k a x
vprim x = VNe (HPrim x) []

vmeta :: MetaVar -> Val
vmeta m = case lookupMeta m of
  Solved v _ -> v
  Unsolved -> VMeta m

vinsertedmeta :: Env -> MetaVar -> [Maybe Icit] -> Val
vinsertedmeta env m bds = go env bds
  where
    go [] [] = vmeta m
    go (Right t : env) (Just i : bds) = vapp (go env bds) t i
    go (Left l : env) (Just i : bds) = vappLevel (go env bds) l
    go (_ : env) (Nothing : bds) = go env bds
    go _ _ = undefined

eval :: Env -> Tm -> Val
eval e = \case
  Var i | i < 0 || coerce i >= length e -> error $ "var out of range: " ++ show i
  Var i -> fromRight undefined (e !! coerce i)
  Global x ->
    case getGlobal x of
      Just e -> gVal e
      Nothing -> undefined
  Prim (Left x) -> vprim x
  Prim (Right x) -> evalprimelim x
  App a b i -> vapp (eval e a) (eval e b) i
  Lam x i b -> VLam x i (Clos e b)
  Pi x i t u1 b u2 -> VPi x i (eval e t) (level e u1) (Clos e b) (level e u2)
  AppLvl t l -> vappLevel (eval e t) (finLevel e l)
  LamLvl x b -> VLamLvl x (Clos e b)
  PiLvl x b u -> VPiLvl x (Clos e b) (ClosLvl e u)
  Proj t p -> vproj (eval e t) p
  Pair a b -> VPair (eval e a) (eval e b)
  Sigma x t u1 b u2 -> VSigma x (eval e t) (level e u1) (Clos e b) (level e u2)
  Let x _ v b -> eval (Right (eval e v) : e) b
  Type l -> VType (level e l)
  Meta m -> vmeta m
  InsertedMeta m bds -> vinsertedmeta e m bds

evalprimelim :: PrimElimName -> Val
evalprimelim PEAbsurd =
  vlamlvl "l" $ \l -> 
  vlamimpl "A" $ \a ->
  vlam "v" $ \v ->
  vprimelim PEAbsurd [Left l, Right (a, Impl)] v
evalprimelim PELower =
  vlamlvl "l" $ \l ->
  vlamlvl "k" $ \k ->
  vlamimpl "A" $ \a ->
  vlam "x" $ \x ->
  vlower l k a x
evalprimelim PEIndBool =
  vlamlvl "l" $ \l ->
  vlam "P" $ \p ->
  vlam "t" $ \t ->
  vlam "f" $ \f ->
  vlam "b" $ \b ->
  vprimelim PEIndBool [Left l, Right (p, Expl), Right (t, Expl), Right (f, Expl)] b
evalprimelim PEElimHEq =
  vlamlvl "l" $ \l ->
  vlamlvl "k" $ \k ->
  vlamimpl "A" $ \a ->
  vlamimpl "x" $ \x ->
  vlam "P" $ \p ->
  vlam "refl" $ \refl ->
  vlamimpl "y" $ \y ->
  vlam "p" $ \pp ->
  vprimelim PEElimHEq [Left l, Left k, Right (a, Impl), Right (x, Impl), Right (p, Expl), Right (refl, Expl), Right (y, Impl)] p

-- quote
data QuoteLevel = Full | KeepGlobals

quoteFinLevel :: Lvl -> VFinLevel -> FinLevel
quoteFinLevel l (VFL n xs ys) =
  M.foldlWithKey (\i x n -> flmax i (addToFinLevel n (FLMeta (LMetaVar x)))) vars ys
  where
    vars = M.foldlWithKey
      (\i x n -> flmax i (addToFinLevel n (FLVar (lvlToIx l (Lvl x)))))
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
quoteHead k (HMeta x) = Meta x

quoteElim :: QuoteLevel -> Lvl -> Elim -> Tm -> Tm
quoteElim ql l (EApp v i) t = App t (quoteWith ql l v) i
quoteElim ql l (EAppLvl k) t = AppLvl t (quoteFinLevel l k)
quoteElim ql l (EProj p) t = Proj t p
quoteElim ql l (EPrimElim x as) t =
  case primElimPosition x of
    PEPLast -> App (foldl app (Prim (Right x)) as) t (primElimIcit x)
    PEPFirst -> foldl app (App (Prim (Right x)) t (primElimIcit x)) as
  where
    app :: Tm -> Either VFinLevel (Val, Icit) -> Tm
    app a (Left lv) = AppLvl a (quoteFinLevel l lv)
    app a (Right (b, i)) = App a (quoteWith ql l b) i

quoteWith :: QuoteLevel -> Lvl -> Val -> Tm
quoteWith ql l = go l
  where
    go l = \case
      VNe h sp -> foldr (quoteElim ql l) (quoteHead l h) sp
      VGlobal h sp v ->
        case ql of
          Full -> go l v
          KeepGlobals -> Global h
      VLam x i b -> Lam x i (go (l + 1) (vinst b (VVar l)))
      VPi x i t u1 b u2 -> Pi x i (go l t) (quoteLevel l u1) (go (l + 1) (vinst b (VVar l))) (quoteLevel l u2)
      VLamLvl x b -> LamLvl x (go (l + 1) (vinstLevel b (vFinLevelVar l)))
      VPiLvl x b u -> let v = vFinLevelVar l in PiLvl x (go (l + 1) (vinstLevel b v)) (quoteLevel (l + 1) (vinstCL u v))
      VPair a b -> Pair (go l a) (go l b)
      VSigma x t u1 b u2 -> Sigma x (go l t) (quoteLevel l u1) (go (l + 1) (vinst b (VVar l))) (quoteLevel l u2)
      VType i -> Type (quoteLevel l i)

quote :: Lvl -> Val -> Tm
quote = quoteWith KeepGlobals

nf :: Tm -> Tm
nf = quoteWith Full 0 . eval []

-- conv
eqvProj :: ProjType -> ProjType -> Bool
eqvProj (PNamed _ i) (PNamed _ i') = i == i'
eqvProj Fst (PNamed _ 0) = True
eqvProj (PNamed _ 0) Fst = True
eqvProj p p' = p == p'

convElim :: Lvl -> Elim -> Elim -> Bool
convElim k (EApp v _) (EApp v' _) = conv k v v'
convElim k (EAppLvl v) (EAppLvl v') = v == v'
convElim k (EProj p) (EProj p') = eqvProj p p'
convElim k (EPrimElim x1 as1) (EPrimElim x2 as2) =
  x1 == x2 && and (zipWith (go k) as1 as2)
  where
    go _ (Left l) (Left l') = l == l'
    go k (Right (v, _)) (Right (v', _)) = conv k v v'
    go _ _ _ = False
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

  (VPi _ i t u1 b u2, VPi _ i' t' u1' b' u2') | i == i' && u1 == u1' && u2 == u2' ->
    conv l t t' && convClos l b b'
  (VPiLvl _ b u, VPiLvl _ b' u') ->
    let v = vFinLevelVar l in convClosLevel l b b' && vinstCL u v == vinstCL u' v
  (VSigma _ t u1 b u2, VSigma _ t' u1' b' u2') | u1 == u1' && u2 == u2' ->
    conv l t t' && convClos l b b'

  (VLam _ _ b, VLam _ _ b') -> convClos l b b'
  (VLam _ i b, b') -> let v = VVar l in conv (l + 1) (vinst b v) (vapp b' v i)
  (b', VLam _ i b) -> let v = VVar l in conv (l + 1) (vapp b' v i) (vinst b v)
  
  (VLamLvl _ b, VLamLvl _ b') -> convClosLevel l b b'
  (VLamLvl _ b, b') -> let v = vFinLevelVar l in conv (l + 1) (vinstLevel b v) (vappLevel b' v)
  (b', VLamLvl _ b) -> let v = vFinLevelVar l in conv (l + 1) (vappLevel b' v) (vinstLevel b v)

  (VPair a b, VPair c d) -> conv l a c && conv l b d
  (VPair a b, x) -> conv l a (vfst x) && conv l b (vsnd x)
  (x, VPair a b) -> conv l (vfst x) a && conv l (vsnd x) b

  (VUnit, v) -> True
  (v, VUnit) -> True

  (VLiftTerm lv k a x, y) -> conv l x (vlower lv k a y)
  (y, VLiftTerm lv k a x) -> conv l (vlower lv k a y) x

  (VNe h sp, VNe h' sp') | h == h' -> convSp l sp sp'
  (VGlobal x sp v, VGlobal x' sp' v') | x == x' -> convSp l sp sp' || conv l v v'
  (VGlobal _ _ v, VGlobal _ _ v') -> conv l v v'
  (VGlobal _ _ v, v') -> conv l v v'
  (v, VGlobal _ _ v') -> conv l v v'
  _ -> False

-- prim types
primType :: PrimName -> (Val, VLevel)
primType PVoid = (VType vFLZ, VFinLevel (vFLS mempty))
primType PUnitType = (VType vFLZ, VFinLevel (vFLS mempty))
primType PUnit = (VUnitType, VFinLevel mempty)
primType PBool = (VType vFLZ, VFinLevel (vFLS mempty))
primType PTrue = (VBool, VFinLevel mempty)
primType PFalse = (VBool, VFinLevel mempty)
-- <l k> -> Type l -> Type (max l k)
primType PLift =
  (vpilvl "l" (const VOmega) $ \l ->
  vpilvl "k" (\k -> VFinLevel (vFLS (l <> k))) $ \k ->
  vfun (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS (l <> k))) $
  VTypeFin $ l <> k, VOmega)
-- <l k> {A : Type l} -> A -> Lift <l> <k> A
primType PLiftTerm =
  (vpilvl "l" (const VOmega) $ \l ->
  vpilvl "k" (\k -> VFinLevel (vFLS l <> k)) $ \k ->
  vpimpl "A" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (l <> k)) $ \a ->
  vfun a (VFinLevel l) (VFinLevel (l <> k)) $
  VLift l k a, VOmega)
-- <l> {A : Type l} {B : Type l} -> A -> B -> Type l
primType PHEq =
  (vpilvl "l" (\l -> VFinLevel (vFLS l)) $ \l ->
  vpimpl "A" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \a ->
  vpimpl "B" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \b ->
  vfun a (VFinLevel l) (VFinLevel (vFLS l)) $
  vfun b (VFinLevel l) (VFinLevel (vFLS l)) $
  VTypeFin l, VOmega)
-- <l> {A : Type l} {x : A} -> HEq {l} {A} {A} x x
primType PHRefl =
  (vpilvl "l" (\l -> VFinLevel (vFLS l)) $ \l ->
  vpimpl "A" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel l) $ \a ->
  vpimpl "x" a (VFinLevel l) (VFinLevel l) $ \x ->
  VHEq l a a x x, VOmega)

primElimType :: PrimElimName -> (Val, VLevel)
-- <l> {A : Type l} -> Void -> A
primElimType PEAbsurd =
  (vpilvl "l" (\l -> VFinLevel (vFLS l)) $ \l ->
  vpimpl "A" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel l) $ \a ->
  vfun VVoid vFLZ (VFinLevel l) $
  a, VOmega)
-- <l> <k> {A : Type l} -> Lift <l> <k> A -> A
primElimType PELower =
  (vpilvl "l" (const VOmega) $ \l ->
  vpilvl "k" (\k -> VFinLevel (vFLS l <> k)) $ \k ->
  vpimpl "A" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (l <> k)) $ \a ->
  vfun (VLift l k a) (VFinLevel (l <> k)) (VFinLevel l) $
  a, VOmega)
{-
<l>
(P : Bool -> Type l)
(t : P True)
(f : P False)
(b : Bool)
-> P b
-}
primElimType PEIndBool =
  (vpilvl "l" (\l -> VFinLevel (vFLS l)) $ \l ->
  vpi "P" (vfun VBool vFLZ (VFinLevel (vFLS l)) (VTypeFin l)) (VFinLevel (vFLS l)) (VFinLevel l) $ \p ->
  vfun (vapp p VTrue Expl) (VFinLevel l) (VFinLevel l) $
  vfun (vapp p VFalse Expl) (VFinLevel l) (VFinLevel l) $
  vpi "b" VBool vFLZ (VFinLevel l) $ \b ->
  vapp p b Expl, VOmega)
{-
<l k>
{A : Type l}
{x : A}
(P : {y : A} -> HEq <l> {A} {A} x y -> Type k)
(refl : P {x} (HRefl <l> {A} {x}))
{y : A}
(p : HEq <l> {A} {A} x y)
P {y} p
-}
primElimType PEElimHEq =
  (vpilvl "l" (const VOmega) $ \l ->
  vpilvl "k" (\k -> VFinLevel (vFLS (l <> k))) $ \k ->
  vpimpl "A" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (l <> vFLS k)) $ \a ->
  vpimpl "x" a (VFinLevel l) (VFinLevel (l <> vFLS k)) $ \x ->
  vpi "P" (vpimpl "y" a (VFinLevel l) (VFinLevel (l <> vFLS k)) $ \y -> vfun (VHEq l a a x y) (VFinLevel l) (VFinLevel (vFLS k)) $ VTypeFin k) (VFinLevel (vFLS k)) (VFinLevel (l <> k)) $ \p ->
  vfun (vapp (vapp p x Impl) (VHRefl l a x) Expl) (VFinLevel k) (VFinLevel (l <> k)) $
  vpimpl "y" a (VFinLevel l) (VFinLevel (l <> k)) $ \y ->
  vpi "p" (VHEq l a a x y) (VFinLevel l) (VFinLevel k) $ \pp ->
  vapp (vapp p y Impl) pp Expl, VOmega)
