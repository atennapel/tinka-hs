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
vapp a b _ = error $ "vapp failed " ++ show a ++ " @ " ++ show b

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

forceMetas :: Val -> Val
forceMetas (VNe (HMeta m) sp) | Solved t _ <- lookupMeta m = forceMetas (velimSp t sp)
forceMetas v = v

forceLevel :: VLevel -> VLevel
forceLevel (VFinLevel l) = VFinLevel (forceFinLevel l)
forceLevel l = l

forceFinLevel :: VFinLevel -> VFinLevel
forceFinLevel (VFL n xs ys) = foldr (<>) (VFL n xs mempty) $ map go $ M.assocs ys
  where
    go :: (Int, Int) -> VFinLevel
    go (m, n) = case lookupLMeta (coerce m) of
      LUnsolved {} -> addToVFinLevel n (vFinMeta $ coerce m)
      LSolved v -> forceFinLevel (addToVFinLevel n v)

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

vprimelim :: PrimElimName -> [Either VFinLevel (Val, Icit)] -> Val -> Val
vprimelim PELower _ (VLiftTerm _ _ _ v) = v

vprimelim PEIndBool [_, _, Right (t, _), _] VTrue = t
vprimelim PEIndBool [_, _, _, Right (f, _)] VFalse = f

vprimelim PEIfDesc [_, _, Right (x, _), Right (y, _)] VTrue = x
vprimelim PEIfDesc [_, _, Right (x, _), Right (y, _)] VFalse = y

vprimelim PEElimId [_, _, _, _, _, Right (refl, _), _] VRefl = refl

-- elimData <k> <l> {I} {D} P alg {i} (Con x) = alg {Data <l> {I} D} (\{i} x. x) (\{i} x. elimData <k> <l> {I} {D} P alg {i} x) {i} x
vprimelim PEElimData as@[_, Left l, Right (i, _), Right (d, _), _, Right (alg, _), Right (ii, _)] (VCon x) =
  vapp (vapp (vapp (vapp (vapp alg (vlam "i" $ \ii -> VData l i d ii) (Impl ImplUnif)) (vlamimpl "i" $ \ii -> vlam "x" $ \x -> x) Expl) (vlamimpl "i" $ \ii -> vlam "x" $ \x -> vprimelim PEElimData (init as ++ [Right (ii, Impl ImplUnif)]) x) Expl) ii (Impl ImplUnif)) x Expl

-- Ex (Var i) X = X i
vprimelim PEEx [_, _, Right (x, _)] (VDVar j) = vapp x j Expl
-- Ex (Arg A K) X = (x : A) -> Ex (K x) X
vprimelim PEEx [Left l, Right (i, _), Right (x, _)] (VArg a k) =
  vpi "x" a (VFinLevel l) (VFinLevel l) $ \xx -> vex l i x (vapp k (VLiftTerm (vFLS l) l a xx) Expl)
-- Ex (Par A B) X = Ex A X ** Ex B X
vprimelim PEEx [Left l, Right (i, _), Right (x, _)] (VInd a b) =
  vpairty (vex l i x a) (VFinLevel l) (VFinLevel l) (vex l i x b)

-- El (Var j) X i = Id j i
vprimelim PEEl [Left l, Right (i, _), Right (x, _), Right (ii, _)] (VDVar j) = VId l i i j ii
-- El (Arg A K) X i = (x : A) ** El (K x) X i
vprimelim PEEl [Left l, Right (i, _), Right (x, _), Right (ii, _)] (VArg a k) =
  vsigma "x" a (VFinLevel l) (VFinLevel l) $ \xx -> vel l i x ii (vapp k (VLiftTerm (vFLS l) l a xx) Expl)
-- El (Par A B) X i = Ex A X ** El B X i
vprimelim PEEl [Left l, Right (i, _), Right (x, _), Right (ii, _)] (VInd a b) =
  vpairty (vex l i x a) (VFinLevel l) (VFinLevel l) (vel l i x ii b)

-- mapDEx (Var j) f x = f {j} x
vprimelim PEMapDEx [Left l, Right (i, _), Right (a, _), Right (b, _), Right (fn, _), Right (x, _)] (VDVar j) = vapp (vapp fn j (Impl ImplUnif)) x Expl
-- mapDEx (Arg A K) f g = \x. mapDEx (K x) f (g x)
vprimelim PEMapDEx [Left l, Right (i, _), Right (a, _), Right (b, _), Right (fn, _), Right (g, _)] (VArg ta k) =
  vlam "x" $ \x -> vmapdex l i (vapp k (VLiftTerm (vFLS l) l a x) Expl) a b fn (vapp g x Expl)
-- mapDEx (Par A B) f (x, y) = (mapDEx A f x, mapDEx B f y)
vprimelim PEMapDEx [Left l, Right (i, _), Right (a, _), Right (b, _), Right (fn, _), Right (x, _)] (VInd ta tb) =
  VPair (vmapdex l i ta a b fn (vfst x)) (vmapdex l i tb a b fn (vsnd x))

-- mapD (Var j) f Refl = Refl
vprimelim PEMapD [Left l, Right (i, _), Right (a, _), Right (b, _), Right (fn, _), Right (ii, _), Right (x, _)] (VDVar j) = VRefl
-- mapD (Arg A K) f (x, y) = (x, mapD (K x) f y)
vprimelim PEMapD [Left l, Right (i, _), Right (a, _), Right (b, _), Right (fn, _), Right (ii, _), Right (x, _)] (VArg ta k) =
  VPair (vfst x) (vmapd l i (vapp k (VLiftTerm (vFLS l) l a (vfst x)) Expl) a b fn ii (vsnd x))
-- mapD (Par A B) f (x, y) = (mapDEx A f x, mapD B y)
vprimelim PEMapD [Left l, Right (i, _), Right (a, _), Right (b, _), Right (fn, _), Right (ii, _), Right (x, _)] (VInd ta tb) =
  VPair (vmapdex l i ta a b fn (vfst x)) (vmapd l i tb a b fn ii (vsnd x))

vprimelim x as (VNe h sp) = VNe h (EPrimElim x as : sp)
vprimelim p as (VGlobal x sp v) = VGlobal x (EPrimElim p as : sp) (vprimelim p as v)
vprimelim x as v = error $ "impossible vprimelim " ++ show x ++ " " ++ show v

vliftterm :: VFinLevel -> VFinLevel -> Val -> Val -> Val
vliftterm k l a (VNe h (EPrimElim PELower _ : sp)) = VNe h sp
vliftterm k l a (VGlobal x (EPrimElim PELower _ : sp) v) = VGlobal x sp (vliftterm k l a v)
vliftterm k l a v = VLiftTerm k l a v

vlower :: VFinLevel -> VFinLevel -> Val -> Val -> Val
vlower k l a = vprimelim PELower [Left k, Left l, Right (a, Impl ImplUnif)]

vex :: VFinLevel -> Val -> Val -> Val -> Val
vex l i x = vprimelim PEEx [Left l, Right (i, Impl ImplUnif), Right (x, Expl)]

vel :: VFinLevel -> Val -> Val -> Val -> Val -> Val
vel l i x ii = vprimelim PEEl [Left l, Right (i, Impl ImplUnif), Right (x, Expl), Right (ii, Expl)]

vmapd :: VFinLevel -> Val -> Val -> Val -> Val -> Val -> Val -> Val -> Val
vmapd l i d a b fn ii x = vprimelim PEMapD [Left l, Right (i, Impl ImplUnif), Right (a, Impl ImplUnif), Right (b, Impl ImplUnif), Right (fn, Expl), Right (ii, Impl ImplUnif), Right (x, Expl)] d

vmapdex :: VFinLevel -> Val -> Val -> Val -> Val -> Val -> Val -> Val
vmapdex l i d a b fn x = vprimelim PEMapDEx [Left l, Right (i, Impl ImplUnif), Right (a, Impl ImplUnif), Right (b, Impl ImplUnif), Right (fn, Expl), Right (x, Expl)] d

vifdesc :: VFinLevel -> Val -> Val -> Val -> Val -> Val
vifdesc l i x y = vprimelim PEIfDesc [Left l, Right (i, Impl ImplUnif), Right (x, Expl), Right (y, Expl)]

vprim :: PrimName -> Val
vprim PLiftTerm =
  vlamlvl "k" $ \k -> vlamlvl "l" $ \l -> vlamimpl "A" $ \a -> vlam "x" $ \x -> vliftterm k l a x
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
      Just e -> VGlobal x [] (gVal e)
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
  Con t -> VCon (eval e t)
  Refl -> VRefl
  NatLit n -> VNatLit n
  LabelLit x -> VLabelLit x
  Let x _ _ v b -> eval (Right (eval e v) : e) b
  Type l -> VType (level e l)
  Meta m -> vmeta m
  InsertedMeta m bds -> vinsertedmeta e m bds

evalprimelim :: PrimElimName -> Val
evalprimelim PEAbsurd =
  vlamlvl "l" $ \l -> 
  vlamimpl "A" $ \a ->
  vlam "v" $ \v ->
  vprimelim PEAbsurd [Left l, Right (a, Impl ImplUnif)] v
evalprimelim PELower =
  vlamlvl "k" $ \k ->
  vlamlvl "l" $ \l ->
  vlamimpl "A" $ \a ->
  vlam "x" $ \x ->
  vlower k l a x
evalprimelim PEIndBool =
  vlamlvl "l" $ \l ->
  vlam "P" $ \p ->
  vlam "t" $ \t ->
  vlam "f" $ \f ->
  vlam "b" $ \b ->
  vprimelim PEIndBool [Left l, Right (p, Expl), Right (t, Expl), Right (f, Expl)] b
evalprimelim PEIfDesc =
  vlamlvl "l" $ \l ->
  vlamimpl "I" $ \i ->
  vlam "x" $ \x ->
  vlam "y" $ \y ->
  vlam "b" $ \b ->
  vifdesc l i x y b
evalprimelim PEElimId =
  vlamlvl "k" $ \k ->
  vlamlvl "l" $ \l ->
  vlamimpl "A" $ \a ->
  vlamimpl "x" $ \x ->
  vlam "P" $ \p ->
  vlam "refl" $ \refl ->
  vlamimpl "y" $ \y ->
  vlam "p" $ \pp ->
  vprimelim PEElimId [Left k, Left l, Right (a, Impl ImplUnif), Right (x, Impl ImplUnif), Right (p, Expl), Right (refl, Expl), Right (y, Impl ImplUnif)] pp
evalprimelim PEEx =
  vlamlvl "l" $ \l ->
  vlamimpl "I" $ \i ->
  vlam "X" $ \x ->
  vlam "D" $ \d ->
  vex l i x d
evalprimelim PEEl =
  vlamlvl "l" $ \l ->
  vlamimpl "I" $ \i ->
  vlam "X" $ \x ->
  vlam "i" $ \ii ->
  vlam "D" $ \d ->
  vel l i x ii d
evalprimelim PEMapD =
  vlamlvl "l" $ \l ->
  vlamimpl "I" $ \i ->
  vlam "D" $ \d ->
  vlamimpl "A" $ \a ->
  vlamimpl "B" $ \b ->
  vlam "fn" $ \fn ->
  vlamimpl "i" $ \ii ->
  vlam "x" $ \x ->
  vmapd l i d a b fn ii x
evalprimelim PEMapDEx =
  vlamlvl "l" $ \l ->
  vlamimpl "I" $ \i ->
  vlam "D" $ \d ->
  vlamimpl "A" $ \a ->
  vlamimpl "B" $ \b ->
  vlam "fn" $ \fn ->
  vlam "x" $ \x ->
  vmapdex l i d a b fn x
evalprimelim PEElimData =
  vlamlvl "k" $ \k ->
  vlamlvl "l" $ \l ->
  vlamimpl "I" $ \i ->
  vlamimpl "D" $ \d ->
  vlam "P" $ \p ->
  vlam "alg" $ \alg ->
  vlamimpl "i" $ \ii ->
  vlam "x" $ \x ->
  vprimelim PEElimData [Left k, Left l, Right (i, Impl ImplUnif), Right (d, Impl ImplUnif), Right (p, Expl), Right (alg, Expl), Right (ii, Impl ImplUnif)] x

-- quote
data QuoteLevel = Full | KeepGlobals

quoteFinLevel :: Lvl -> VFinLevel -> FinLevel
quoteFinLevel l lv = case forceFinLevel lv of
  VFL n xs ys ->
    M.foldlWithKey (\i x n -> flmax i (addToFinLevel n (FLMeta (LMetaVar x)))) vars ys
    where
      vars = M.foldlWithKey
        (\i x n -> flmax i (addToFinLevel n (FLVar (lvlToIx l (Lvl x)))))
        (addToFinLevel n FLZ)
        xs

quoteLevel :: Lvl -> VLevel -> Level
quoteLevel l lv = case forceLevel lv of
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
    PEPThird -> case as of
      (a : b : rest) -> foldl app (App (app (app (Prim (Right x)) a) b) t (primElimIcit x)) rest
      _ -> undefined
  where
    app :: Tm -> Either VFinLevel (Val, Icit) -> Tm
    app a (Left lv) = AppLvl a (quoteFinLevel l lv)
    app a (Right (b, i)) = App a (quoteWith ql l b) i

quoteWith :: QuoteLevel -> Lvl -> Val -> Tm
quoteWith ql l = go l
  where
    go l v = case forceMetas v of
      VNe h sp -> foldr (quoteElim ql l) (quoteHead l h) sp
      VGlobal h sp v ->
        case ql of
          Full -> go l v
          KeepGlobals -> foldr (quoteElim ql l) (Global h) sp
      VLam x i b -> Lam x i (go (l + 1) (vinst b (VVar l)))
      VPi x i t u1 b u2 -> Pi x i (go l t) (quoteLevel l u1) (go (l + 1) (vinst b (VVar l))) (quoteLevel l u2)
      VLamLvl x b -> LamLvl x (go (l + 1) (vinstLevel b (vFinLevelVar l)))
      VPiLvl x b u -> let v = vFinLevelVar l in PiLvl x (go (l + 1) (vinstLevel b v)) (quoteLevel (l + 1) (vinstCL u v))
      VPair a b -> Pair (go l a) (go l b)
      VSigma x t u1 b u2 -> Sigma x (go l t) (quoteLevel l u1) (go (l + 1) (vinst b (VVar l))) (quoteLevel l u2)
      VCon t -> Con (go l t)
      VRefl -> Refl
      VNatLit n -> NatLit n
      VLabelLit x -> LabelLit x
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
convElim k (EPrimElim PEIndBool [Left l, Right (p, _), Right (t, _), Right (f, _)]) (EPrimElim PEIfDesc [Left l', Right (i, _), Right (t', _), Right (f', _)]) =
  l == vFLS l' && conv k p (vlam "_" $ \_ -> vDesc l i) && conv k t t' && conv k f f'
convElim k (EPrimElim PEIfDesc [Left l', Right (i, _), Right (t', _), Right (f', _)]) (EPrimElim PEIndBool [Left l, Right (p, _), Right (t, _), Right (f, _)]) =
  vFLS l' == l && conv k (vlam "_" $ \_ -> vDesc l i) p && conv k t' t && conv k f' f
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
  (VCon t, VCon t') -> conv l t t'
  (VLabelLit x, VLabelLit y) -> x == y
  (VNatLit x, VNatLit y) -> x == y

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

  (VRefl, v) -> True
  (v, VRefl) -> True

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
primType PNat = (VType vFLZ, VFinLevel (vFLS mempty))
primType PVoid = (VType vFLZ, VFinLevel (vFLS mempty))
primType PUnitType = (VType vFLZ, VFinLevel (vFLS mempty))
primType PUnit = (VUnitType, VFinLevel mempty)
primType PBool = (VType vFLZ, VFinLevel (vFLS mempty))
primType PTrue = (VBool, VFinLevel mempty)
primType PFalse = (VBool, VFinLevel mempty)
-- <k l> -> Type l -> Type (max l k)
primType PLift =
  (vpilvl "k" (const VOmega) $ \k ->
  vpilvl "l" (\l -> VFinLevel (vFLS (l <> k))) $ \l ->
  vfun (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS (l <> k))) $
  VTypeFin $ l <> k, VOmega)
-- <k l> {A : Type l} -> A -> Lift <k> <l> A
primType PLiftTerm =
  (vpilvl "k" (const VOmega) $ \k ->
  vpilvl "l" (\l -> VFinLevel (vFLS l <> k)) $ \l ->
  vpimpl "A" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (l <> k)) $ \a ->
  vfun a (VFinLevel l) (VFinLevel (l <> k)) $
  VLift k l a, VOmega)
-- <l> {A : Type l} {B : Type l} -> A -> B -> Type l
primType PId =
  (vpilvl "l" (\l -> VFinLevel (vFLS l)) $ \l ->
  vpimpl "A" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \a ->
  vpimpl "B" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \b ->
  vfun a (VFinLevel l) (VFinLevel (vFLS l)) $
  vfun b (VFinLevel l) (VFinLevel (vFLS l)) $
  VTypeFin l, VOmega)
-- Data : <l> {I : Type l} -> Desc <l> I -> I -> Type l
primType PData =
  (vpilvl "l" (\l -> VFinLevel (vFLS l)) $ \l ->
  vpimpl "I" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \i ->
  vfun (vDesc l i) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $
  vfun i (VFinLevel l) (VFinLevel (vFLS l)) $
  VTypeFin l, VOmega)

primType PLabel = (VType vFLZ, VFinLevel (vFLS mempty))

primType PEnum = (VType vFLZ, VFinLevel (vFLS mempty))
primType PENil = (VEnum, VFinLevel mempty)
primType PECons = (vfun VLabel (VFinLevel mempty) (VFinLevel mempty) $ vfun VEnum (VFinLevel mempty) (VFinLevel mempty) VEnum, (VFinLevel mempty))

-- Tag : Enum -> Type
primType PTag = (vfun VEnum (VFinLevel mempty) (VFinLevel (vFLS mempty)) (VType vFLZ), VFinLevel (vFLS mempty))
-- TZ : {l : Label} {e : Enum} -> Tag (ECons l e)
primType PTZ =
  (vpimpl "l" VLabel (VFinLevel mempty) (VFinLevel mempty) $ \l ->
  vpimpl "e" VEnum (VFinLevel mempty) (VFinLevel mempty) $ \e ->
  VTag (VECons l e), VFinLevel mempty)
-- TS : {l : Label} {e : Enum} -> Tag e -> Tag (ECons l e)
primType PTS =
  (vpimpl "l" VLabel (VFinLevel mempty) (VFinLevel mempty) $ \l ->
  vpimpl "e" VEnum (VFinLevel mempty) (VFinLevel mempty) $ \e ->
  vfun (VTag e) (VFinLevel mempty) (VFinLevel mempty) $
  VTag (VECons l e), VFinLevel mempty)

primElimType :: PrimElimName -> (Val, VLevel)
-- <l> {A : Type l} -> Void -> A
primElimType PEAbsurd =
  (vpilvl "l" (\l -> VFinLevel (vFLS l)) $ \l ->
  vpimpl "A" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel l) $ \a ->
  vfun VVoid vFLZ (VFinLevel l) $
  a, VOmega)
-- <k> <l> {A : Type l} -> Lift <k> <l> A -> A
primElimType PELower =
  (vpilvl "k" (const VOmega) $ \k ->
  vpilvl "l" (\l -> VFinLevel (vFLS l <> k)) $ \l ->
  vpimpl "A" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (l <> k)) $ \a ->
  vfun (VLift k l a) (VFinLevel (l <> k)) (VFinLevel l) $
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
{- ifDesc : <l> {I : Type l} -> Desc <l> I -> Desc <l> I -> Bool -> Desc <l> I -}
primElimType PEIfDesc =
  (vpilvl "l" (\l -> VFinLevel (vFLS l)) $ \l ->
  vpimpl "I" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \i ->
  vfun (vDesc l i) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $
  vfun (vDesc l i) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $
  vfun VBool (VFinLevel mempty) (VFinLevel (vFLS l)) $
  vDesc l i, VOmega)
{-
<k l>
{A : Type l}
{x : A}
(P : {y : A} -> Id <l> {A} {A} x y -> Type k)
(refl : P {x} Refl)
{y : A}
(p : Id <l> {A} {A} x y)
P {y} p
-}
primElimType PEElimId =
  (vpilvl "k" (const VOmega) $ \k ->
  vpilvl "l" (\l -> VFinLevel (vFLS (l <> k))) $ \l ->
  vpimpl "A" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (l <> vFLS k)) $ \a ->
  vpimpl "x" a (VFinLevel l) (VFinLevel (l <> vFLS k)) $ \x ->
  vpi "P" (vpimpl "y" a (VFinLevel l) (VFinLevel (l <> vFLS k)) $ \y -> vfun (VId l a a x y) (VFinLevel l) (VFinLevel (vFLS k)) $ VTypeFin k) (VFinLevel (vFLS k)) (VFinLevel (l <> k)) $ \p ->
  vfun (vapp (vapp p x (Impl ImplUnif)) VRefl Expl) (VFinLevel k) (VFinLevel (l <> k)) $
  vpimpl "y" a (VFinLevel l) (VFinLevel (l <> k)) $ \y ->
  vpi "p" (VId l a a x y) (VFinLevel l) (VFinLevel k) $ \pp ->
  vapp (vapp p y (Impl ImplUnif)) pp Expl, VOmega)
-- Ex : <l> {I : Type l} -> (I -> Type l) -> Desc <l> I -> Type l
primElimType PEEx =
  (vpilvl "l" (\l -> VFinLevel (vFLS l)) $ \l ->
  vpimpl "I" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \i ->
  vfun (vfun i (VFinLevel l) (VFinLevel (vFLS l)) (VTypeFin l)) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $
  vfun (vDesc l i) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $
  VTypeFin l, VOmega)
-- El : <l> {I : Type l} -> (I -> Type l) -> I -> Desc <l> I -> Type l
primElimType PEEl =
  (vpilvl "l" (\l -> VFinLevel (vFLS l)) $ \l ->
  vpimpl "I" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \i ->
  vfun (vfun i (VFinLevel l) (VFinLevel (vFLS l)) (VTypeFin l)) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $
  vfun i (VFinLevel l) (VFinLevel (vFLS l)) $
  vfun (vDesc l i) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $
  VTypeFin l, VOmega)
-- mapD : <l> {I : Type l} -> (D : Desc <l> I) -> {A B : I -> Type l} ({i : I} -> A i -> B i) {i : I} -> El <l> {I} D A i -> El <l> {I} D B i
primElimType PEMapD =
  (vpilvl "l" (\l -> VFinLevel (vFLS l)) $ \l ->
  vpimpl "I" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \i ->
  vpi "D" (vDesc l i) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \d ->
  vpimpl "A" (vfun i (VFinLevel l) (VFinLevel (vFLS l)) (VTypeFin l)) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \a ->
  vpimpl "B" (vfun i (VFinLevel l) (VFinLevel (vFLS l)) (VTypeFin l)) (VFinLevel (vFLS l)) (VFinLevel l) $ \b ->
  vfun (vpimpl "i" i (VFinLevel l) (VFinLevel l) $ \ii -> vfun (vapp a ii Expl) (VFinLevel l) (VFinLevel l) (vapp b ii Expl)) (VFinLevel l) (VFinLevel l) $
  vpimpl "i" i (VFinLevel l) (VFinLevel l) $ \ii ->
  vfun (vel l i a ii d) (VFinLevel l) (VFinLevel l) $
  vel l i b ii d, VOmega)
-- mapDEx : <l> {I : Type l} -> (D : Desc <l> I) -> {A B : I -> Type l} ({i : I} -> A i -> B i) -> Ex <l> {I} D A -> Ex <l> {I} D B
primElimType PEMapDEx =
  (vpilvl "l" (\l -> VFinLevel (vFLS l)) $ \l ->
  vpimpl "I" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \i ->
  vpi "D" (vDesc l i) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \d ->
  vpimpl "A" (vfun i (VFinLevel l) (VFinLevel (vFLS l)) (VTypeFin l)) (VFinLevel (vFLS l)) (VFinLevel (vFLS l)) $ \a ->
  vpimpl "B" (vfun i (VFinLevel l) (VFinLevel (vFLS l)) (VTypeFin l)) (VFinLevel (vFLS l)) (VFinLevel l) $ \b ->
  vfun (vpimpl "i" i (VFinLevel l) (VFinLevel l) $ \ii -> vfun (vapp a ii Expl) (VFinLevel l) (VFinLevel l) (vapp b ii Expl)) (VFinLevel l) (VFinLevel l) $
  vfun (vex l i a d) (VFinLevel l) (VFinLevel l) $
  vex l i b d, VOmega)
{- elimData :
<k l>
{I : Type l}
{D : Desc <l> I}
(P : {i : I} -> Data <l> {I} D i -> Type k)
(
  {R : I -> Type l}
  (case : {i : I} -> R i -> Data <l> {I} D i)
  -> ({i : I} -> (x : R i) -> P {i} (case {i} x))
  -> {i : I} (x : El <l> {I} D R i)
  -> P {i} (Con (mapD <l> {I} D {R} {Data <l> {I} D} case {i} x))
)
{i : I}
(x : Data <l> {I} D i)
P {i} x
-}
primElimType PEElimData =
  (vpilvl "k" (\_ -> VOmega) $ \k ->
  vpilvl "l" (\l -> VFinLevel (vFLS l <> vFLS k)) $ \l ->
  vpimpl "I" (VTypeFin l) (VFinLevel (vFLS l)) (VFinLevel (vFLS l <> vFLS k)) $ \i ->
  vpimpl "D" (vDesc l i) (VFinLevel (vFLS l)) (VFinLevel (vFLS l <> vFLS k)) $ \d ->
  vpi "P" (vpimpl "i" i (VFinLevel l) (VFinLevel (l <> vFLS k)) $ \ii -> vfun (VData l i d ii) (VFinLevel l) (VFinLevel (vFLS k)) (VTypeFin k)) (VFinLevel (l <> vFLS k)) (VFinLevel (vFLS l <> k)) $ \p ->
  vfun (alg k l i d p) (VFinLevel (vFLS l <> k)) (VFinLevel (l <> k)) $
  vpimpl "i" i (VFinLevel l) (VFinLevel (l <> k)) $ \ii ->
  vpi "x" (VData l i d ii) (VFinLevel l) (VFinLevel k) $ \x ->
  vapp (vapp p ii (Impl ImplUnif)) x Expl, VOmega)
  where
    alg k l i d p =
      (vpimpl "R" (vfun i (VFinLevel l) (VFinLevel (vFLS l)) (VTypeFin l)) (VFinLevel (vFLS l)) (VFinLevel (l <> k)) $ \r ->
      vpi "case" (vpimpl "i" i (VFinLevel l) (VFinLevel l) $ \ii -> vfun (vapp r ii Expl) (VFinLevel l) (VFinLevel l) $ VData l i d ii) (VFinLevel l) (VFinLevel (l <> k)) $ \cs ->
      vfun (vpimpl "i" i (VFinLevel l) (VFinLevel (l <> k)) $ \ii -> vpi "x" (vapp r ii Expl) (VFinLevel l) (VFinLevel k) $ \x -> vapp (vapp p ii (Impl ImplUnif)) (vapp (vapp cs ii (Impl ImplUnif)) x Expl) Expl) (VFinLevel (l <> k)) (VFinLevel (l <> k)) $
      vpimpl "i" i (VFinLevel l) (VFinLevel (l <> k)) $ \ii ->
      vpi "x" (vel l i r ii d) (VFinLevel l) (VFinLevel k) $ \x ->
      vapp (vapp p ii (Impl ImplUnif)) (VCon (vmapd l i d r (vlam "ii" $ \ii -> VData l i d ii) cs ii x)) Expl)

-- levitation
vVar :: VFinLevel -> Val -> Val -> Val
vVar l i j = let k = vFLS l in VCon $ vpairs [VLiftTerm k mempty VBool VTrue, VLiftTerm k l i j, VRefl]

pattern VDVar j <- VCon (VPair (VLiftTerm _ _ _ VTrue) (VPair (VLiftTerm _ _ _ j) _))

-- \<l> {I} A K. Con (lift <S l> <0> {Bool} False, lift <S l> <0> {Bool} True, A, \x. K (lower <S l> <l> {A} x), Refl)
vArg :: VFinLevel -> Val -> Val -> Val -> Val
vArg l i a kk = let k = vFLS l in VCon $ vpairs [VLiftTerm k mempty VBool VFalse, VLiftTerm k mempty VBool VTrue, a, vlam "x" (\x -> vapp kk (vlower k l a x) Expl), VRefl]

pattern VArg a k <- VCon (VPair (VLiftTerm _ _ _ VFalse) (VPair (VLiftTerm _ _ _ VTrue) (VPair a (VPair k _))))

-- \<l> {I} A B. Con (lift <S l> <0> {Bool} False, lift <S l> <0> {Bool} False, A, B, Refl)
vInd :: VFinLevel -> Val -> Val -> Val -> Val
vInd l i a b = let k = vFLS l in VCon $ vpairs [VLiftTerm k mempty VBool VFalse, VLiftTerm k mempty VBool VFalse, a, b, VRefl]

pattern VInd a b <- VCon (VPair (VLiftTerm _ _ _ VFalse) (VPair (VLiftTerm _ _ _ VFalse) (VPair a (VPair b _))))

-- \<l> {I} A B. Arg <l> {I} (Lift <l> <0> Bool) (\b. indBool <S l> (\_. Desc <l> I) A B (lower <l> <0> {Bool} b))
vSumD :: VFinLevel -> Val -> Val -> Val -> Val
vSumD l i a b = vArg l i (VLift l mempty VBool) (vlam "b" $ \bb -> vifdesc l i a b (vlower l mempty VBool bb))

{-
DescD : <l> -> Type l -> Desc (Lift <S l> ())
  = \<l> I. 
    let var = Var (lift []);
    SumD (Arg (Lift <S l> I) \_. var)
    (SumD
      (Arg (Type l) (\A. Ind (Arg (Lift <S l> A) \_. var) var))
      (Ind var (Ind var var)));
-}
vDescD :: VFinLevel -> Val -> Val
vDescD l i =
  let k = vFLS l in
  let tu = VLift k mempty VUnitType in
  let u = VLiftTerm k mempty VUnitType VUnit in
  let var = vVar k tu u in
  {- Var -} vSumD k tu (vArg k tu (VLift k l i) (vlam "_" $ \_ -> var)) $
  {- Arg -} vSumD k tu (vArg k tu (VTypeFin l) (vlam "A" $ \a -> vInd k tu (vArg k tu (VLift k l a) (vlam "_" $ \_ -> var)) var)) $
  {- Ind -} (vInd k tu var (vInd k tu var var))

-- <l> -> Type l -> Type (S l) = \I. Data (DescD I) [];
vDesc :: VFinLevel -> Val -> Val
vDesc l i = let k = vFLS l in VData k (VLift k mempty VUnitType) (vDescD l i) (VLiftTerm k mempty VUnitType VUnit)
