module Val where

import Common
import Core
import Levels

type Spine = [Elim]
type Env = [Val]

data Clos v
  = Clos (Env, EnvLevel) Core
  | Fun (v -> Val)

data Head = HVar Lvl | HPrim PrimName | HMeta MetaVar
  deriving (Eq)

data Elim
  = EApp Val Icit
  | EAppLevel VLevel
  | EProj ProjType
  | EPrimElim PrimElimName [(Val, Icit)]

data Val
  = VNe Head Spine
  | VGlobal Name Spine Val
  | VAbs Name Icit (Clos Val)
  | VPi Name Icit Val VLevel (Clos Val) VLevel
  | VSigma Name Val VLevel (Clos Val) VLevel
  | VPair Val Val
  | VU VLevel
  | VAbsLevel Name (Clos VLevel)
  | VPiLevel Name (Clos VLevel)

pattern VVar x = VNe (HVar x) []
pattern VMeta x = VNe (HMeta x) []

pattern VVoid = VNe (HPrim PVoid) []
pattern VUnitType = VNe (HPrim PUnitType) []
pattern VUnit = VNe (HPrim PUnit) []
pattern VBool = VNe (HPrim PBool) []
pattern VTrue = VNe (HPrim PTrue) []
pattern VFalse = VNe (HPrim PFalse) []
pattern VLift l x = VNe (HPrim PLift) [EApp x Expl, EApp l Impl]
pattern VLiftTerm l a x = VNe (HPrim PLiftTerm) [EApp x Expl, EApp a Impl, EApp l Impl]
pattern VHEq l a b x y = VNe (HPrim PHEq) [EApp y Expl, EApp x Expl, EApp b Impl, EApp a Impl, EApp l Impl]
pattern VHRefl l a x = VNe (HPrim PHRefl) [EApp x Impl, EApp a Impl, EApp l Impl]

vpi :: Name -> Val -> VLevel -> VLevel -> (Val -> Val) -> Val
vpi x a u1 u2 b = VPi x Expl a u1 (Fun b) u2

vpimpl :: Name -> Val -> VLevel -> VLevel -> (Val -> Val) -> Val
vpimpl x a u1 u2 b = VPi x Impl a u1 (Fun b) u2

vsigma :: Name -> Val -> VLevel -> VLevel -> (Val -> Val) -> Val
vsigma x a u1 u2 b = VSigma x a u1 (Fun b) u2

vfun :: Val -> VLevel -> VLevel -> Val -> Val
vfun a u1 u2 b = VPi "_" Expl a u1 (Fun $ const b) u2

vpairty :: Val -> VLevel -> VLevel -> Val -> Val
vpairty a u1 u2 b = VSigma "_" a u1 (Fun $ const b) u2

vabs :: Name -> (Val -> Val) -> Val
vabs x b = VAbs x Expl (Fun b)

vabsimpl :: Name -> (Val -> Val) -> Val
vabsimpl x b = VAbs x Impl (Fun b)

vvar :: Lvl -> Val
vvar k = VNe (HVar k) []
