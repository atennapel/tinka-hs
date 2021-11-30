module Val where

import Common
import Core

type Spine = [Elim]
type Env = [Val]

data Clos
  = Clos Env Core
  | Fun (Val -> Val)

data ClosLevel
  = ClosLevel Env Level
  | FunLevel (Val -> VLevel)

data Head = HVar Lvl | HPrim PrimName | HMeta MetaVar
  deriving (Eq)

data Elim
  = EApp Val Icit
  | EProj ProjType
  | EPrimElim PrimElimName [(Val, Icit)]
  | ELower

data VLevel = VFin Val | VOmega

data Val
  = VNe Head Spine
  | VGlobal Name Spine Val
  | VAbs Name Icit Clos
  | VPi Name Icit Val VLevel Clos ClosLevel
  | VSigma Name Val VLevel Clos ClosLevel
  | VPair Val Val
  | VU VLevel
  | VULevel
  | VL0
  | VLS Val
  | VLMax Val Val
  | VLift Val
  | VLiftTerm Val
  | VRefl

pattern VVar x = VNe (HVar x) []
pattern VMeta x = VNe (HMeta x) []
pattern VType v = VU (VFin v)

vpi :: Name -> Val -> VLevel -> (Val -> VLevel) -> (Val -> Val) -> Val
vpi x a u1 u2 b = VPi x Expl a u1 (Fun b) (FunLevel u2)

vpimpl :: Name -> Val -> VLevel -> (Val -> VLevel) -> (Val -> Val) -> Val
vpimpl x a u1 u2 b = VPi x Impl a u1 (Fun b) (FunLevel u2)

vsigma :: Name -> Val -> VLevel -> (Val -> VLevel) -> (Val -> Val) -> Val
vsigma x a u1 u2 b = VSigma x a u1 (Fun b) (FunLevel u2)

vfun :: Val -> VLevel -> (Val -> VLevel) -> Val -> Val
vfun a u1 u2 b = VPi "_" Expl a u1 (Fun $ const b) (FunLevel u2)

vpairty :: Val -> VLevel -> (Val -> VLevel) -> Val -> Val
vpairty a u1 u2 b = VSigma "_" a u1 (Fun $ const b) (FunLevel u2)

vabs :: Name -> (Val -> Val) -> Val
vabs x b = VAbs x Expl (Fun b)

vabsimpl :: Name -> (Val -> Val) -> Val
vabsimpl x b = VAbs x Impl (Fun b)

vvar :: Lvl -> Val
vvar k = VNe (HVar k) []

vprim :: PrimName -> Val
vprim x = VNe (HPrim x) []

vvoid, vunittype, vunit, vbool, vtrue, vfalse :: Val
vvoid = vprim PVoid
vunittype = vprim PUnitType
vunit = vprim PUnit
vbool = vprim PBool
vtrue = vprim PTrue
vfalse = vprim PFalse

vheq :: Val -> Val -> Val -> Val -> Val
vheq a b x y = VNe (HPrim PHEq) [EApp y Expl, EApp x Expl, EApp b Expl, EApp a Expl]
