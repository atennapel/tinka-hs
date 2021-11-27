module Val where

import Common
import Core
import Universes

type Spine = [Elim]
type Env = [Val]

data Clos
  = Clos Env Core
  | Fun (Val -> Val)

data Head = HVar Lvl | HPrim PrimName ULvl | HMeta MetaVar
  deriving (Eq)

data Elim
  = EApp Val Icit
  | EProj ProjType
  | EPrimElim PrimElimName ULvl ULvl [Val]
  | ELower

data Val
  = VNe Head Spine
  | VGlobal Name ULvl Spine Val
  | VAbs Name Icit Clos
  | VPi Name Icit Val Univ Clos Univ
  | VSigma Name Val Univ Clos Univ
  | VPair Val Val
  | VU Univ
  | VLift Val
  | VLiftTerm Val
  | VCon Val
  | VRefl

pattern VVar x = VNe (HVar x) []
pattern VMeta x = VNe (HMeta x) []
pattern VType l = VU (UConst l)

vpi :: Name -> Val -> Univ -> Univ -> (Val -> Val) -> Val
vpi x a u1 u2 b = VPi x Expl a u1 (Fun b) u2

vsigma :: Name -> Val -> Univ -> Univ -> (Val -> Val) -> Val
vsigma x a u1 u2 b = VSigma x a u1 (Fun b) u2

vfun :: Val -> Univ -> Univ -> Val -> Val
vfun a u1 u2 b = VPi "_" Expl a u1 (Fun $ const b) u2

vpairty :: Val -> Univ -> Univ -> Val -> Val
vpairty a u1 u2 b = VSigma "_" a u1 (Fun $ const b) u2

vabs :: Name -> (Val -> Val) -> Val
vabs x b = VAbs x Expl (Fun b)

vvar :: Lvl -> Val
vvar k = VNe (HVar k) []

vprim :: PrimName -> ULvl -> Val
vprim x l = VNe (HPrim x l) []

vvoid, vunittype, vunit, vbool, vtrue, vfalse :: ULvl -> Val
vvoid = vprim PVoid
vunittype = vprim PUnitType
vunit = vprim PUnit
vbool = vprim PBool
vtrue = vprim PTrue
vfalse = vprim PFalse

vheq :: ULvl -> Val -> Val -> Val -> Val -> Val
vheq l a b x y = VNe (HPrim PHEq l) [EApp y Expl, EApp x Expl, EApp b Expl, EApp a Expl]

vdata :: ULvl -> Val -> Val
vdata l v = VNe (HPrim PData l) [EApp v Expl]
