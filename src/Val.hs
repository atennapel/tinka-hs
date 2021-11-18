module Val where

import Common
import Core

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
  | VAbs Name Clos
  | VPi Name Val Clos
  | VSigma Name Val Clos
  | VPair Val Val
  | VU ULvl
  | VLift Val
  | VLiftTerm Val
  | VCon Val

vpi :: Name -> Val -> (Val -> Val) -> Val
vpi x a b = VPi x a (Fun b)

vsigma :: Name -> Val -> (Val -> Val) -> Val
vsigma x a b = VSigma x a (Fun b)

vfun :: Val -> Val -> Val
vfun a b = VPi "_" a (Fun $ const b)

vpairty :: Val -> Val -> Val
vpairty a b = VSigma "_" a (Fun $ const b)

vabs :: Name -> (Val -> Val) -> Val
vabs x b = VAbs x (Fun b)

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
vheq l a b x y = VNe (HPrim PHEq l) [EApp y, EApp x, EApp b, EApp a]

vhrefl :: ULvl -> Val -> Val -> Val
vhrefl l a x = VNe (HPrim PHRefl l) [EApp x, EApp a]

vdata :: ULvl -> Val -> Val
vdata l v = VNe (HPrim PData l) [EApp v]
