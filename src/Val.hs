module Val where

import Common
import Core
import Levels
import Prims

type VTy = Val

type Sp = [Elim]
type Env = [Either VFinLevel Val]

data Clos v
  = Clos Env Tm
  | Fun (v -> Val)

data Head = HVar Lvl | HPrim PrimName
  deriving (Eq)

data Elim
  = EApp Val Icit
  | EAppLvl VFinLevel
  | EProj ProjType
  | EPrimElim PrimElimName [Either VFinLevel (Val, Icit)]

data Val
  = VNe Head Sp
  | VGlobal Name Sp Val
  | VLam Name Icit (Clos Val)
  | VPi Name Icit Val (Clos Val)
  | VLamLvl Name (Clos VFinLevel)
  | VPiLvl Name (Clos VFinLevel)
  | VPair Val Val
  | VSigma Name Val (Clos Val)
  | VType VLevel

pattern VTypeFin l = VType (VFinLevel l)
pattern VVar l = VNe (HVar l) []
pattern VVoid = VNe (HPrim PVoid) []
pattern VUnitType = VNe (HPrim PUnitType) []
pattern VUnit = VNe (HPrim PUnit) []
pattern VBool = VNe (HPrim PBool) []
pattern VTrue = VNe (HPrim PTrue) []
pattern VFalse = VNe (HPrim PFalse) []
pattern VLift l x = VNe (HPrim PLift) [EApp x Expl, EAppLvl l]
pattern VLiftTerm l a x = VNe (HPrim PLiftTerm) [EApp x Expl, EApp a Impl, EAppLvl l]
pattern VHEq l a b x y = VNe (HPrim PHEq) [EApp y Expl, EApp x Expl, EApp b Impl, EApp a Impl, EAppLvl l]
pattern VHRefl l a x = VNe (HPrim PHRefl) [EApp x Impl, EApp a Impl, EAppLvl l]

vpi :: Name -> Val -> (Val -> Val) -> Val
vpi x a b = VPi x Expl a (Fun b)

vpimpl :: Name -> Val -> (Val -> Val) -> Val
vpimpl x a b = VPi x Impl a (Fun b)

vpilvl :: Name -> (VFinLevel -> Val) -> Val
vpilvl x b = VPiLvl x (Fun b)

vsigma :: Name -> Val -> (Val -> Val) -> Val
vsigma x a b = VSigma x a (Fun b)

vfun :: Val -> Val -> Val
vfun a b = VPi "_" Expl a (Fun $ const b)

vpairty :: Val -> Val -> Val
vpairty a b = VSigma "_" a (Fun $ const b)

vlam :: Name -> (Val -> Val) -> Val
vlam x b = VLam x Expl (Fun b)

vlamimpl :: Name -> (Val -> Val) -> Val
vlamimpl x b = VLam x Impl (Fun b)

vlamlvl :: Name -> (VFinLevel -> Val) -> Val
vlamlvl x b = VLamLvl x (Fun b)
