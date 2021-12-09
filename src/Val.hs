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

data ClosLvl
  = ClosLvl Env Level
  | FunLvl (VFinLevel -> VLevel)

data Head = HVar Lvl | HPrim PrimName | HMeta MetaVar
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
  | VPi Name Icit Val VLevel (Clos Val) VLevel
  | VLamLvl Name (Clos VFinLevel)
  | VPiLvl Name (Clos VFinLevel) ClosLvl
  | VPair Val Val
  | VSigma Name Val VLevel (Clos Val) VLevel
  | VType VLevel

pattern VTypeFin l = VType (VFinLevel l)
pattern VVar l = VNe (HVar l) []
pattern VMeta m = VNe (HMeta m) []

pattern VVoid = VNe (HPrim PVoid) []
pattern VUnitType = VNe (HPrim PUnitType) []
pattern VUnit = VNe (HPrim PUnit) []
pattern VBool = VNe (HPrim PBool) []
pattern VTrue = VNe (HPrim PTrue) []
pattern VFalse = VNe (HPrim PFalse) []
pattern VLift l k x = VNe (HPrim PLift) [EApp x Expl, EAppLvl k, EAppLvl l]
pattern VLiftTerm l k a x = VNe (HPrim PLiftTerm) [EApp x Expl, EApp a Impl, EAppLvl k, EAppLvl l]
pattern VHEq l a b x y = VNe (HPrim PHEq) [EApp y Expl, EApp x Expl, EApp b Impl, EApp a Impl, EAppLvl l]
pattern VHRefl l a x = VNe (HPrim PHRefl) [EApp x Impl, EApp a Impl, EAppLvl l]

vpi :: Name -> Val -> VLevel -> VLevel -> (Val -> Val) -> Val
vpi x a u1 u2 b = VPi x Expl a u1 (Fun b) u2

vpimpl :: Name -> Val -> VLevel -> VLevel -> (Val -> Val) -> Val
vpimpl x a u1 u2 b = VPi x Impl a u1 (Fun b) u2

vpilvl :: Name -> (VFinLevel -> VLevel) -> (VFinLevel -> Val) -> Val
vpilvl x u b = VPiLvl x (Fun b) (FunLvl u)

vsigma :: Name -> Val -> VLevel -> VLevel -> (Val -> Val) -> Val
vsigma x a u1 u2 b = VSigma x a u1 (Fun b) u2

vfun :: Val -> VLevel -> VLevel -> Val -> Val
vfun a u1 u2 b = VPi "_" Expl a u1 (Fun $ const b) u2

vpairty :: Val -> VLevel -> VLevel -> Val -> Val
vpairty a u1 u2 b = VSigma "_" a u1 (Fun $ const b) u2

vlam :: Name -> (Val -> Val) -> Val
vlam x b = VLam x Expl (Fun b)

vlamimpl :: Name -> (Val -> Val) -> Val
vlamimpl x b = VLam x Impl (Fun b)

vlamlvl :: Name -> (VFinLevel -> Val) -> Val
vlamlvl x b = VLamLvl x (Fun b)
