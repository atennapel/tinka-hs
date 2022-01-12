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

instance Show (Clos v) where
  show (Clos _ tm) = "(Clos " ++ show tm ++ ")"
  show _ = "Fun"

data ClosLvl
  = ClosLvl Env Level
  | FunLvl (VFinLevel -> VLevel)

instance Show ClosLvl where
  show (ClosLvl _ tm) = "(ClosLvl " ++ show tm ++ ")"
  show _ = "FunLvl"

data Head = HVar Lvl | HPrim PrimName | HMeta MetaVar
  deriving (Eq, Show)

data Elim
  = EApp Val Icit
  | EAppLvl VFinLevel
  | EProj ProjType
  | EPrimElim PrimElimName [Either VFinLevel (Val, Icit)]
  deriving (Show)

data Val
  = VNe Head Sp
  | VGlobal Name Sp Val
  | VLam Name Icit (Clos Val)
  | VPi Name Icit Val VLevel (Clos Val) VLevel
  | VLamLvl Name (Clos VFinLevel)
  | VPiLvl Name (Clos VFinLevel) ClosLvl
  | VPair Val Val
  | VSigma Name Val VLevel (Clos Val) VLevel
  | VCon Val
  | VRefl
  | VLabelLit Name
  | VType VLevel
  deriving (Show)

pattern VTypeFin l = VType (VFinLevel l)
pattern VVar l = VNe (HVar l) []
pattern VMeta m = VNe (HMeta m) []
pattern VPrim x = VNe (HPrim x) []

pattern VVoid = VNe (HPrim PVoid) []
pattern VUnitType = VNe (HPrim PUnitType) []
pattern VUnit = VNe (HPrim PUnit) []
pattern VBool = VNe (HPrim PBool) []
pattern VTrue = VNe (HPrim PTrue) []
pattern VFalse = VNe (HPrim PFalse) []
pattern VLift k l x = VNe (HPrim PLift) [EApp x Expl, EAppLvl l, EAppLvl k]
pattern VLiftTerm k l a x = VNe (HPrim PLiftTerm) [EApp x Expl, EApp a (Impl ImplUnif), EAppLvl l, EAppLvl k]
pattern VId l a b x y = VNe (HPrim PId) [EApp y Expl, EApp x Expl, EApp b (Impl ImplUnif), EApp a (Impl ImplUnif), EAppLvl l]

pattern VData l i d j = VNe (HPrim PData) [EApp j Expl, EApp d Expl, EApp i (Impl ImplUnif), EAppLvl l]

pattern VLabel = VNe (HPrim PLabel) []
pattern VEnum = VNe (HPrim PEnum) []
pattern VENil = VNe (HPrim PENil) []
pattern VECons hd tl = VNe (HPrim PECons) [EApp tl Expl, EApp hd Expl]
pattern VTag e = VNe (HPrim PTag) [EApp e Expl]
pattern VTZ l e = VNe (HPrim PTZ) [EApp e (Impl ImplUnif), EApp l (Impl ImplUnif)]
pattern VTS l e t = VNe (HPrim PTS) [EApp t Expl, EApp e (Impl ImplUnif), EApp l (Impl ImplUnif)]

vpi :: Name -> Val -> VLevel -> VLevel -> (Val -> Val) -> Val
vpi x a u1 u2 b = VPi x Expl a u1 (Fun b) u2

vpimpl :: Name -> Val -> VLevel -> VLevel -> (Val -> Val) -> Val
vpimpl x a u1 u2 b = VPi x (Impl ImplUnif) a u1 (Fun b) u2

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
vlamimpl x b = VLam x (Impl ImplUnif) (Fun b)

vlamlvl :: Name -> (VFinLevel -> Val) -> Val
vlamlvl x b = VLamLvl x (Fun b)

vpairs :: [Val] -> Val
vpairs = foldr1 VPair
