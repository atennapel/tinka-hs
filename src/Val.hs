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
  | VType VLevel
  deriving (Show)

pattern VTypeFin l = VType (VFinLevel l)
pattern VVar l = VNe (HVar l) []
pattern VMeta m = VNe (HMeta m) []
pattern VPrim x = VNe (HPrim x) []

pattern VUnitType = VNe (HPrim PUnitType) []
pattern VUnit = VNe (HPrim PUnit) []
pattern VLift k l x = VNe (HPrim PLift) [EApp x Expl, EAppLvl l, EAppLvl k]
pattern VLiftTerm k l a x = VNe (HPrim PLiftTerm) [EApp x Expl, EApp a (Impl ImplUnif), EAppLvl l, EAppLvl k]

pattern VTyPrim l i = VNe (HPrim PTy) [EApp i Expl, EAppLvl l]
pattern VEnd l i ii = VNe (HPrim PEnd) [EApp ii Expl, EApp i (Impl ImplUnif), EAppLvl l]
pattern VArg l i a b = VNe (HPrim PArg) [EApp b Expl, EApp a Expl, EApp i (Impl ImplUnif), EAppLvl l]
pattern VInd l i ii b = VNe (HPrim PInd) [EApp b Expl, EApp ii Expl, EApp i (Impl ImplUnif), EAppLvl l]
pattern VHInd l i a ii b = VNe (HPrim PHInd) [EApp b Expl, EApp ii Expl, EApp a Expl, EApp i (Impl ImplUnif), EAppLvl l]

pattern VCtx l i = VNe (HPrim PCtx) [EApp i Expl, EAppLvl l]
pattern VEmpty l i = VNe (HPrim PEmpty) [EApp i (Impl ImplUnif), EAppLvl l]
pattern VExt l i ty ctx = VNe (HPrim PExt) [EApp ctx Expl, EApp ty Expl, EApp i (Impl ImplUnif), EAppLvl l]

pattern VVarPrim l i ctx ty = VNe (HPrim PVar) [EApp ty Expl, EApp ctx Expl, EApp i (Impl ImplUnif), EAppLvl l]
pattern VVZ l i ctx a = VNe (HPrim PVZ) [EApp a (Impl ImplUnif), EApp ctx (Impl ImplUnif), EApp i (Impl ImplUnif), EAppLvl l]
pattern VVS l i ctx a b v = VNe (HPrim PVS) [EApp v Expl, EApp b (Impl ImplUnif), EApp a (Impl ImplUnif), EApp ctx (Impl ImplUnif), EApp i (Impl ImplUnif), EAppLvl l]

pattern VTm l i ctx ty = VNe (HPrim PTm) [EApp ty Expl, EApp ctx Expl, EApp i (Impl ImplUnif), EAppLvl l]
pattern VEl l i ctx a v = VNe (HPrim PEl) [EApp v Expl, EApp a (Impl ImplUnif), EApp ctx (Impl ImplUnif), EApp i (Impl ImplUnif), EAppLvl l]
pattern VApp l i ctx a b tm arg = VNe (HPrim PApp) [EApp arg Expl, EApp tm Expl, EApp b (Impl ImplUnif), EApp a (Impl ImplUnif), EApp ctx (Impl ImplUnif), EApp i (Impl ImplUnif), EAppLvl l]
pattern VAppInd l i ctx ii b tm arg = VNe (HPrim PAppInd) [EApp arg Expl, EApp tm Expl, EApp b (Impl ImplUnif), EApp ii (Impl ImplUnif), EApp ctx (Impl ImplUnif), EApp i (Impl ImplUnif), EAppLvl l]
pattern VAppHInd l i ctx a ii b tm f = VNe (HPrim PAppInd) [EApp f Expl, EApp tm Expl, EApp b (Impl ImplUnif), EApp ii (Impl ImplUnif), EApp a (Impl ImplUnif), EApp ctx (Impl ImplUnif), EApp i (Impl ImplUnif), EAppLvl l]

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
