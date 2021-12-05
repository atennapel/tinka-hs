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
  | EPrimElim PrimElimName [(Val, Icit)]

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

pattern VVar l = VNe (HVar l) []
