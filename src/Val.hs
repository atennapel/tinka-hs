module Val where

import Common
import Core
import Levels

type VTy = Val

type Sp = [Elim]
type Env = [Either VFinLevel Val]

data Clos v
  = Clos Env Tm
  | Fun (v -> Val)

data Head = HVar Lvl
  deriving (Eq)

data Elim
  = EApp Val
  | EAppLvl VFinLevel

data Val
  = VNe Head Sp
  | VLam Name (Clos Val)
  | VPi Name Val (Clos Val)
  | VLamLvl Name (Clos VFinLevel)
  | VPiLvl Name (Clos VFinLevel)
  | VType VLevel

pattern VVar l = VNe (HVar l) []
