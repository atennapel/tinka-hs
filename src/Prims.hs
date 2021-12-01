module Prims where

import Common
data PrimName
  = PVoid
  | PUnitType | PUnit
  | PBool | PTrue | PFalse
  | PHEq | PHRefl

  | PLevel
  | PL0
  | PLS

  | PLift
  | PLiftTerm
  deriving (Eq)

data PrimElimName
  = PEAbsurd
  | PELower
  | PELMax
  deriving (Eq)

instance Show PrimName where
  show PVoid = "Void"
  show PUnitType = "()"
  show PUnit = "[]"
  show PBool = "Bool"
  show PTrue = "True"
  show PFalse = "False"
  show PHEq = "HEq"
  show PHRefl = "HRefl"
  show PLevel = "Level"
  show PL0 = "L0"
  show PLS = "LS"
  show PLift = "Lift"
  show PLiftTerm = "lift"

instance Show PrimElimName where
  show PEAbsurd = "absurd"
  show PELower = "lower"
  show PELMax = "lmax"

toPrimName :: String -> Maybe PrimName
toPrimName "Void" = Just PVoid
toPrimName "()" = Just PUnitType
toPrimName "[]" = Just PUnit
toPrimName "Bool" = Just PBool
toPrimName "True" = Just PTrue
toPrimName "False" = Just PFalse
toPrimName "HEq" = Just PHEq
toPrimName "HRefl" = Just PHRefl
toPrimName "Level" = Just PLevel
toPrimName "L0" = Just PL0
toPrimName "LS" = Just PLS
toPrimName "Lift" = Just PLift
toPrimName "lift" = Just PLiftTerm
toPrimName _ = Nothing

toPrimElimName :: String -> Maybe PrimElimName
toPrimElimName "absurd" = Just PEAbsurd
toPrimElimName "lower" = Just PELower
toPrimElimName "lmax" = Just PELMax
toPrimElimName _ = Nothing

data PrimElimPosition = PEPFirst | PEPLast

primElimPosition :: PrimElimName -> PrimElimPosition
primElimPosition PELMax = PEPFirst
primElimPosition _ = PEPLast

primElimIcit :: PrimElimName -> Icit
primElimIcit _ = Expl
