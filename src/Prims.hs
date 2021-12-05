module Prims where

import Common
data PrimName
  = PVoid
  | PUnitType | PUnit
  | PBool | PTrue | PFalse
  | PHEq | PHRefl

  | PLift
  | PLiftTerm
  deriving (Eq)

data PrimElimName
  = PEAbsurd
  | PELower
  | PEIndBool
  | PEElimHEq
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
  show PLift = "Lift"
  show PLiftTerm = "lift"

instance Show PrimElimName where
  show PEAbsurd = "absurd"
  show PELower = "lower"
  show PEIndBool = "indBool"
  show PEElimHEq = "elimHEq"

toPrimName :: String -> Maybe PrimName
toPrimName "Void" = Just PVoid
toPrimName "()" = Just PUnitType
toPrimName "[]" = Just PUnit
toPrimName "Bool" = Just PBool
toPrimName "True" = Just PTrue
toPrimName "False" = Just PFalse
toPrimName "HEq" = Just PHEq
toPrimName "HRefl" = Just PHRefl
toPrimName "Lift" = Just PLift
toPrimName "lift" = Just PLiftTerm
toPrimName _ = Nothing

toPrimElimName :: String -> Maybe PrimElimName
toPrimElimName "absurd" = Just PEAbsurd
toPrimElimName "lower" = Just PELower
toPrimElimName "indBool" = Just PEIndBool
toPrimElimName "elimHEq" = Just PEElimHEq
toPrimElimName _ = Nothing

data PrimElimPosition = PEPFirst | PEPLast

primElimPosition :: PrimElimName -> PrimElimPosition
primElimPosition _ = PEPLast

primElimIcit :: PrimElimName -> Icit
primElimIcit _ = Expl
