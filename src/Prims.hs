module Prims where

import Common
data PrimName
  = PVoid
  | PUnitType | PUnit
  | PBool | PTrue | PFalse
  | PHEq
  deriving (Eq)

data PrimElimName
  = PEVoid
  deriving (Eq)

instance Show PrimName where
  show PVoid = "Void"
  show PUnitType = "()"
  show PUnit = "[]"
  show PBool = "Bool"
  show PTrue = "True"
  show PFalse = "False"
  show PHEq = "HEq"

instance Show PrimElimName where
  show PEVoid = "Void"

toPrimName :: String -> Maybe PrimName
toPrimName "Void" = Just PVoid
toPrimName "()" = Just PUnitType
toPrimName "[]" = Just PUnit
toPrimName "Bool" = Just PBool
toPrimName "True" = Just PTrue
toPrimName "False" = Just PFalse
toPrimName "HEq" = Just PHEq
toPrimName _ = Nothing

toPrimElimName :: String -> Maybe PrimElimName
toPrimElimName "Void" = Just PEVoid
toPrimElimName _ = Nothing

data PrimElimPosition = PEPFirst | PEPLast

primElimPosition :: PrimElimName -> PrimElimPosition
primElimPosition _ = PEPLast

primElimIcit :: PrimElimName -> Icit
primElimIcit _ = Expl
