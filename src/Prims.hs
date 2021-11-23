module Prims where

data PrimName
  = PVoid
  | PUnitType | PUnit
  | PBool | PTrue | PFalse
  | PHEq
  | PData
  deriving (Eq)

data PrimElimName
  = PEVoid
  | PEBool
  | PEBoolDesc
  | PEHEq
  | PEEl
  | PEAll
  | PEall
  | PEData
  deriving (Eq)

instance Show PrimName where
  show PVoid = "Void"
  show PUnitType = "UnitType"
  show PUnit = "Unit"
  show PBool = "Bool"
  show PTrue = "True"
  show PFalse = "False"
  show PHEq = "HEq"
  show PData = "Data"

instance Show PrimElimName where
  show PEVoid = "Void"
  show PEBool = "Bool"
  show PEBoolDesc = "BoolDesc"
  show PEHEq = "HEq"
  show PEEl = "El"
  show PEAll = "All"
  show PEall = "all"
  show PEData = "Data"

toPrimName :: String -> Maybe PrimName
toPrimName "Void" = Just PVoid
toPrimName "UnitType" = Just PUnitType
toPrimName "Unit" = Just PUnit
toPrimName "Bool" = Just PBool
toPrimName "True" = Just PTrue
toPrimName "False" = Just PFalse
toPrimName "HEq" = Just PHEq
toPrimName "Data" = Just PData
toPrimName _ = Nothing

toPrimElimName :: String -> Maybe PrimElimName
toPrimElimName "Void" = Just PEVoid
toPrimElimName "Bool" = Just PEBool
toPrimElimName "BoolDesc" = Just PEBoolDesc
toPrimElimName "HEq" = Just PEHEq
toPrimElimName "El" = Just PEEl
toPrimElimName "All" = Just PEAll
toPrimElimName "all" = Just PEall
toPrimElimName "Data" = Just PEData
toPrimElimName _ = Nothing

data PrimElimPosition = PEPFirst | PEPLast

primElimPosition :: PrimElimName -> PrimElimPosition
primElimPosition PEAll = PEPFirst
primElimPosition PEall = PEPFirst
primElimPosition _ = PEPLast
