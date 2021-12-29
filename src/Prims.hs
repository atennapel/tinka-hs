module Prims where

import Common

data PrimName
  = PVoid
  | PUnitType | PUnit
  | PBool | PTrue | PFalse
  | PId

  | PLift
  | PLiftTerm

  | PData
  deriving (Eq, Ord)

data PrimElimName
  = PEAbsurd
  | PELower
  | PEIndBool | PEIfDesc
  | PEElimId
  | PEEx | PEEl | PEMapD | PEMapDEx
  | PEElimData
  deriving (Eq)

instance Show PrimName where
  show PVoid = "Void"
  show PUnitType = "()"
  show PUnit = "[]"
  show PBool = "Bool"
  show PTrue = "True"
  show PFalse = "False"
  show PId = "Id"
  show PLift = "Lift"
  show PLiftTerm = "lift"
  show PData = "Data"

instance Show PrimElimName where
  show PEAbsurd = "absurd"
  show PELower = "lower"
  show PEIndBool = "indBool"
  show PEIfDesc = "ifDesc"
  show PEElimId = "elimId"
  show PEEx = "Ex"
  show PEEl = "El"
  show PEMapD = "mapD"
  show PEMapDEx = "mapDEx"
  show PEElimData = "elimData"

toPrimName :: String -> Maybe PrimName
toPrimName "Void" = Just PVoid
toPrimName "()" = Just PUnitType
toPrimName "[]" = Just PUnit
toPrimName "Bool" = Just PBool
toPrimName "True" = Just PTrue
toPrimName "False" = Just PFalse
toPrimName "Id" = Just PId
toPrimName "Lift" = Just PLift
toPrimName "lift" = Just PLiftTerm
toPrimName "Data" = Just PData
toPrimName _ = Nothing

toPrimElimName :: String -> Maybe PrimElimName
toPrimElimName "absurd" = Just PEAbsurd
toPrimElimName "lower" = Just PELower
toPrimElimName "indBool" = Just PEIndBool
toPrimElimName "ifDesc" = Just PEIfDesc
toPrimElimName "elimId" = Just PEElimId
toPrimElimName "Ex" = Just PEEx
toPrimElimName "El" = Just PEEl
toPrimElimName "mapD" = Just PEMapD
toPrimElimName "mapDEx" = Just PEMapDEx
toPrimElimName "elimData" = Just PEElimData
toPrimElimName _ = Nothing

data PrimElimPosition = PEPFirst | PEPLast | PEPThird

primElimPosition :: PrimElimName -> PrimElimPosition
primElimPosition PEMapD = PEPThird
primElimPosition PEMapDEx = PEPThird
primElimPosition _ = PEPLast

primElimIcit :: PrimElimName -> Icit
primElimIcit _ = Expl
