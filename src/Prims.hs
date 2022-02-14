module Prims where

import Common

data PrimName
  = PUnitType | PUnit
  | PId

  | PLift
  | PLiftTerm

  | PLabel
  | PEnum | PENil | PECons
  | PTag | PTZ | PTS
  deriving (Eq, Ord)

data PrimElimName
  = PELower
  | PEElimId
  | PEElimEnum
  | PEElimTag
  deriving (Eq)

instance Show PrimName where
  show PUnitType = "()"
  show PUnit = "[]"
  show PId = "Id"
  show PLift = "Lift"
  show PLiftTerm = "lift"
  show PLabel = "Label"
  show PEnum = "Enum"
  show PENil = "ENil"
  show PECons = "ECons"
  show PTag = "Tag"
  show PTZ = "TZ"
  show PTS = "TS"

instance Show PrimElimName where
  show PELower = "lower"
  show PEElimId = "elimId"
  show PEElimEnum = "elimEnum"
  show PEElimTag = "elimTag"

toPrimName :: String -> Maybe PrimName
toPrimName "()" = Just PUnitType
toPrimName "[]" = Just PUnit
toPrimName "Id" = Just PId
toPrimName "Lift" = Just PLift
toPrimName "lift" = Just PLiftTerm
toPrimName "Label" = Just PLabel
toPrimName "Enum" = Just PEnum
toPrimName "ENil" = Just PENil
toPrimName "ECons" = Just PECons
toPrimName "Tag" = Just PTag
toPrimName "TZ" = Just PTZ
toPrimName "TS" = Just PTS
toPrimName _ = Nothing

toPrimElimName :: String -> Maybe PrimElimName
toPrimElimName "lower" = Just PELower
toPrimElimName "elimId" = Just PEElimId
toPrimElimName "elimEnum" = Just PEElimEnum
toPrimElimName "elimTag" = Just PEElimTag
toPrimElimName _ = Nothing

data PrimElimPosition = PEPFirst | PEPLast | PEPThird

primElimPosition :: PrimElimName -> PrimElimPosition
primElimPosition _ = PEPLast

primElimIcit :: PrimElimName -> Icit
primElimIcit _ = Expl
