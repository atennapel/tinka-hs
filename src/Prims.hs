module Prims where

import Common

data PrimName
  = PUnitType | PUnit
  | PLift | PLiftTerm
  deriving (Eq, Ord)

data PrimElimName
  = PELower
  deriving (Eq)

instance Show PrimName where
  show PUnitType = "()"
  show PUnit = "[]"
  show PLift = "Lift"
  show PLiftTerm = "lift"

instance Show PrimElimName where
  show PELower = "lower"

toPrimName :: String -> Maybe PrimName
toPrimName "()" = Just PUnitType
toPrimName "[]" = Just PUnit
toPrimName "Lift" = Just PLift
toPrimName "lift" = Just PLiftTerm
toPrimName _ = Nothing

toPrimElimName :: String -> Maybe PrimElimName
toPrimElimName "lower" = Just PELower
toPrimElimName _ = Nothing

data PrimElimPosition = PEPFirst | PEPLast | PEPThird

primElimPosition :: PrimElimName -> PrimElimPosition
primElimPosition _ = PEPLast

primElimIcit :: PrimElimName -> Icit
primElimIcit _ = Expl
