module Prims where

import Common

data PrimName
  = PUnitType | PUnit
  | PLift | PLiftTerm
  | PTy | PEnd | PArg | PInd | PHInd
  | PCtx | PEmpty | PExt
  | PVar | PVZ | PVS
  | PTm | PEl | PApp | PAppInd | PAppHInd
  deriving (Eq, Ord)

data PrimElimName
  = PELower
  deriving (Eq)

instance Show PrimName where
  show PUnitType = "()"
  show PUnit = "[]"

  show PLift = "Lift"
  show PLiftTerm = "lift"

  show PTy = "Ty"
  show PEnd = "End"
  show PArg = "Arg"
  show PInd = "Ind"
  show PHInd = "HInd"

  show PCtx = "Ctx"
  show PEmpty = "Empty"
  show PExt = "Ext"

  show PVar = "Var"
  show PVZ = "VZ"
  show PVS = "VS"

  show PTm = "Tm"
  show PEl = "El"
  show PApp = "App"
  show PAppInd = "AppInd"
  show PAppHInd = "AppHInd"

instance Show PrimElimName where
  show PELower = "lower"

toPrimName :: String -> Maybe PrimName
toPrimName "()" = Just PUnitType
toPrimName "[]" = Just PUnit

toPrimName "Lift" = Just PLift
toPrimName "lift" = Just PLiftTerm

toPrimName "Ty" = Just PTy
toPrimName "End" = Just PEnd
toPrimName "Arg" = Just PArg
toPrimName "Ind" = Just PInd
toPrimName "HInd" = Just PHInd

toPrimName "Ctx" = Just PCtx
toPrimName "Empty" = Just PEmpty
toPrimName "Ext" = Just PExt

toPrimName "Var" = Just PVar
toPrimName "VZ" = Just PVZ
toPrimName "VS" = Just PVS

toPrimName "Tm" = Just PTm
toPrimName "El" = Just PEl
toPrimName "App" = Just PApp
toPrimName "AppInd" = Just PAppInd
toPrimName "AppHInd" = Just PAppHInd

toPrimName _ = Nothing

toPrimElimName :: String -> Maybe PrimElimName
toPrimElimName "lower" = Just PELower
toPrimElimName _ = Nothing

data PrimElimPosition = PEPFirst | PEPLast | PEPThird

primElimPosition :: PrimElimName -> PrimElimPosition
primElimPosition _ = PEPLast

primElimIcit :: PrimElimName -> Icit
primElimIcit _ = Expl
