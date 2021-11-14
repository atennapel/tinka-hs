module Core (Core(..), liftUniv, PrimName(..), PrimElimName(..), toPrimName, toPrimElimName, PrimElimPosition(..), primElimPosition) where

import Common

data PrimName
  = PVoid
  | PUnitType | PUnit
  | PBool | PTrue | PFalse
  | PHEq | PHRefl
  | PDesc | PEnd | PArg | PInd | PHInd | PData | PCon
  deriving (Eq)

data PrimElimName
  = PEVoid
  | PEBool
  | PEHEq
  | PEDesc
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
  show PHRefl = "HRefl"
  show PDesc = "Desc"
  show PEnd = "End"
  show PArg = "Arg"
  show PInd = "Ind"
  show PHInd = "HInd"
  show PData = "Data"
  show PCon = "Con"

instance Show PrimElimName where
  show PEVoid = "Void"
  show PEBool = "Bool"
  show PEHEq = "HEq"
  show PEDesc = "Desc"
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
toPrimName "HRefl" = Just PHRefl
toPrimName "Desc" = Just PDesc
toPrimName "End" = Just PEnd
toPrimName "Arg" = Just PArg
toPrimName "Ind" = Just PInd
toPrimName "HInd" = Just PHInd
toPrimName "Data" = Just PData
toPrimName "Con" = Just PCon
toPrimName _ = Nothing

toPrimElimName :: String -> Maybe PrimElimName
toPrimElimName "Void" = Just PEVoid
toPrimElimName "Bool" = Just PEBool
toPrimElimName "HEq" = Just PEHEq
toPrimElimName "Desc" = Just PEDesc
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

data Core
  = Var Ix
  | Global Name ULvl
  | Prim PrimName ULvl
  | PrimElim PrimElimName ULvl ULvl
  | App Core Core
  | Abs Name Core Core
  | Pi Name Core Core
  | Sigma Name Core Core
  | Pair Core Core Core
  | Proj Core ProjType
  | U ULvl
  | Let Name Core Core Core
  | Lift Core
  | LiftTerm Core
  | Lower Core

showProjType :: ProjType -> String
showProjType Fst = ".1"
showProjType Snd = ".2"

instance Show Core where
  show (Var x) = show x
  show (Global x 0) = x
  show (Global x 1) = x ++ "^"
  show (Global x l) = x ++ "^" ++ show l
  show (Prim x 0) = show x
  show (Prim x 1) = show x ++ "^"
  show (Prim x l) = show x ++ "^" ++ show l
  show (PrimElim x 0 k) = "elim " ++ show x ++ (if k == 0 then "" else " " ++ show k)
  show (PrimElim x 1 k) = "elim " ++ show x ++ "^" ++ (if k == 0 then "" else " " ++ show k)
  show (PrimElim x l k) = "elim " ++ show x ++ "^" ++ show l ++ (if k == 0 then "" else " " ++ show k)
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (Abs x t b) = "(\\(" ++ x ++ " : " ++ show t ++ "). " ++ show b ++ ")"
  show (Pi x t b) = "((" ++ x ++ " : " ++ show t ++ ") -> " ++ show b ++ ")"
  show (Sigma x t b) = "((" ++ x ++ " : " ++ show t ++ ") ** " ++ show b ++ ")"
  show (Pair a b t) = "(" ++ show a ++ ", " ++ show b ++ ") : " ++ show t
  show (Proj s p) = show s ++ showProjType p
  show (U 0) = "Type"
  show (U l) = "Type" ++ show l
  show (Let x t v b) = "(let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b ++ ")"
  show (Lift t) = "(Lift " ++ show t ++ ")"
  show (LiftTerm t) = "(lift " ++ show t ++ ")"
  show (Lower t) = "(lower " ++ show t ++ ")"

liftUniv :: ULvl -> Core -> Core
liftUniv l (U l') = U (l + l')
liftUniv l c@(Var _) = c
liftUniv l (Global x l') = Global x (l + l')
liftUniv l (Prim x l') = Prim x (l + l')
liftUniv l (PrimElim x l' k) = PrimElim x (l + l') k
liftUniv l (App a b) = App (liftUniv l a) (liftUniv l b)
liftUniv l (Abs x t b) = Abs x (liftUniv l t) (liftUniv l b)
liftUniv l (Pi x t b) = Pi x (liftUniv l t) (liftUniv l b)
liftUniv l (Sigma x t b) = Sigma x (liftUniv l t) (liftUniv l b)
liftUniv l (Pair a b t) = Pair (liftUniv l a) (liftUniv l b) (liftUniv l t)
liftUniv l (Proj t p) = Proj (liftUniv l t) p
liftUniv l (Let x t v b) = Let x (liftUniv l t) (liftUniv l v) (liftUniv l b)
liftUniv l (Lift t) = Lift (liftUniv l t)
liftUniv l (LiftTerm t) = LiftTerm (liftUniv l t)
liftUniv l (Lower t) = Lower (liftUniv l t)
