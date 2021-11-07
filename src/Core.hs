module Core (Core(..), liftUniv, PrimName(..), toPrimName, canLiftPrim) where

import Common

data PrimName
  = PVoid | PAbsurd
  | PUnitType | PUnit
  | PBool | PTrue | PFalse | PIndBool
  | PHEq | PHRefl | PElimHEq
  deriving (Eq)

instance Show PrimName where
  show PVoid = "Void"
  show PAbsurd = "absurd"
  show PUnitType = "UnitType"
  show PUnit = "Unit"
  show PBool = "Bool"
  show PTrue = "True"
  show PFalse = "False"
  show PIndBool = "indBool"
  show PHEq = "HEq"
  show PHRefl = "HRefl"
  show PElimHEq = "elimHEq"

canLiftPrim :: PrimName -> Bool
canLiftPrim PAbsurd = True
canLiftPrim PIndBool = True
canLiftPrim PElimHEq = True
canLiftPrim _ = False

toPrimName :: String -> Maybe PrimName
toPrimName "Void" = Just PVoid
toPrimName "absurd" = Just PAbsurd
toPrimName "UnitType" = Just PUnitType
toPrimName "Unit" = Just PUnit
toPrimName "Bool" = Just PBool
toPrimName "True" = Just PTrue
toPrimName "False" = Just PFalse
toPrimName "indBool" = Just PIndBool
toPrimName "HEq" = Just PHEq
toPrimName "HRefl" = Just PHRefl
toPrimName "elimHEq" = Just PElimHEq
toPrimName _ = Nothing

data Core
  = Var Ix
  | Global Name ULvl
  | Prim PrimName ULvl
  | App Core Core
  | Abs Name Core Core
  | Pi Name Core Core
  | Sigma Name Core Core
  | Pair Core Core Core
  | Proj Core ProjType
  | U ULvl
  | Let Name Core Core Core

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
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (Abs x t b) = "(\\(" ++ x ++ " : " ++ show t ++ "). " ++ show b ++ ")"
  show (Pi x t b) = "((" ++ x ++ " : " ++ show t ++ ") -> " ++ show b ++ ")"
  show (Sigma x t b) = "((" ++ x ++ " : " ++ show t ++ ") ** " ++ show b ++ ")"
  show (Pair a b t) = "(" ++ show a ++ ", " ++ show b ++ ") : " ++ show t
  show (Proj s p) = show s ++ showProjType p
  show (U 0) = "Type"
  show (U l) = "Type" ++ show l
  show (Let x t v b) = "(let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b ++ ")"

liftUniv :: ULvl -> Core -> Core
liftUniv l (U l') = U (l + l')
liftUniv l c@(Var _) = c
liftUniv l (Global x l') = Global x (l + l')
liftUniv l (Prim x l') | canLiftPrim x = Prim x (l + l')
liftUniv l c@(Prim x l') = c
liftUniv l (App a b) = App (liftUniv l a) (liftUniv l b)
liftUniv l (Abs x t b) = Abs x (liftUniv l t) (liftUniv l b)
liftUniv l (Pi x t b) = Pi x (liftUniv l t) (liftUniv l b)
liftUniv l (Sigma x t b) = Sigma x (liftUniv l t) (liftUniv l b)
liftUniv l (Pair a b t) = Pair (liftUniv l a) (liftUniv l b) (liftUniv l t)
liftUniv l (Proj t p) = Proj (liftUniv l t) p
liftUniv l (Let x t v b) = Let x (liftUniv l t) (liftUniv l v) (liftUniv l b)
