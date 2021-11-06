module Core (Core(..), liftUniv, PrimName(..), toPrimName) where

import Common

data PrimName = PVoid | PAbsurd | PUnitType | PUnit
  deriving (Eq)

instance Show PrimName where
  show PVoid = "Void"
  show PAbsurd = "absurd"
  show PUnitType = "UnitType"
  show PUnit = "Unit"

toPrimName :: String -> Maybe PrimName
toPrimName "Void" = Just PVoid 
toPrimName "absurd" = Just PAbsurd 
toPrimName "UnitType" = Just PUnitType 
toPrimName "Unit" = Just PUnit 
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
  show (Global x l) = show x ++ "^" ++ show l
  show (Prim x l) = show x ++ "^" ++ show l
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (Abs x t b) = "(\\(" ++ x ++ " : " ++ show t ++ "). " ++ show b ++ ")"
  show (Pi x t b) = "((" ++ x ++ " : " ++ show t ++ ") -> " ++ show b ++ ")"
  show (Sigma x t b) = "((" ++ x ++ " : " ++ show t ++ ") ** " ++ show b ++ ")"
  show (Pair a b t) = "(" ++ show a ++ ", " ++ show b ++ ") : " ++ show t
  show (Proj s p) = show s ++ showProjType p
  show (U l) = "Type" ++ show l
  show (Let x t v b) = "(let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b ++ ")"

liftUniv :: ULvl -> Core -> Core
liftUniv l (U l') = U (l + l')
liftUniv l c@(Var _) = c
liftUniv l (Global x l') = Global x (l + l')
liftUniv l (Prim x l') = Prim x (l + l')
liftUniv l (App a b) = App (liftUniv l a) (liftUniv l b)
liftUniv l (Abs x t b) = Abs x (liftUniv l t) (liftUniv l b)
liftUniv l (Pi x t b) = Pi x (liftUniv l t) (liftUniv l b)
liftUniv l (Sigma x t b) = Sigma x (liftUniv l t) (liftUniv l b)
liftUniv l (Pair a b t) = Pair (liftUniv l a) (liftUniv l b) (liftUniv l t)
liftUniv l (Proj t p) = Proj (liftUniv l t) p
liftUniv l (Let x t v b) = Let x (liftUniv l t) (liftUniv l v) (liftUniv l b)
