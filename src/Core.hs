module Core (Core(..)) where

import Common

data Core
  = Var Ix
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
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (Abs x t b) = "(\\(" ++ x ++ " : " ++ show t ++ "). " ++ show b ++ ")"
  show (Pi x t b) = "((" ++ x ++ " : " ++ show t ++ ") -> " ++ show b ++ ")"
  show (Sigma x t b) = "((" ++ x ++ " : " ++ show t ++ ") ** " ++ show b ++ ")"
  show (Pair a b t) = "(" ++ show a ++ ", " ++ show b ++ ") : " ++ show t
  show (Proj s p) = show s ++ showProjType p
  show (U l) = "Type" ++ show l
  show (Let x t v b) = "(let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b ++ ")"
