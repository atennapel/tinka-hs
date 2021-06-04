module Core where

import Common

data Core
  = Var Ix
  | App Core Core
  | Abs Name Core Core
  | Pi Name Core Core
  | U Ix
  | Let Name Core Core Core

instance Show Core where
  show (Var x) = show x
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show (Abs x t b) = "(\\(" ++ x ++ " : " ++ show t ++ "). " ++ show b ++ ")"
  show (Pi x t b) = "((" ++ x ++ " : " ++ show t ++ ") -> " ++ show b ++ ")"
  show (U i) = "U" ++ show i
  show (Let x t v b) = "(let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b ++ ")"
