module Core (Core(..), liftUniv, PrimName(..), PrimElimName(..), toPrimName, toPrimElimName, PrimElimPosition(..), primElimPosition, allMetas, expandMetas) where

import Common
import Prims

import qualified Data.Set as S
import Data.Set (Set)
import Data.List (elemIndex)
import Data.Maybe (fromJust)

data Core
  = Var Ix
  | Global Name ULvl
  | Prim PrimName ULvl
  | PrimElim PrimElimName ULvl ULvl
  | App Core Core
  | AppPruning Core Pruning
  | Abs Name Core
  | Pi Name Core Core
  | Sigma Name Core Core
  | Pair Core Core
  | Proj Core ProjType
  | U ULvl
  | Let Name Core Core Core
  | Lift Core
  | LiftTerm Core
  | Lower Core
  | Con Core
  | Refl
  | Meta MetaVar

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
  show (Abs x b) = "(\\" ++ x ++ ". " ++ show b ++ ")"
  show (Pi x t b) = "((" ++ x ++ " : " ++ show t ++ ") -> " ++ show b ++ ")"
  show (Sigma x t b) = "((" ++ x ++ " : " ++ show t ++ ") ** " ++ show b ++ ")"
  show (Pair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (Proj s p) = show s ++ showProjType p
  show (U 0) = "Type"
  show (U l) = "Type" ++ show l
  show (Let x t v b) = "(let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b ++ ")"
  show (Lift t) = "(Lift " ++ show t ++ ")"
  show (LiftTerm t) = "(lift " ++ show t ++ ")"
  show (Lower t) = "(lower " ++ show t ++ ")"
  show (Con t) = "(Con " ++ show t ++ ")"
  show Refl = "Refl"
  show (Meta x) = "?" ++ show x
  show (AppPruning x _) = show x ++ "*"

liftUniv :: ULvl -> Core -> Core
liftUniv l (U l') = U (l + l')
liftUniv l c@(Var _) = c
liftUniv l (Global x l') = Global x (l + l')
liftUniv l (Prim x l') = Prim x (l + l')
liftUniv l (PrimElim x l' k) = PrimElim x (l + l') k
liftUniv l (App a b) = App (liftUniv l a) (liftUniv l b)
liftUniv l (AppPruning t p) = AppPruning (liftUniv l t) p
liftUniv l (Abs x b) = Abs x (liftUniv l b)
liftUniv l (Pi x t b) = Pi x (liftUniv l t) (liftUniv l b)
liftUniv l (Sigma x t b) = Sigma x (liftUniv l t) (liftUniv l b)
liftUniv l (Pair a b) = Pair (liftUniv l a) (liftUniv l b)
liftUniv l (Proj t p) = Proj (liftUniv l t) p
liftUniv l (Let x t v b) = Let x (liftUniv l t) (liftUniv l v) (liftUniv l b)
liftUniv l (Lift t) = Lift (liftUniv l t)
liftUniv l (LiftTerm t) = LiftTerm (liftUniv l t)
liftUniv l (Lower t) = Lower (liftUniv l t)
liftUniv l (Con t) = Con (liftUniv l t)
liftUniv _ Refl = Refl
liftUniv _ c@(Meta _) = c

allMetas :: Core -> Set MetaVar
allMetas (Meta x) = S.singleton x
allMetas (App a b) = S.union (allMetas a) (allMetas b)
allMetas (AppPruning t _) = allMetas t
allMetas (Abs _ b) = allMetas b
allMetas (Pi x t b) = S.union (allMetas t) (allMetas b)
allMetas (Sigma x t b) = S.union (allMetas t) (allMetas b)
allMetas (Pair t b) = S.union (allMetas t) (allMetas b)
allMetas (Proj t _) = allMetas t
allMetas (Let _ t v b) = S.union (allMetas t) $ S.union (allMetas v) (allMetas b)
allMetas (Lift t) = allMetas t
allMetas (LiftTerm t) = allMetas t
allMetas (Lower t) = allMetas t
allMetas (Con t) = allMetas t
allMetas _ = S.empty

expandMetas :: [MetaVar] -> Core -> Core
expandMetas ms c = go 0 c
  where
    go :: Lvl -> Core -> Core
    go l (Meta x) = goMeta l x
    go l (AppPruning t bds) =
      let as = concatMap (\(i, bd) -> [Var i | bd == Just ()]) $ zip [0..] bds in
      foldr (flip App) (go l t) as
    go l (U l') = U l'
    go l c@(Var _) = c
    go l (Global x l') = Global x l'
    go l (Prim x l') = Prim x l'
    go l (PrimElim x l' k) = PrimElim x l' k
    go l (App a b) = App (go l a) (go l b)
    go l (Abs x b) = Abs x (go (l + 1) b)
    go l (Pi x t b) = Pi x (go l t) (go (l + 1) b)
    go l (Sigma x t b) = Sigma x (go l t) (go (l + 1) b)
    go l (Pair a b) = Pair (go l a) (go l b)
    go l (Proj t p) = Proj (go l t) p
    go l (Let x t v b) = Let x (go l t) (go l v) (go (l + 1) b)
    go l (Lift t) = Lift (go l t)
    go l (LiftTerm t) = LiftTerm (go l t)
    go l (Lower t) = Lower (go l t)
    go l (Con t) = Con (go l t)
    go _ Refl = Refl

    goMeta :: Lvl -> MetaVar -> Core
    goMeta l x = let i = fromJust (elemIndex x ms) in Var (l + length ms - i - 1)
