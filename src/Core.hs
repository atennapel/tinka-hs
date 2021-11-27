module Core (ProjType(..), Core(..), liftUniv, PrimName(..), PrimElimName(..), toPrimName, toPrimElimName, PrimElimPosition(..), primElimPosition, allMetas, expandMetas) where

import Common
import Prims
import Universes

import qualified Data.Set as S
import Data.Set (Set)
import Data.List (elemIndex)
import Data.Maybe (fromJust)

data ProjType = Fst | Snd | PNamed (Maybe Name) Ix
  deriving (Eq)

data Core
  = Var Ix
  | Global Name ULvl
  | Prim PrimName ULvl
  | PrimElim PrimElimName ULvl ULvl
  | App Core Core Icit
  | AppPruning Core Pruning
  | Abs Name Icit Core
  | Pi Name Icit Core Univ Core Univ
  | Sigma Name Core Univ Core Univ
  | Pair Core Core
  | Proj Core ProjType
  | U Univ
  | Let Name Core Core Core
  | Lift Core
  | LiftTerm Core
  | Lower Core
  | Con Core
  | Refl
  | Meta MetaVar

showProjType :: ProjType -> String
showProjType Fst = "._1"
showProjType Snd = "._2"
showProjType (PNamed (Just x) _) = "." ++ x
showProjType (PNamed Nothing i) = "." ++ show i

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
  show (App f a i) = "(" ++ show f ++ icit i " {" " " ++ show a ++ icit i "})" ")"
  show (Abs x i b) = "(\\" ++ icit i "{" "" ++ x ++ icit i "}" "" ++ ". " ++ show b ++ ")"
  show (Pi x i t _ b _) = icit i "({" "((" ++ x ++ " : " ++ show t ++ icit i "}" ")" ++ " -> " ++ show b ++ ")"
  show (Sigma x t _ b _) = "((" ++ x ++ " : " ++ show t ++ ") ** " ++ show b ++ ")"
  show (Pair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (Proj s p) = show s ++ showProjType p
  show (U l) = "Type " ++ show l
  show (Let x t v b) = "(let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b ++ ")"
  show (Lift t) = "(Lift " ++ show t ++ ")"
  show (LiftTerm t) = "(lift " ++ show t ++ ")"
  show (Lower t) = "(lower " ++ show t ++ ")"
  show (Con t) = "(Con " ++ show t ++ ")"
  show Refl = "Refl"
  show (Meta x) = "?" ++ show x
  show (AppPruning x _) = show x ++ "*"

liftUniv :: ULvl -> Core -> Core
liftUniv l (U l') = U (uAddConst l l')
liftUniv l c@(Var _) = c
liftUniv l (Global x l') = Global x (l + l')
liftUniv l (Prim x l') = Prim x (l + l')
liftUniv l (PrimElim x l' k) = PrimElim x (l + l') k
liftUniv l (App a b i) = App (liftUniv l a) (liftUniv l b) i
liftUniv l (AppPruning t p) = AppPruning (liftUniv l t) p
liftUniv l (Abs x i b) = Abs x i (liftUniv l b)
liftUniv l (Pi x i t u1 b u2) = Pi x i (liftUniv l t) (us u1) (liftUniv l b) (us u2)
liftUniv l (Sigma x t u1 b u2) = Sigma x (liftUniv l t) (us u1) (liftUniv l b) (us u2)
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
allMetas (App a b _) = S.union (allMetas a) (allMetas b)
allMetas (AppPruning t _) = allMetas t
allMetas (Abs _ _ b) = allMetas b
allMetas (Pi x _ t _ b _) = S.union (allMetas t) (allMetas b)
allMetas (Sigma x t _ b _) = S.union (allMetas t) (allMetas b)
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
      let as = concatMap (\(i, bd) -> maybe [] (\pl -> [(Var i, pl)]) bd) $ zip [0..] bds in
      foldr (\(x, i) a -> App a x i) (go l t) as
    go l (U l') = U (normalizeUniv l')
    go l c@(Var _) = c
    go l (Global x l') = Global x l'
    go l (Prim x l') = Prim x l'
    go l (PrimElim x l' k) = PrimElim x l' k
    go l (App a b i) = App (go l a) (go l b) i
    go l (Abs x i b) = Abs x i (go (l + 1) b)
    go l (Pi x i t u1 b u2) = Pi x i (go l t) u1 (go (l + 1) b) u2
    go l (Sigma x t u1 b u2) = Sigma x (go l t) u1 (go (l + 1) b) u2
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
