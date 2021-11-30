module Core (ProjType(..), Level(..), Core(..), PrimName(..), PrimElimName(..), toPrimName, toPrimElimName, PrimElimPosition(..), primElimPosition, allMetas, expandMetas) where

import Common
import Prims

import qualified Data.Set as S
import Data.Set (Set)
import Data.List (elemIndex, intercalate)
import Data.Maybe (fromJust)

data ProjType = Fst | Snd | PNamed (Maybe Name) Ix
  deriving (Eq)

data Level = Fin Core | Omega
  deriving (Show)

data Core
  = Var Ix
  | Global Name
  | Prim PrimName
  | PrimElim PrimElimName
  | App Core Core Icit
  | AppPruning Core Pruning
  | Abs Name Icit Core
  | Pi Name Icit Core Level Core Level
  | Sigma Name Core Level Core Level
  | Pair Core Core
  | Proj Core ProjType
  | U Level
  | ULevel
  | L0
  | LS Core
  | LMax Core Core
  | Let Name Core Core Core
  | Lift Core
  | LiftTerm Core
  | Lower Core
  | Refl
  | Meta MetaVar

showProjType :: ProjType -> String
showProjType Fst = "._1"
showProjType Snd = "._2"
showProjType (PNamed (Just x) _) = "." ++ x
showProjType (PNamed Nothing i) = "." ++ show i

flattenApp :: Core -> (Core, [(Core, Icit)])
flattenApp s = go s []
  where
    go (App f a i) as = go f ((a, i) : as)
    go s as = (s, as)

flattenAbs :: Core -> ([(Name, Icit)], Core)
flattenAbs (Abs x i b) = let (as, s') = flattenAbs b in ((x, i) : as, s')
flattenAbs s = ([], s)

flattenPair :: Core -> [Core]
flattenPair (Pair a b) = a : flattenPair b
flattenPair s = [s]

flattenPi :: Core -> ([(Name, Icit, Core)], Core)
flattenPi (Pi x i t _ b _) = let (as, s') = flattenPi b in ((x, i, t) : as, s')
flattenPi s = ([], s)

flattenSigma :: Core -> ([(Name, Core)], Core)
flattenSigma (Sigma x t _ b _) = let (as, s') = flattenSigma b in ((x, t) : as, s')
flattenSigma s = ([], s)

showTelescope :: [(Name, Icit, Core)] -> Core -> String -> String
showTelescope ps rt delim = go ps
  where
    go [] = show rt
    go (("_", Expl, s) : tl) = show s ++ delim ++ go tl
    go ((x, i, s) : tl) = icit i "{" "(" ++ x ++ " : " ++ show s ++ icit i "}" ")" ++ delim ++ go tl

instance Show Core where
  show (Var x) = "'" ++ show x
  show (Global x) = x
  show (Prim x) = show x
  show (PrimElim x) = "elim " ++ show x
  show s@(App f a i) =
    let (f, as) = flattenApp s in
    "(" ++ show f ++ " " ++ unwords (map (\(a, i) -> icit i "{" "" ++ show a ++ icit i "}" "") as) ++ ")"
  show s@(Abs x i b) =
    let (as, b) = flattenAbs s in
    "(\\" ++ unwords (map (\(x, i) -> icit i "{" "" ++ x ++ icit i "}" "") as) ++ ". " ++ show b ++ ")"
  show s@(Pi x i t _ b _) =
    let (as, s') = flattenPi s in
    showTelescope as s' " -> "
  show s@(Sigma x t _ b _) =
    let (as, s') = flattenSigma s in
    showTelescope (map (\(x, t) -> (x, Expl, t)) as) s' " ** "
  show s@(Pair a b) =
    let ps = flattenPair s in
    case last ps of
      Prim PUnit -> "[" ++ intercalate ", " (map show $ init ps) ++ "]"
      _ -> "(" ++ intercalate ", " (map show ps) ++ ")"
  show (Proj s p) = show s ++ showProjType p
  show (U (Fin c)) = "Type " ++ show c
  show (U Omega) = "Type omega"
  show ULevel = "Level"
  show L0 = "L0"
  show (LS c) = "(LS " ++ show c ++ ")"
  show (LMax a b) = "(max " ++ show a ++ " " ++ show b ++ ")"
  show (Let x t v b) = "(let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b ++ ")"
  show (Lift t) = "(Lift " ++ show t ++ ")"
  show (LiftTerm t) = "(lift " ++ show t ++ ")"
  show (Lower t) = "(lower " ++ show t ++ ")"
  show Refl = "Refl"
  show (Meta x) = "?" ++ show x
  show (AppPruning x _) = show x ++ "*"

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
allMetas _ = S.empty

expandMetas :: [MetaVar] -> Core -> Core
expandMetas ms c = go 0 c
  where
    go :: Lvl -> Core -> Core
    go l (Meta x) = goMeta l x
    go l (AppPruning t bds) =
      let as = concatMap (\(i, bd) -> maybe [] (\pl -> [(Var i, pl)]) bd) $ zip [0..] bds in
      foldr (\(x, i) a -> App a x i) (go l t) as
    go l (U l') = U l'
    go l ULevel = ULevel
    go l L0 = L0
    go l (LS c) = LS (go l c)
    go l (LMax a b) = LMax (go l a) (go l b)
    go l c@(Var _) = c
    go l (Global x) = Global x
    go l (Prim x) = Prim x
    go l (PrimElim x) = PrimElim x
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
    go _ Refl = Refl

    goMeta :: Lvl -> MetaVar -> Core
    goMeta l x = let i = fromJust (elemIndex x ms) in Var (l + length ms - i - 1)
