module Core where

import Data.List (intercalate)

import Common
import Levels
import Prims

data ProjType = Fst | Snd | PNamed (Maybe Name) Ix
  deriving (Eq)

instance Show ProjType where
  show Fst = "._1"
  show Snd = "._2"
  show (PNamed (Just x) _) = "." ++ x
  show (PNamed Nothing i) = "." ++ show i

type Ty = Tm

data Tm
  = Var Ix
  | Global Name
  | Prim (Either PrimName PrimElimName)
  | App Tm Tm Icit
  | Lam Name Icit Tm
  | Pi Name Icit Tm Level Tm Level
  | AppLvl Tm FinLevel
  | LamLvl Name Tm
  | PiLvl Name Tm Level
  | Proj Tm ProjType
  | Pair Tm Tm
  | Sigma Name Tm Level Tm Level
  | Con Tm
  | Refl
  | Let Name Ty Tm Tm
  | Type Level
  | Meta MetaVar
  | InsertedMeta MetaVar [Maybe Icit]
  deriving (Eq)

capps :: Tm -> [Either FinLevel (Tm, Icit)] -> Tm
capps t [] = t
capps t (Left l : r) = capps (AppLvl t l) r
capps t (Right (a, i) : r) = capps (App t a i) r

cLiftTerm :: FinLevel -> FinLevel -> Ty -> Tm -> Tm
cLiftTerm k l a x = capps (Prim (Left PLiftTerm)) [Left k, Left l, Right (a, Impl), Right (x, Expl)]

showTmS :: Tm -> String
showTmS t@(Var _) = show t
showTmS t@(Pair _ _) = show t
showTmS t@(Global _) = show t
showTmS t@(Prim _) = show t
showTmS t@(Meta _) = show t
showTmS t@Refl = show t
showTmS t@(InsertedMeta _ _) = show t
showTmS t@(Type (FinLevel FLZ)) = show t
showTmS t = "(" ++ show t ++ ")"

showTmApp :: Tm -> String
showTmApp t =
  let (f, as) = go t in
  showTmS f ++ " " ++ unwords (map showAppArgument $ reverse as)
  where
    go :: Tm -> (Tm, [Either FinLevel (Tm, Icit)])
    go (App f a i) = let (f', as) = go f in (f', Right (a, i) : as)
    go (AppLvl f a) = let (f', as) = go f in (f', Left a : as)
    go t = (t, [])

    showAppArgument :: Either FinLevel (Tm, Icit) -> String
    showAppArgument (Right (a, Expl)) = showTmS a
    showAppArgument (Right (a, Impl)) = "{" ++ show a ++ "}"
    showAppArgument (Left a) = "<" ++ show a ++ ">"

showTmLam :: Tm -> String
showTmLam t =
  let (xs, b) = go t in
  "\\" ++ unwords (map showAbsParameter xs) ++ ". " ++ show b
  where
    go :: Tm -> ([(Name, Maybe Icit)], Tm)
    go (Lam x i b) = let (as, b') = go b in ((x, Just i) : as, b')
    go (LamLvl x b) = let (as, b') = go b in ((x, Nothing) : as, b')
    go t = ([], t)

    showAbsParameter :: (Name, Maybe Icit) -> String
    showAbsParameter (x, Just Expl) = x
    showAbsParameter (x, Just Impl) = "{" ++ x ++ "}"
    showAbsParameter (x, Nothing) = "<" ++ x ++ ">"

showTmPi :: Tm -> String
showTmPi t =
  let (ps, b) = go t in
  intercalate " -> " (map showParam ps) ++ " -> " ++ showApp b
  where
    go :: Tm -> ([(Name, Maybe (Icit, Tm))], Tm)
    go (Pi x i t _ b _) = let (ps, b') = go b in ((x, Just (i, t)) : ps, b')
    go (PiLvl x b _) = let (ps, b') = go b in ((x, Nothing) : ps, b')
    go t = ([], t)

    showApp :: Tm -> String
    showApp t@(App _ _ _) = show t
    showApp t@(AppLvl _ _) = show t
    showApp t@(Type _) = show t
    showApp t = showTmS t

    showParam :: (Name, Maybe (Icit, Tm)) -> String
    showParam ("_", Just (Expl, t)) = showApp t
    showParam (x, Just (Expl, t)) = "(" ++ x ++ " : " ++ show t ++ ")"
    showParam (x, Just (Impl, t)) = "{" ++ x ++ " : " ++ show t ++ "}"
    showParam (x, Nothing) = "<" ++ x ++ ">"

showTmPair :: Tm -> String
showTmPair s =
  let ps = flattenPair s in
    case last ps of
      Prim (Left PUnit) -> "[" ++ intercalate ", " (map show $ init ps) ++ "]"
      Refl -> "[" ++ intercalate ", " (map show $ init ps) ++ "]"
      _ -> "(" ++ intercalate ", " (map show ps) ++ ")"
  where
    flattenPair :: Tm -> [Tm]
    flattenPair (Pair a b) = a : flattenPair b
    flattenPair s = [s]

showTmProj :: Tm -> String
showTmProj s =
  let (s', ps) = flattenProj s in
  showTmS s' ++ intercalate "" (map show ps)
  where
    flattenProj :: Tm -> (Tm, [ProjType])
    flattenProj s = go s []
      where
        go (Proj b p) ps = go b (p : ps)
        go s ps = (s, ps)

showTmSigma :: Tm -> String
showTmSigma t =
  let (ps, b) = go t in
  intercalate " ** " (map showParam ps) ++ " ** " ++ showApp b
  where
    go :: Tm -> ([(Name, Tm)], Tm)
    go (Sigma x t _ b _) = let (ps, b') = go b in ((x, t) : ps, b')
    go t = ([], t)

    showApp :: Tm -> String
    showApp t@App {} = show t
    showApp t@(AppLvl _ _) = show t
    showApp t@(Type _) = show t
    showApp t = showTmS t

    showParam :: (Name, Tm) -> String
    showParam ("_", t) = showApp t
    showParam (x, t) = "(" ++ x ++ " : " ++ show t ++ ")"

instance Show Tm where
  show (Var i) = "'" ++ show i
  show (Global x) = x
  show (Prim (Left x)) = show x
  show (Prim (Right x)) = show x
  show t@(App _ _ _) = showTmApp t
  show t@(Lam _ _ _) = showTmLam t
  show t@Pi {} = showTmPi t
  show t@(AppLvl _ _) = showTmApp t
  show t@(LamLvl _ _) = showTmLam t
  show t@PiLvl {} = showTmPi t
  show t@(Proj _ _) = showTmProj t
  show t@(Pair _ _) = showTmPair t
  show t@Sigma {} = showTmSigma t
  show (Con t) = "Con " ++ showTmS t
  show Refl = "Refl"
  show (Let x t v b) = "let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b
  show (Type (FinLevel FLZ)) = "Type"
  show (Type l) = "Type " ++ showLevelS l
  show (Meta m) = "?" ++ show m
  show (InsertedMeta m _) = "?*" ++ show m
