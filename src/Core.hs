module Core where

import Data.List (intercalate)

import Common
import Levels

type Ty = Tm

data Tm
  = Var Ix
  | App Tm Tm
  | Lam Name Tm
  | Pi Name Tm Tm
  | AppLvl Tm FinLevel
  | LamLvl Name Tm
  | PiLvl Name Tm
  | Let Name Ty Tm Tm
  | Type Level

showTmS :: Tm -> String
showTmS t@(Var _) = show t
showTmS t@(Type (FinLevel FLZ)) = show t
showTmS t = "(" ++ show t ++ ")"

showTmApp :: Tm -> String
showTmApp t =
  let (f, as) = go t in
  showTmS f ++ " " ++ unwords (map (either (\l -> "@" ++ showFinLevelS l) showTmS) as)
  where
    go :: Tm -> (Tm, [Either FinLevel Tm])
    go (App f a) = let (f', as) = go f in (f', Right a : as)
    go (AppLvl f a) =let (f', as) = go f in (f', Left a : as)
    go t = (t, [])

showTmLam :: Tm -> String
showTmLam t =
  let (xs, b) = go t in
  "\\" ++ unwords (map (either ("@" ++) id) xs) ++ ". " ++ show b
  where
    go :: Tm -> ([Either Name Name], Tm)
    go (Lam x b) = let (as, b') = go b in (Right x : as, b')
    go (LamLvl x b) = let (as, b') = go b in (Left x : as, b')
    go t = ([], t)

showTmPi :: Tm -> String
showTmPi t =
  let (ps, b) = go t in
  intercalate " -> " (map showParam ps) ++ " -> " ++ showApp b
  where
    go :: Tm -> ([(Name, Maybe Tm)], Tm)
    go (Pi x t b) = let (ps, b') = go b in ((x, Just t) : ps, b')
    go (PiLvl x b) = let (ps, b') = go b in ((x, Nothing) : ps, b')
    go t = ([], t)

    showApp :: Tm -> String
    showApp t@(App _ _) = show t
    showApp t@(AppLvl _ _) = show t
    showApp t = showTmS t

    showParam :: (Name, Maybe Tm) -> String
    showParam ("_", Just t) = showApp t
    showParam (x, Just t) = "(" ++ x ++ " : " ++ show t ++ ")"
    showParam (x, Nothing) = "@" ++ x

instance Show Tm where
  show (Var i) = "'" ++ show i
  show t@(App _ _) = showTmApp t
  show t@(Lam _ _) = showTmLam t
  show t@Pi {} = showTmPi t
  show t@(AppLvl _ _) = showTmApp t
  show t@(LamLvl _ _) = showTmLam t
  show t@(PiLvl _ _) = showTmPi t
  show (Let x t v b) = "let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b
  show (Type (FinLevel FLZ)) = "Type"
  show (Type l) = "Type " ++ showLevelS l
