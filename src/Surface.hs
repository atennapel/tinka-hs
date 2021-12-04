module Surface where

import Data.List (intercalate)

import Common

data SLevel
  = SLVar Name
  | SLZ
  | SLS SLevel
  | SLMax SLevel SLevel

showSLevelS :: SLevel -> String
showSLevelS l@SLZ = show l
showSLevelS l@(SLVar _) = show l
showSLevelS l = "(" ++ show l ++ ")"

instance Show SLevel where
  show (SLVar x) = x
  show SLZ = "Z"
  show (SLS l) = "S " ++ showSLevelS l
  show (SLMax a b) = "max " ++ showSLevelS a ++ " " ++ showSLevelS b

type STy = STm

data STm
  = SVar Name
  | SApp STm STm
  | SLam Name STm
  | SPi Name STm STm
  | SAppLvl STm SLevel
  | SLamLvl Name STm
  | SPiLvl Name STm
  | SLet Name STy STm STm
  | SType SLevel

showSTmS :: STm -> String
showSTmS t@(SVar _) = show t
showSTmS t@(SType SLZ) = show t
showSTmS t = "(" ++ show t ++ ")"

showSTmApp :: STm -> String
showSTmApp t =
  let (f, as) = go t in
  showSTmS f ++ " " ++ unwords (map (either (\l -> "@" ++ showSLevelS l) showSTmS) as)
  where
    go :: STm -> (STm, [Either SLevel STm])
    go (SApp f a) = let (f', as) = go f in (f', Right a : as)
    go (SAppLvl f a) =let (f', as) = go f in (f', Left a : as)
    go t = (t, [])

showSTmLam :: STm -> String
showSTmLam t =
  let (xs, b) = go t in
  "\\" ++ unwords (map (either ("@" ++) id) xs) ++ ". " ++ show b
  where
    go :: STm -> ([Either Name Name], STm)
    go (SLam x b) = let (as, b') = go b in (Right x : as, b')
    go (SLamLvl x b) = let (as, b') = go b in (Left x : as, b')
    go t = ([], t)

showSTmPi :: STm -> String
showSTmPi t =
  let (ps, b) = go t in
  intercalate " -> " (map showParam ps) ++ " -> " ++ showApp b
  where
    go :: STm -> ([(Name, Maybe STm)], STm)
    go (SPi x t b) = let (ps, b') = go b in ((x, Just t) : ps, b')
    go (SPiLvl x b) = let (ps, b') = go b in ((x, Nothing) : ps, b')
    go t = ([], t)

    showApp :: STm -> String
    showApp t@(SApp _ _) = show t
    showApp t@(SAppLvl _ _) = show t
    showApp t = showSTmS t

    showParam :: (Name, Maybe STm) -> String
    showParam ("_", Just t) = showApp t
    showParam (x, Just t) = "(" ++ x ++ " : " ++ show t ++ ")"
    showParam (x, Nothing) = "@" ++ x

instance Show STm where
  show (SVar x) = x
  show t@(SApp _ _) = showSTmApp t
  show t@(SLam _ _) = showSTmLam t
  show t@SPi {} = showSTmPi t
  show t@(SAppLvl _ _) = showSTmApp t
  show t@(SLamLvl _ _) = showSTmLam t
  show t@(SPiLvl _ _) = showSTmPi t
  show (SLet x t v b) = "let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b
  show (SType SLZ) = "Type"
  show (SType l) = "Type " ++ showSLevelS l
