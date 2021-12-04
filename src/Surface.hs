module Surface where

import Data.List (intercalate)
import Text.Megaparsec (SourcePos)
import Data.Maybe (fromMaybe)

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

data SProjType = SFst | SSnd | SIndex Ix | SNamed Name
  deriving (Eq)

instance Show SProjType where
  show SFst = "._1"
  show SSnd = "._2"
  show (SIndex i) = "." ++ show i
  show (SNamed x) = "." ++ x

type STy = STm

data STm
  = SVar Name
  | SApp STm STm
  | SLam Name STm
  | SPi Name STm STm
  | SAppLvl STm SLevel
  | SLamLvl Name STm
  | SPiLvl Name STm
  | SProj STm SProjType
  | SPair STm STm
  | SSigma Name STm STm
  | SLet Name STy STm STm
  | SType SLevel
  | SHole (Maybe Name)
  | SPos SourcePos STm

showSTmS :: STm -> String
showSTmS t@(SVar _) = show t
showSTmS t@(SType SLZ) = show t
showSTmS t@(SPair _ _) = show t
showSTmS t@(SHole _) = show t
showSTmS (SPos _ t) = showSTmS t
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

showSTmPair :: STm -> String
showSTmPair s =
  let ps = flattenPair s in
    case last ps of
      SVar "[]" -> "[" ++ intercalate ", " (map show $ init ps) ++ "]"
      _ -> "(" ++ intercalate ", " (map show ps) ++ ")"
  where
    flattenPair :: STm -> [STm]
    flattenPair (SPair a b) = a : flattenPair b
    flattenPair (SPos _ s) = flattenPair s
    flattenPair s = [s]

showSTmProj :: STm -> String
showSTmProj s =
  let (s', ps) = flattenProj s in
  showSTmS s' ++ intercalate "" (map show ps)
  where
    flattenProj :: STm -> (STm, [SProjType])
    flattenProj s = go s []
      where
        go (SProj b p) ps = go b (p : ps)
        go (SPos _ s) ps = go s ps
        go s ps = (s, ps)

showSTmSigma :: STm -> String
showSTmSigma t =
  let (ps, b) = go t in
  intercalate " ** " (map showParam ps) ++ " ** " ++ showApp b
  where
    go :: STm -> ([(Name, STm)], STm)
    go (SSigma x t b) = let (ps, b') = go b in ((x, t) : ps, b')
    go t = ([], t)

    showApp :: STm -> String
    showApp t@(SApp _ _) = show t
    showApp t@(SAppLvl _ _) = show t
    showApp t = showSTmS t

    showParam :: (Name, STm) -> String
    showParam ("_", t) = showApp t
    showParam (x, t) = "(" ++ x ++ " : " ++ show t ++ ")"

instance Show STm where
  show (SPos _ t) = show t
  show (SVar x) = x
  show (SHole x) = "_" ++ fromMaybe "" x
  show t@(SApp _ _) = showSTmApp t
  show t@(SLam _ _) = showSTmLam t
  show t@SPi {} = showSTmPi t
  show t@(SAppLvl _ _) = showSTmApp t
  show t@(SLamLvl _ _) = showSTmLam t
  show t@(SPiLvl _ _) = showSTmPi t
  show t@(SProj _ _) = showSTmProj t
  show t@(SPair _ _) = showSTmPair t
  show t@(SSigma _ _ _) = showSTmSigma t
  show (SLet x t v b) = "let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b
  show (SType SLZ) = "Type"
  show (SType l) = "Type " ++ showSLevelS l
