module Surface where

import Data.List (intercalate)
import Text.Megaparsec (SourcePos)
import Data.Maybe (fromMaybe)

import Common

data SLevel
  = SLVar Name
  | SLS SLevel
  | SLMax SLevel SLevel
  | SLNat Int

showSLevelS :: SLevel -> String
showSLevelS l@(SLNat _) = show l
showSLevelS l@(SLVar _) = show l
showSLevelS l = "(" ++ show l ++ ")"

instance Show SLevel where
  show (SLVar x) = x
  show (SLNat i) = show i
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
  | SApp STm STm (Either Name Icit)
  | SLam Name (Either Name Icit) (Maybe STy) STm
  | SPi Name Icit STm STm
  | SAppLvl STm SLevel
  | SLamLvl Name STm
  | SPiLvl Name STm
  | SProj STm SProjType
  | SPair STm STm
  | SSigma Name STm STm
  | SCon STm
  | SRefl
  | SLet Name (Maybe STy) STm STm
  | SType SLevel
  | SHole (Maybe Name)
  | SPos SourcePos STm

showSTmS :: STm -> String
showSTmS t@(SVar _) = show t
showSTmS t@SRefl = show t
showSTmS t@(SType (SLNat 0)) = show t
showSTmS t@(SPair _ _) = show t
showSTmS t@(SHole _) = show t
showSTmS (SPos _ t) = showSTmS t
showSTmS t = "(" ++ show t ++ ")"

showSTmApp :: STm -> String
showSTmApp t =
  let (f, as) = go t in
  showSTmS f ++ " " ++ unwords (map showAppArgument $ reverse as)
  where
    go :: STm -> (STm, [Either SLevel (STm, Either Name Icit)])
    go (SApp f a i) = let (f', as) = go f in (f', Right (a, i) : as)
    go (SAppLvl f a) = let (f', as) = go f in (f', Left a : as)
    go (SPos _ s) = go s
    go t = (t, [])

    showAppArgument :: Either SLevel (STm, Either Name Icit) -> String
    showAppArgument (Right (a, Right Expl)) = showSTmS a
    showAppArgument (Right (a, Right Impl)) = "{" ++ show a ++ "}"
    showAppArgument (Right (a, Left x)) = "{" ++ x ++ " = " ++ show a ++ "}"
    showAppArgument (Left a) = "<" ++ show a ++ ">"

showSTmLam :: STm -> String
showSTmLam t =
  let (xs, b) = go t in
  "\\" ++ unwords (map showAbsParameter xs) ++ ". " ++ show b
  where
    go :: STm -> ([(Name, Maybe (Either Name Icit, Maybe STy))], STm)
    go (SLam x i t b) = let (as, b') = go b in ((x, Just (i, t)) : as, b')
    go (SLamLvl x b) = let (as, b') = go b in ((x, Nothing) : as, b')
    go (SPos _ s) = go s
    go t = ([], t)

    showAbsParameter :: (Name, Maybe (Either Name Icit, Maybe STy)) -> String
    showAbsParameter (x, Just (Right Expl, Nothing)) = x
    showAbsParameter (x, Just (Right Expl, Just t)) = "(" ++ x ++ " : " ++ show t ++ ")"
    showAbsParameter (x, Just (Right Impl, Nothing)) = "{" ++ x ++ "}"
    showAbsParameter (x, Just (Right Impl, Just t)) = "{" ++ x ++ " : " ++ show t ++ "}"
    showAbsParameter (x, Just (Left y, Nothing)) = "{" ++ x ++ " = " ++ y ++ "}"
    showAbsParameter (x, Just (Left y, Just t)) = "{" ++ x ++ " : " ++ show t ++ " = " ++ y ++ "}"
    showAbsParameter (x, Nothing) = "<" ++ x ++ ">"

showSTmPi :: STm -> String
showSTmPi t =
  let (ps, b) = go t in
  intercalate " -> " (map showParam ps) ++ " -> " ++ showApp b
  where
    go :: STm -> ([(Name, Maybe (STm, Icit))], STm)
    go (SPi x i t b) = let (ps, b') = go b in ((x, Just (t, i)) : ps, b')
    go (SPiLvl x b) = let (ps, b') = go b in ((x, Nothing) : ps, b')
    go (SPos _ s) = go s
    go t = ([], t)

    showApp :: STm -> String
    showApp t@SApp {} = show t
    showApp t@(SAppLvl _ _) = show t
    showApp t@(SType _) = show t
    showApp (SPos _ s) = showApp s
    showApp t = showSTmS t

    showParam :: (Name, Maybe (STm, Icit)) -> String
    showParam ("_", Just (t, Expl)) = showApp t
    showParam (x, Just (t, Expl)) = "(" ++ x ++ " : " ++ show t ++ ")"
    showParam (x, Just (t, Impl)) = "{" ++ x ++ " : " ++ show t ++ "}"
    showParam (x, Nothing) = "<" ++ x ++ ">"

showSTmPair :: STm -> String
showSTmPair s =
  let ps = flattenPair s in
    case last ps of
      SVar "[]" -> "[" ++ intercalate ", " (map show $ init ps) ++ "]"
      SRefl -> "[" ++ intercalate ", " (map show $ init ps) ++ "]"
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
    go (SPos _ s) = go s
    go t = ([], t)

    showApp :: STm -> String
    showApp t@SApp {} = show t
    showApp t@(SAppLvl _ _) = show t
    showApp t@(SType _) = show t
    showApp (SPos _ s) = showApp s
    showApp t = showSTmS t

    showParam :: (Name, STm) -> String
    showParam ("_", t) = showApp t
    showParam (x, t) = "(" ++ x ++ " : " ++ show t ++ ")"

instance Show STm where
  show (SPos _ t) = show t
  show (SVar x) = x
  show (SHole x) = "_" ++ fromMaybe "" x
  show t@SApp {} = showSTmApp t
  show t@SLam {} = showSTmLam t
  show t@SPi {} = showSTmPi t
  show t@(SAppLvl _ _) = showSTmApp t
  show t@(SLamLvl _ _) = showSTmLam t
  show t@(SPiLvl _ _) = showSTmPi t
  show t@(SProj _ _) = showSTmProj t
  show t@(SPair _ _) = showSTmPair t
  show t@(SSigma _ _ _) = showSTmSigma t
  show (SCon t) = "Con " ++ showSTmS t
  show SRefl = "Refl"
  show (SLet x (Just t) v b) = "let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b
  show (SLet x Nothing v b) = "let " ++ x ++ " = " ++ show v ++ "; " ++ show b
  show (SType (SLNat 0)) = "Type"
  show (SType l) = "Type " ++ showSLevelS l

data Decl
  = Def Name (Maybe STy) STm
  | Import String

instance Show Decl where
  show (Def x (Just ty) tm) = x ++ " : " ++ show ty ++ " = " ++ show tm
  show (Def x Nothing tm) = x ++ " = " ++ show tm
  show (Import x) = "import " ++ x

type Decls = [Decl]

showDecls :: Decls -> String
showDecls [] = ""
showDecls (hd : tl) = show hd ++ "\n" ++ showDecls tl

declNames :: Decls -> [String]
declNames [] = []
declNames (Def x _ _ : t) = x : declNames t
declNames (_ : t) = declNames t

countNames :: Decls -> Int
countNames = length . declNames

imports :: Decls -> [String]
imports [] = []
imports (Import x : t) = x : imports t
imports (_ : t) = imports t
