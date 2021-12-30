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
  | SApp STm STm (Either (Name, Impl) Icit)
  | SLam Name (Either (Name, Impl) Icit) (Maybe STy) STm
  | SPi Name Icit STm STm
  | SAppLvl STm SLevel (Maybe Name)
  | SLamLvl Name (Maybe Name) STm
  | SPiLvl Name STm
  | SProj STm SProjType
  | SPair STm STm
  | SSigma Name STm STm
  | SCon STm
  | SRefl
  | SLet Name (Maybe STy) STm STm
  | SType SLevel
  | SHole (Maybe Name)
  | SNatLit Int
  | SPos SourcePos STm

showSTmS :: STm -> String
showSTmS t@(SVar _) = show t
showSTmS t@SRefl = show t
showSTmS t@(SType (SLNat 0)) = show t
showSTmS t@(SPair _ _) = show t
showSTmS t@(SHole _) = show t
showSTmS t@(SNatLit _) = show t
showSTmS (SPos _ t) = showSTmS t
showSTmS t = "(" ++ show t ++ ")"

showSTmApp :: STm -> String
showSTmApp t =
  let (f, as) = go t in
  showSTmS f ++ " " ++ unwords (map showAppArgument $ reverse as)
  where
    go :: STm -> (STm, [Either (SLevel, Maybe Name) (STm, Either (Name, Impl) Icit)])
    go (SApp f a i) = let (f', as) = go f in (f', Right (a, i) : as)
    go (SAppLvl f a i) = let (f', as) = go f in (f', Left (a, i) : as)
    go (SPos _ s) = go s
    go t = (t, [])

    showAppArgument :: Either (SLevel, Maybe Name) (STm, Either (Name, Impl) Icit) -> String
    showAppArgument (Right (a, Right Expl)) = showSTmS a
    showAppArgument (Right (a, Right (Impl ImplUnif))) = "{" ++ show a ++ "}"
    showAppArgument (Right (a, Right (Impl ImplInst))) = "{{" ++ show a ++ "}}"
    showAppArgument (Right (a, Left (x, ImplUnif))) = "{" ++ showName x ++ " = " ++ show a ++ "}"
    showAppArgument (Right (a, Left (x, ImplInst))) = "{{" ++ showName x ++ " = " ++ show a ++ "}}"
    showAppArgument (Left (a, Just x)) = "<" ++ x ++ " = " ++ show a ++ ">"
    showAppArgument (Left (a, Nothing)) = "<" ++ show a ++ ">"

showSTmLam :: STm -> String
showSTmLam t =
  let (xs, b) = go t in
  "\\" ++ unwords (map showAbsParameter xs) ++ ". " ++ show b
  where
    go :: STm -> ([(Name, Either (Maybe Name) (Either (Name, Impl) Icit, Maybe STy))], STm)
    go (SLam x i t b) = let (as, b') = go b in ((x, Right (i, t)) : as, b')
    go (SLamLvl x i b) = let (as, b') = go b in ((x, Left i) : as, b')
    go (SPos _ s) = go s
    go t = ([], t)

    showAbsParameter :: (Name, Either (Maybe Name) (Either (Name, Impl) Icit, Maybe STy)) -> String
    showAbsParameter (x, Right (Right Expl, Nothing)) = showName x
    showAbsParameter (x, Right (Right Expl, Just t)) = "(" ++ showName x ++ " : " ++ show t ++ ")"
    showAbsParameter (x, Right (Right (Impl ImplUnif), Nothing)) = "{" ++ showName x ++ "}"
    showAbsParameter (x, Right (Right (Impl ImplInst), Nothing)) = "{{" ++ showName x ++ "}}"
    showAbsParameter (x, Right (Right (Impl ImplUnif), Just t)) = "{" ++ showName x ++ " : " ++ show t ++ "}"
    showAbsParameter (x, Right (Right (Impl ImplInst), Just t)) = "{{" ++ showName x ++ " : " ++ show t ++ "}}"
    showAbsParameter (x, Right (Left (y, ImplUnif), Nothing)) = "{" ++ showName x ++ " = " ++ y ++ "}"
    showAbsParameter (x, Right (Left (y, ImplInst), Nothing)) = "{{" ++ showName x ++ " = " ++ y ++ "}}"
    showAbsParameter (x, Right (Left (y, ImplUnif), Just t)) = "{" ++ showName x ++ " : " ++ show t ++ " = " ++ y ++ "}"
    showAbsParameter (x, Right (Left (y, ImplInst), Just t)) = "{{" ++ showName x ++ " : " ++ show t ++ " = " ++ y ++ "}}"
    showAbsParameter (x, Left (Just y)) = "<" ++ x ++ " = " ++ y ++ ">"
    showAbsParameter (x, Left Nothing) = "<" ++ x ++ ">"

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
    showApp t@SAppLvl {} = show t
    showApp t@(SType _) = show t
    showApp (SPos _ s) = showApp s
    showApp t = showSTmS t

    showParam :: (Name, Maybe (STm, Icit)) -> String
    showParam ("_", Just (t, Expl)) = showApp t
    showParam (x, Just (t, Expl)) = "(" ++ showName x ++ " : " ++ show t ++ ")"
    showParam (x, Just (t, Impl ImplUnif)) = "{" ++ showName x ++ " : " ++ show t ++ "}"
    showParam (x, Just (t, Impl ImplInst)) = "{{" ++ showName x ++ " : " ++ show t ++ "}}"
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
    showApp t@SAppLvl {} = show t
    showApp t@(SType _) = show t
    showApp (SPos _ s) = showApp s
    showApp t = showSTmS t

    showParam :: (Name, STm) -> String
    showParam ("_", t) = showApp t
    showParam (x, t) = "(" ++ showName x ++ " : " ++ show t ++ ")"

instance Show STm where
  show (SPos _ t) = show t
  show (SVar x) = showName x
  show (SHole x) = "_" ++ fromMaybe "" x
  show t@SApp {} = showSTmApp t
  show t@SLam {} = showSTmLam t
  show t@SPi {} = showSTmPi t
  show t@SAppLvl {} = showSTmApp t
  show t@SLamLvl {} = showSTmLam t
  show t@(SPiLvl _ _) = showSTmPi t
  show t@(SProj _ _) = showSTmProj t
  show t@(SPair _ _) = showSTmPair t
  show t@(SSigma _ _ _) = showSTmSigma t
  show (SCon t) = "Con " ++ showSTmS t
  show SRefl = "Refl"
  show (SLet x (Just t) v b) = "let " ++ showName x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b
  show (SLet x Nothing v b) = "let " ++ showName x ++ " = " ++ show v ++ "; " ++ show b
  show (SType (SLNat 0)) = "Type"
  show (SType l) = "Type " ++ showSLevelS l
  show (SNatLit i) = show i

data Decl
  = Def Name Bool (Maybe STy) STm
  | Import String

instance Show Decl where
  show (Def x inst (Just ty) tm) = (if inst then "instance " else "") ++ showName x ++ " : " ++ show ty ++ " = " ++ show tm
  show (Def x inst Nothing tm) = (if inst then "instance " else "") ++ showName x ++ " = " ++ show tm
  show (Import x) = "import " ++ x

type Decls = [Decl]

showDecls :: Decls -> String
showDecls [] = ""
showDecls (hd : tl) = show hd ++ "\n" ++ showDecls tl

declNames :: Decls -> [String]
declNames [] = []
declNames (Def x _ _ _ : t) = x : declNames t
declNames (_ : t) = declNames t

countNames :: Decls -> Int
countNames = length . declNames

imports :: Decls -> [String]
imports [] = []
imports (Import x : t) = x : imports t
imports (_ : t) = imports t
