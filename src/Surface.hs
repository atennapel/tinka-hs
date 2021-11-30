module Surface (SProjType(..), Surface(..), fromCore, Def(..), Defs, showDefs, defNames, countNames, imports) where

import GHC.Exts(IsString(..))
import Data.List (intercalate)
import Text.Megaparsec (SourcePos)
import Data.Maybe (fromMaybe)

import Common
import Core

data SProjType = SFst | SSnd | SIndex Ix | SNamed Name
  deriving (Eq)

data Surface
  = SVar Name
  | SPrimElim Name
  | SApp Surface Surface (Either Name Icit)
  | SAbs Name (Either Name Icit) (Maybe Surface) Surface
  | SPi Name Icit Surface Surface
  | SSigma Name Surface Surface
  | SPair Surface Surface
  | SProj Surface SProjType
  | SU Surface
  | SLevel
  | SL0
  | SLS Surface
  | SLMax Surface Surface
  | SLet Name (Maybe Surface) Surface Surface
  | SPos SourcePos Surface
  | SHole (Maybe Name)
  | SLift Surface
  | SLiftTerm Surface
  | SLower Surface
  | SRefl

isSimple :: Surface -> Bool
isSimple (SVar _) = True
isSimple (SHole _) = True
isSimple (SPair _ _) = True
isSimple SRefl = True
isSimple (SProj _ _) = True
isSimple SLevel = True
isSimple SL0 = True
isSimple (SPos _ s) = isSimple s
isSimple _ = False

showS :: Surface -> String
showS s = if isSimple s then show s else "(" ++ show s ++ ")"

flattenApp :: Surface -> (Surface, [(Surface, Either Name Icit)])
flattenApp s = go s []
  where
    go (SApp f a i) as = go f ((a, i) : as)
    go (SPos _ s) as = go s as
    go s as = (s, as)

flattenAbs :: Surface -> ([(Name, Either Name Icit, Maybe Surface)], Surface)
flattenAbs (SAbs x i t b) = let (as, s') = flattenAbs b in ((x, i, t) : as, s')
flattenAbs (SPos _ s) = flattenAbs s
flattenAbs s = ([], s)

flattenPi :: Surface -> ([(Name, Icit, Surface)], Surface)
flattenPi (SPi x i t b) = let (as, s') = flattenPi b in ((x, i, t) : as, s')
flattenPi (SPos _ s) = flattenPi s
flattenPi s = ([], s)

flattenSigma :: Surface -> ([(Name, Surface)], Surface)
flattenSigma (SSigma x t b) = let (as, s') = flattenSigma b in ((x, t) : as, s')
flattenSigma (SPos _ s) = flattenSigma s
flattenSigma s = ([], s)

flattenPair :: Surface -> [Surface]
flattenPair (SPair a b) = a : flattenPair b
flattenPair (SPos _ s) = flattenPair s
flattenPair s = [s]

flattenProj :: Surface -> (Surface, [SProjType])
flattenProj s = go s []
  where
    go (SProj b p) ps = go b (p : ps)
    go (SPos _ s) ps = go s ps
    go s ps = (s, ps)

showTelescope :: [(Name, Icit, Surface)] -> Surface -> String -> String
showTelescope ps rt delim = go ps
  where
    go [] = show rt
    go (("_", Expl, s@SApp {}) : tl) = show s ++ delim ++ go tl
    go (("_", Expl, SPos _ s@SApp {}) : tl) = show s ++ delim ++ go tl
    go (("_", Expl, s@SU {}) : tl) = show s ++ delim ++ go tl
    go (("_", Expl, SPos _ s@SU {}) : tl) = show s ++ delim ++ go tl
    go (("_", Expl, s) : tl) = showS s ++ delim ++ go tl
    go ((x, i, s) : tl) = icit i "{" "(" ++ x ++ " : " ++ show s ++ icit i "}" ")" ++ delim ++ go tl

showSProjType :: SProjType -> String
showSProjType SFst = "._1"
showSProjType SSnd = "._2"
showSProjType (SIndex i) = "." ++ show i
showSProjType (SNamed x) = "." ++ x

showAbsParameter :: (Name, Either Name Icit, Maybe Surface) -> String
showAbsParameter (x, Right Expl, Nothing) = x
showAbsParameter (x, Right Expl, Just t) = "(" ++ x ++ " : " ++ show t ++ ")"
showAbsParameter (x, Right Impl, Nothing) = "{" ++ x ++ "}"
showAbsParameter (x, Right Impl, Just t) = "{" ++ x ++ " : " ++ show t ++ "}"
showAbsParameter (x, Left y, Nothing) = "{" ++ x ++ " = " ++ y ++ "}"
showAbsParameter (x, Left y, Just t) = "{" ++ x ++ " : " ++ show t ++ " = " ++ y ++ "}"

showAppArgument :: (Surface, Either Name Icit) -> String
showAppArgument (a, Right Expl) = showS a
showAppArgument (a, Right Impl) = "{" ++ show a ++ "}"
showAppArgument (a, Left x) = "{" ++ x ++ " = " ++ show a ++ "}"

showLevel :: Surface -> String
showLevel top = go 0 top
  where
    go :: Int -> Surface -> String
    go n SL0 = show n
    go n (SLS a) = go (n + 1) a
    go _ _ = showS top

instance Show Surface where
  show (SVar x) = x
  show (SPrimElim x) = "elim " ++ x
  show (SU c) = "Type " ++ showLevel c
  show SLevel = "Level"
  show SL0 = "L0"
  show (SLS c) = "LS " ++ showLevel c
  show (SLMax a b) = "max " ++ showLevel a ++ " " ++ showLevel b
  show (SHole x) = "_" ++ fromMaybe "" x
  show s@SApp {} =
    let (f', as) = flattenApp s in
    showS f' ++ " " ++ unwords (map showAppArgument as)
  show s@SAbs {} =
    let (as, s') = flattenAbs s in
    "\\" ++ unwords (map showAbsParameter as) ++ ". " ++ show s'
  show s@SPi {} =
    let (as, s') = flattenPi s in
    showTelescope as s' " -> "
  show s@(SSigma x t b) =
    let (as, s') = flattenSigma s in
    showTelescope (map (\(x, t) -> (x, Expl, t)) as) s' " ** "
  show s@(SPair _ _) =
    let ps = flattenPair s in
    case last ps of
      SVar "[]" -> "[" ++ intercalate ", " (map show $ init ps) ++ "]"
      _ -> "(" ++ intercalate ", " (map show ps) ++ ")"      
  show s@(SProj _ _) = let (s', ps) = flattenProj s in showS s' ++ intercalate "" (map showSProjType ps)
  show (SLet x Nothing v b) = "let " ++ x ++ " = " ++ show v ++ "; " ++ show b
  show (SLet x (Just t) v b) = "let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b
  show (SPos _ s) = show s
  show (SLift s) = "Lift " ++ showS s
  show (SLiftTerm s) = "lift " ++ showS s
  show (SLower s) = "lower " ++ showS s
  show SRefl = "Refl"

instance IsString Surface where
  fromString x = SVar x

-- only used for pretty printing
fromCore :: [Name] -> Core -> Surface
fromCore ns (Var i) = SVar (ns !! i)
fromCore ns (Global x) = SVar x
fromCore ns (Prim x) = SVar (show x)
fromCore ns (PrimElim x) = SPrimElim (show x)
fromCore ns (App f a i) = SApp (fromCore ns f) (fromCore ns a) (Right i)
fromCore ns (Abs x i b) = SAbs x (Right i) Nothing (fromCore (x : ns) b)
fromCore ns (Pi x i t _ b _) = SPi x i (fromCore ns t) (fromCore (x : ns) b)
fromCore ns (Sigma x t _ b _) = SSigma x (fromCore ns t) (fromCore (x : ns) b)
fromCore ns (Pair a b) = SPair (fromCore ns a) (fromCore ns b)
fromCore ns (Proj s p) = SProj (fromCore ns s) (go p)
  where
    go Fst = SFst
    go Snd = SSnd
    go (PNamed (Just x) _) = SNamed x
    go (PNamed Nothing i) = SIndex i
fromCore ns (U (Fin l)) = SU (fromCore ns l)
fromCore ns (U Omega) = SVar "Type omega"
fromCore ns ULevel = SLevel
fromCore ns L0 = SL0
fromCore ns (LS a) = SLS (fromCore ns a)
fromCore ns (LMax a b) = SLMax (fromCore ns a) (fromCore ns b)
fromCore ns (Let x t v b) = SLet x (Just $ fromCore ns t) (fromCore ns v) (fromCore (x : ns) b)
fromCore ns (Lift t) = SLift (fromCore ns t)
fromCore ns (LiftTerm t) = SLiftTerm (fromCore ns t)
fromCore ns (Lower t) = SLower (fromCore ns t)
fromCore _ Refl = SRefl
fromCore _ (Meta x) = SVar ("?" ++ show x)
fromCore ns (AppPruning t _) = SApp (fromCore ns t) (SVar "*") (Right Expl)

data Def
  = Def Name (Maybe Surface) Surface -- name type term
  | Import String -- filename

instance Show Def where
  show (Def x (Just ty) tm) = x ++ " : " ++ show ty ++ " = " ++ show tm
  show (Def x Nothing tm) = x ++ " = " ++ show tm
  show (Import x) = "import " ++ x

type Defs = [Def]

showDefs :: Defs -> String
showDefs [] = ""
showDefs (hd : tl) = show hd ++ "\n" ++ showDefs tl

defNames :: Defs -> [String]
defNames [] = []
defNames (Def x _ _ : t) = x : defNames t
defNames (_ : t) = defNames t

countNames :: Defs -> Int
countNames = length . defNames

imports :: Defs -> [String]
imports [] = []
imports (Import x : t) = x : imports t
imports (_ : t) = imports t
