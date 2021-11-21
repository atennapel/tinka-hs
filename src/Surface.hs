module Surface (Surface(..), fromCore, Def(..), Defs, showDefs, defNames, countNames, imports) where

import GHC.Exts(IsString(..))
import Data.List (intercalate)
import Text.Megaparsec (SourcePos)

import Common
import Core

data Surface
  = SVar Name ULvl
  | SPrimElim Name ULvl ULvl
  | SApp Surface Surface
  | SAbs Name Surface
  | SPi Name Surface Surface
  | SSigma Name Surface Surface
  | SPair Surface Surface
  | SProj Surface ProjType
  | SU ULvl
  | SLet Name (Maybe Surface) Surface Surface
  | SPos SourcePos Surface
  | SHole
  | SLift Surface
  | SLiftTerm Surface
  | SLower Surface
  | SCon Surface
  | SRefl

isSimple :: Surface -> Bool
isSimple (SVar _ _) = True
isSimple (SU _) = True
isSimple SHole = True
isSimple (SPair _ _) = True
isSimple SRefl = True
isSimple (SPos _ s) = isSimple s
isSimple _ = False

showS :: Surface -> String
showS s = if isSimple s then show s else "(" ++ show s ++ ")"

flattenApp :: Surface -> (Surface, [Surface])
flattenApp s = go s []
  where
    go (SApp f a) as = go f (a : as)
    go (SPos _ s) as = go s as
    go s as = (s, as)

flattenAbs :: Surface -> ([Name], Surface)
flattenAbs (SAbs x b) = let (as, s') = flattenAbs b in (x : as, s')
flattenAbs (SPos _ s) = flattenAbs s
flattenAbs s = ([], s)

flattenPi :: Surface -> ([(Name, Surface)], Surface)
flattenPi (SPi x t b) = let (as, s') = flattenPi b in ((x, t) : as, s')
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

flattenProj :: Surface -> (Surface, [ProjType])
flattenProj s = go s []
  where
    go (SProj b p) ps = go b (p : ps)
    go (SPos _ s) ps = go s ps
    go s ps = (s, ps)

showTelescope :: [(Name, Surface)] -> Surface -> String -> String
showTelescope ps rt delim = go ps
  where
    go [] = show rt
    go (("_", s@(SApp _ _)) : tl) = show s ++ delim ++ go tl
    go (("_", SPos _ s@(SApp _ _)) : tl) = show s ++ delim ++ go tl
    go (("_", s) : tl) = showS s ++ delim ++ go tl
    go ((x, s) : tl) = "(" ++ x ++ " : " ++ show s ++ ")" ++ delim ++ go tl

showProjType :: ProjType -> String
showProjType Fst = ".1"
showProjType Snd = ".2"

instance Show Surface where
  show (SVar x 0) = x
  show (SVar x 1) = x ++ "^"
  show (SVar x l) = x ++ "^" ++ show l
  show (SPrimElim x 0 k) = "elim " ++ x ++ (if k == 0 then "" else " " ++ show k)
  show (SPrimElim x 1 k) = "elim " ++ x ++ "^" ++ (if k == 0 then "" else " " ++ show k)
  show (SPrimElim x l k) = "elim " ++ x ++ "^" ++ show l ++ (if k == 0 then "" else " " ++ show k)
  show (SU 0) = "Type"
  show (SU l) = "Type" ++ show l
  show SHole = "_"
  show s@(SApp f a) =
    let (f', as) = flattenApp s in
    showS f' ++ " " ++ unwords (map showS as)
  show s@(SAbs x b) =
    let (as, s') = flattenAbs s in
    "\\" ++ unwords as ++ ". " ++ show s'
  show s@(SPi x t b) =
    let (as, s') = flattenPi s in
    showTelescope as s' " -> "
  show s@(SSigma x t b) =
    let (as, s') = flattenSigma s in
    showTelescope as s' " ** "
  show s@(SPair _ _) = "(" ++ intercalate ", " (map show $ flattenPair s) ++ ")"
  show s@(SProj _ _) = let (s', ps) = flattenProj s in showS s' ++ intercalate "" (map showProjType ps)
  show (SLet x Nothing v b) = "let " ++ x ++ " = " ++ show v ++ "; " ++ show b
  show (SLet x (Just t) v b) = "let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b
  show (SPos _ s) = show s
  show (SLift s) = "Lift " ++ showS s
  show (SLiftTerm s) = "lift " ++ showS s
  show (SLower s) = "lower " ++ showS s
  show (SCon s) = "Con " ++ showS s
  show SRefl = "Refl"

instance IsString Surface where
  fromString x = SVar x 0

-- only used for pretty printing
fromCore :: [Name] -> Core -> Surface
fromCore ns (Var i) = SVar (ns !! i) 0
fromCore ns (Global x l) = SVar x l
fromCore ns (Prim x l) = SVar (show x) l
fromCore ns (PrimElim x l k) = SPrimElim (show x) l k
fromCore ns (App f a) = SApp (fromCore ns f) (fromCore ns a)
fromCore ns (Abs x b) = SAbs x (fromCore (x : ns) b)
fromCore ns (Pi x t b) = SPi x (fromCore ns t) (fromCore (x : ns) b)
fromCore ns (Sigma x t b) = SSigma x (fromCore ns t) (fromCore (x : ns) b)
fromCore ns (Pair a b) = SPair (fromCore ns a) (fromCore ns b)
fromCore ns (Proj s p) = SProj (fromCore ns s) p 
fromCore ns (U l) = SU l
fromCore ns (Let x t v b) = SLet x (Just $ fromCore ns t) (fromCore ns v) (fromCore (x : ns) b)
fromCore ns (Lift t) = SLift (fromCore ns t)
fromCore ns (LiftTerm t) = SLiftTerm (fromCore ns t)
fromCore ns (Lower t) = SLower (fromCore ns t)
fromCore ns (Con t) = SCon (fromCore ns t)
fromCore _ Refl = SRefl
fromCore _ (Meta x) = SVar ("?" ++ show x) 0
fromCore _ (InsertedMeta x _) = SVar ("?*" ++ show x) 0

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
