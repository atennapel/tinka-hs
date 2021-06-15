module Surface (Surface(..), fromCore) where

import GHC.Exts(IsString(..))
import Data.List (intercalate)
import Text.Megaparsec (SourcePos)

import Common
import Core

data Surface
  = SVar Name
  | SApp Surface Surface
  | SAbs Name (Maybe Surface) Surface
  | SPi Name Surface Surface
  | SSigma Name Surface Surface
  | SPair Surface Surface
  | SProj Surface ProjType
  | SU
  | SLet Name (Maybe Surface) Surface Surface
  | SPos SourcePos Surface
  | SHole

isSimple :: Surface -> Bool
isSimple (SVar _) = True
isSimple SU = True
isSimple SHole = True
isSimple (SPair _ _) = True
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

flattenAbs :: Surface -> ([(Name, Maybe Surface)], Surface)
flattenAbs (SAbs x t b) = let (as, s') = flattenAbs b in ((x, t) : as, s')
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

showAbsBinder :: (Name, Maybe Surface) -> String
showAbsBinder (x, Nothing) = x
showAbsBinder (x, Just t) = "(" ++ x ++ " : " ++ show t ++ ")"

showPiBinder :: (Name, Surface) -> String
showPiBinder ("_", s@(SApp _ _)) = show s
showPiBinder ("_", SPos _ s@(SApp _ _)) = show s
showPiBinder ("_", s) = showS s
showPiBinder (x, s) = "(" ++ x ++ " : " ++ show s ++ ")"

showProjType :: ProjType -> String
showProjType Fst = ".1"
showProjType Snd = ".2"

instance Show Surface where
  show (SVar x) = x
  show SU = "U"
  show SHole = "_"
  show s@(SApp f a) =
    let (f', as) = flattenApp s in
    showS f' ++ " " ++ unwords (map showS as)
  show s@(SAbs x t b) =
    let (as, s') = flattenAbs s in
    "\\" ++ unwords (map showAbsBinder as) ++ ". " ++ show s'
  show s@(SPi x t b) =
    let (as, s') = flattenPi s in
    intercalate " -> " (map showPiBinder as) ++ " -> " ++ show s'
  show s@(SSigma x t b) =
    let (as, s') = flattenSigma s in
    intercalate " ** " (map showPiBinder as) ++ " ** " ++ show s'
  show s@(SPair _ _) = "(" ++ intercalate ", " (map show $ flattenPair s) ++ ")"
  show s@(SProj _ _) = let (s', ps) = flattenProj s in showS s' ++ intercalate "" (map showProjType ps)
  show (SLet x Nothing v b) = "let " ++ x ++ " = " ++ show v ++ "; " ++ show b
  show (SLet x (Just t) v b) = "let " ++ x ++ " : " ++ show t ++ " = " ++ show v ++ "; " ++ show b
  show (SPos _ s) = show s

instance IsString Surface where
  fromString = SVar

fromCore :: [Name] -> Core -> Surface
fromCore ns (Var i) = SVar (ns !! i)
fromCore ns (App f a) = SApp (fromCore ns f) (fromCore ns a)
fromCore ns (Abs x t b) = SAbs x (Just $ fromCore ns t) (fromCore (x : ns) b)
fromCore ns (Pi x t b) = SPi x (fromCore ns t) (fromCore (x : ns) b)
fromCore ns (Sigma x t b) = SSigma x (fromCore ns t) (fromCore (x : ns) b)
fromCore ns (Pair a b _) = SPair (fromCore ns a) (fromCore ns b) -- TODO: use type or not?
fromCore ns (Proj s p) = SProj (fromCore ns s) p 
fromCore ns U = SU
fromCore ns (Let x t v b) = SLet x (Just $ fromCore ns t) (fromCore ns v) (fromCore (x : ns) b)
