module Surface (Surface(..), fromCore) where

import GHC.Exts( IsString(..) )
import Data.List (intercalate)
import Text.Megaparsec (SourcePos)

import Common
import Core

data Surface
  = SVar Name
  | SApp Surface Surface
  | SAbs Name (Maybe Surface) Surface
  | SPi Name Surface Surface
  | SU Ix
  | SLet Name (Maybe Surface) Surface Surface
  | SPos SourcePos Surface
  | SHole

isSimple :: Surface -> Bool
isSimple (SVar _) = True
isSimple (SU _) = True
isSimple SHole = True
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

showAbsBinder :: (Name, Maybe Surface) -> String
showAbsBinder (x, Nothing) = x
showAbsBinder (x, Just t) = "(" ++ x ++ " : " ++ show t ++ ")"

showPiBinder :: (Name, Surface) -> String
showPiBinder ("_", s@(SApp _ _)) = show s
showPiBinder ("_", SPos _ s@(SApp _ _)) = show s
showPiBinder ("_", s) = showS s
showPiBinder (x, s) = "(" ++ x ++ " : " ++ show s ++ ")"

instance Show Surface where
  show (SVar x) = x
  show (SU 0) = "U"
  show (SU i) = "U" ++ show i
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
fromCore ns (U i) = SU i
fromCore ns (Let x t v b) = SLet x (Just $ fromCore ns t) (fromCore ns v) (fromCore (x : ns) b)
