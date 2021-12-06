module Levels where

import qualified Data.IntMap as M
import Data.Coerce

import Common

data FinLevel
  = FLVar Ix
  | FLZ
  | FLS FinLevel
  | FLMax FinLevel FinLevel
  deriving (Eq)

showFinLevelS :: FinLevel -> String
showFinLevelS l@FLZ = show l
showFinLevelS l@(FLVar _) = show l
showFinLevelS l = "(" ++ show l ++ ")"

instance Show FinLevel where
  show (FLVar i) = "'" ++ show i
  show FLZ = "Z"
  show (FLS l) = "S " ++ showFinLevelS l
  show (FLMax a b) = "max " ++ showFinLevelS a ++ " " ++ showFinLevelS b

flmax :: FinLevel -> FinLevel -> FinLevel
flmax FLZ x = x
flmax x FLZ = x
flmax (FLS x) (FLS y) = FLS (flmax x y)
flmax x y = FLMax x y

data Level = Omega | Omega1 | FinLevel FinLevel
  deriving (Eq)

showLevelS :: Level -> String
showLevelS l@Omega = show l
showLevelS l@Omega1 = show l
showLevelS (FinLevel l) = showFinLevelS l

instance Show Level where
  show Omega = "omega"
  show Omega1 = "omega1"
  show (FinLevel l) = show l

data VFinLevel = VFL Int (M.IntMap Int)
  deriving (Eq, Show)

data VLevel = VOmega | VOmega1 | VFinLevel {-# unpack #-} VFinLevel
  deriving (Eq, Show)

instance Semigroup VFinLevel where
  VFL n xs <> VFL n' xs' = VFL (max n n') (M.unionWith max xs xs')

instance Monoid VFinLevel where
  mempty = VFL 0 mempty

instance Semigroup VLevel where
  VFinLevel i <> VFinLevel j = VFinLevel (i <> j)
  VOmega1 <> _ = VOmega1
  _ <> VOmega1 = VOmega1
  _ <> _ = VOmega

instance Monoid VLevel where
  mempty = VFinLevel mempty

vFinLevelVar :: Lvl -> VFinLevel
vFinLevelVar x = VFL 0 (M.singleton (coerce x) 0)

addToVFinLevel :: Int -> VFinLevel -> VFinLevel
addToVFinLevel n (VFL m xs) = VFL (n + m) ((+ n) <$> xs)

addToFinLevel :: Int -> FinLevel -> FinLevel
addToFinLevel n i = go n i
  where
    go 0 i = i
    go n i = go (n - 1) (FLS i)

vFLZ :: VLevel
vFLZ = VFinLevel mempty

vFLS :: VFinLevel -> VFinLevel
vFLS = addToVFinLevel 1
