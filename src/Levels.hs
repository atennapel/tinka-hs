module Levels where

import qualified Data.IntMap as M
import Data.Coerce

import Common

data FinLevel
  = FLVar Ix
  | FLZ
  | FLS FinLevel
  | FLMax FinLevel FinLevel
  | FLMeta LMetaVar
  deriving (Eq)

showFinLevelS :: FinLevel -> String
showFinLevelS l@FLZ = show l
showFinLevelS l@(FLVar _) = show l
showFinLevelS l@(FLMeta _) = show l
showFinLevelS l = "(" ++ show l ++ ")"

instance Show FinLevel where
  show (FLVar i) = "'" ++ show i
  show FLZ = "Z"
  show (FLS l) = "S " ++ showFinLevelS l
  show (FLMax a b) = "max " ++ showFinLevelS a ++ " " ++ showFinLevelS b
  show (FLMeta m) = "?l" ++ show m

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

data VFinLevel = VFL Int (M.IntMap Int) (M.IntMap Int)
  deriving (Eq, Show)

data VLevel = VOmega | VOmega1 | VFinLevel {-# unpack #-} VFinLevel
  deriving (Eq, Show)

instance Semigroup VFinLevel where
  VFL n xs ys <> VFL n' xs' ys' = VFL (max n n') (M.unionWith max xs xs') (M.unionWith max ys ys')

instance Monoid VFinLevel where
  mempty = VFL 0 mempty mempty

instance Semigroup VLevel where
  VFinLevel i <> VFinLevel j = VFinLevel (i <> j)
  VOmega1 <> _ = VOmega1
  _ <> VOmega1 = VOmega1
  _ <> _ = VOmega

instance Monoid VLevel where
  mempty = VFinLevel mempty

isVFinLevelZero :: VFinLevel -> Bool
isVFinLevelZero l = l == mempty

vFinLevelVar :: Lvl -> VFinLevel
vFinLevelVar x = VFL 0 (M.singleton (coerce x) 0) mempty

vFinMeta :: LMetaVar -> VFinLevel
vFinMeta m = VFL 0 mempty (M.singleton (coerce m) 0)

addToVFinLevel :: Int -> VFinLevel -> VFinLevel
addToVFinLevel n (VFL m xs ms) = VFL (n + m) ((+ n) <$> xs) ((+ n) <$> ms)

-- partial
subVFinLevel :: Int -> VFinLevel -> VFinLevel
subVFinLevel n (VFL m xs ys) = VFL (goN n m) (subMap n xs) (subMap n ys)
  where
    goN n m | m == 0 = 0
    goN n m | m >= n = m - n
    goN _ _ = error "subVFinLevel subtracted too much!"

    subMap n xs = M.map (goMap n) xs

    goMap n x | x >= n = x - n
    goMap n x = error "subVFinLevel subtracted too much!"

addToFinLevel :: Int -> FinLevel -> FinLevel
addToFinLevel n i = go n i
  where
    go 0 i = i
    go n i = go (n - 1) (FLS i)

vFLZ :: VLevel
vFLZ = VFinLevel mempty

vFLS :: VFinLevel -> VFinLevel
vFLS = addToVFinLevel 1

vLS :: VLevel -> VLevel
vLS VOmega1 = error "cannot increment omega1"
vLS VOmega = VOmega1
vLS (VFinLevel l) = VFinLevel (vFLS l)
