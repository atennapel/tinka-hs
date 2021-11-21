module Common where

type Name = String
type Ix = Int
type Lvl = Int
type ULvl = Int

data ProjType = Fst | Snd
  deriving (Eq)

newtype MetaVar = MetaVar { unMetaVar :: Int } deriving (Eq, Show, Num) via Int
