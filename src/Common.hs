module Common where

import Control.Exception (catch, SomeException)

type Name = String
type Ix = Int
type Lvl = Int
type ULvl = Int

data ProjType = Fst | Snd
  deriving (Eq)

newtype MetaVar = MetaVar { unMetaVar :: Int } deriving (Eq, Show, Num, Ord) via Int

test :: Bool -> String -> IO ()
test False msg = error msg
test True _ = return ()

testIO :: IO a -> (SomeException -> String) -> IO a
testIO a msg = catch a (error . msg)

data Icit = Impl | Expl deriving (Show, Eq)

icit :: Icit -> a -> a -> a
icit Impl a _ = a
icit Expl _ b = b

type Pruning = [Maybe Icit]
newtype RevPruning = RevPruning Pruning

revPruning :: Pruning -> RevPruning
revPruning = RevPruning . reverse
