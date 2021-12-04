module Common where

import Data.Coerce (coerce)

newtype Ix = Ix Int deriving (Eq, Show, Ord, Num) via Int
newtype Lvl = Lvl Int deriving (Eq, Show, Ord, Num) via Int

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx l x = coerce (l - x - 1)

type Name = String
