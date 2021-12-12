module Common where

import Data.Coerce (coerce)

newtype MetaVar = MetaVar { unMetaVar :: Int } deriving (Eq, Show, Num, Ord) via Int
newtype LMetaVar = LMetaVar { unLMetaVar :: Int } deriving (Eq, Show, Num, Ord) via Int
newtype Ix = Ix Int deriving (Eq, Show, Ord, Num) via Int
newtype Lvl = Lvl Int deriving (Eq, Show, Ord, Num) via Int

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx l x = coerce (l - x - 1)

type Name = String

data Icit = Impl | Expl deriving (Show, Eq)

icit :: Icit -> a -> a -> a
icit Impl a _ = a
icit Expl _ b = b

onlyIf :: Bool -> IO () -> IO ()
onlyIf True action = action
onlyIf False _ = return ()

doDebug :: Bool
doDebug = True

debug :: String -> IO ()
debug = if doDebug then putStrLn else (\_ -> return ())
