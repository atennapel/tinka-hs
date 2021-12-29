module Common where

import Data.Coerce (coerce)
import Data.Char (isAlpha, isDigit)
import System.IO.Unsafe
import Data.IORef

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

doDebug :: IORef Bool
doDebug = unsafeDupablePerformIO $ newIORef False
{-# noinline doDebug #-}

getDebug :: IO Bool
getDebug = readIORef doDebug

setDebug :: Bool -> IO ()
setDebug b = writeIORef doDebug b

debug :: String -> IO ()
debug x = if unsafeDupablePerformIO (readIORef doDebug) then putStrLn x else return ()

showName :: Name -> String
showName x@"()" = x
showName x@"[]" = x
showName x | length x > 0 && head x == '_' = x
showName x | length x > 1 && head x == '?' && all isDigit (tail x) = x
showName x | length x > 2 && head x == '?' && head (tail x) == '*' && all isDigit (tail (tail x)) = x
showName x | length x > 0 && not (isAlpha (head x)) = "(" ++ x ++ ")"
showName x = x

nextName :: Name -> Name
nextName "_" = "_"
nextName x = x ++ "'"

chooseName :: Name -> [Name] -> Name
chooseName "_" _ = "_"
chooseName x ns | elem x ns = chooseName (nextName x) ns
chooseName x _ = x
