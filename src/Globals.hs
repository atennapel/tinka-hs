module Globals where

import Common
import Core
import Val

import Data.IORef
import GHC.IO.Unsafe (unsafeDupablePerformIO)
import Data.List (isSuffixOf)

data GlobalEntry = GlobalEntry {
  gname :: Name,
  gcore :: Core,
  gtype :: Core,
  gval :: Val,
  gvtype :: Val
}

type GlobalCtx = [GlobalEntry]

globals :: IORef GlobalCtx
globals = unsafeDupablePerformIO $ newIORef []
{-# noinline globals #-}

getGlobals :: IO GlobalCtx
getGlobals = readIORef globals

addGlobal :: GlobalEntry -> IO ()
addGlobal e = modifyIORef globals (e :)

resetGlobals :: IO ()
resetGlobals = writeIORef globals []

getGlobal :: Name -> Maybe GlobalEntry
getGlobal x = unsafeDupablePerformIO $ go <$> getGlobals
  where
    go [] = Nothing
    go (e : ts) | gname e == x = return e
    go (_ : ts) = go ts

handleFilename :: String -> String
handleFilename s = if ".tinka" `isSuffixOf` s then s else s ++ ".tinka"
