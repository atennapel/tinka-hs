module Globals where

import Data.IORef
import GHC.IO.Unsafe (unsafeDupablePerformIO)

import Common
import Val
import Core
import Levels

data GlobalEntry = GlobalEntry {
  gName :: Name,
  gTy :: VTy,
  gUniv :: VLevel,
  gVal :: Val,
  gCoreTy :: Ty,
  gCoreUniv :: Level,
  gCoreVal :: Tm,
  gInstance :: Bool,
  gModule :: Maybe String
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
    go (e : ts) | gName e == x = return e
    go (_ : ts) = go ts
