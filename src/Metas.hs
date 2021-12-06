module Metas where

import System.IO.Unsafe
import Data.IORef
import qualified Data.IntMap as IM

import Common
import Core
import Val

data MetaEntry = Solved Val Tm | Unsolved

type MetaMap = IM.IntMap MetaEntry

nextMeta :: IORef Int
nextMeta = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextMeta #-}

mctx :: IORef MetaMap
mctx = unsafeDupablePerformIO $ newIORef mempty
{-# noinline mctx #-}

getMetas :: IO MetaMap
getMetas = readIORef mctx

isSolved :: MetaEntry -> Bool
isSolved (Solved {}) = True
isSolved _ = False

allSolved :: IO Bool
allSolved = do
  ms <- getMetas
  return $ all isSolved $ IM.elems ms

writeMeta :: MetaVar -> MetaEntry -> IO ()
writeMeta (MetaVar m) e = modifyIORef mctx $ IM.insert m e

solveMeta :: MetaVar -> Val -> Tm -> IO ()
solveMeta m v c = writeMeta m (Solved v c)

newMeta :: IO MetaVar
newMeta = do
  m <- readIORef nextMeta
  writeIORef nextMeta $! m + 1
  modifyIORef mctx $ IM.insert m Unsolved
  return $ MetaVar m

lookupMeta :: MetaVar -> MetaEntry
lookupMeta (MetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef mctx
  case IM.lookup m ms of
    Just e  -> pure e
    Nothing -> error "impossible"

resetMetas :: IO ()
resetMetas = do
  writeIORef nextMeta 0
  writeIORef mctx mempty
