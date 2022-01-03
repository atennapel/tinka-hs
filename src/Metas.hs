module Metas where

import System.IO.Unsafe
import Data.IORef
import qualified Data.IntMap as IM
import qualified Data.Set as S
import Data.Coerce (coerce)

import Common
import Core
import Val
import Levels

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

allUnsolved :: IO [MetaVar]
allUnsolved = do
  ms <- getMetas
  return $ map (coerce . fst) $ filter (\(k, v) -> not (isSolved v)) $ IM.assocs ms

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

-- level metas
data LMetaEntry = LSolved VFinLevel | LUnsolved Lvl (S.Set Lvl)

type LMetaMap = IM.IntMap LMetaEntry

nextLMeta :: IORef Int
nextLMeta = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextLMeta #-}

lmctx :: IORef LMetaMap
lmctx = unsafeDupablePerformIO $ newIORef mempty
{-# noinline lmctx #-}

getLMetas :: IO LMetaMap
getLMetas = readIORef lmctx

isLSolved :: LMetaEntry -> Bool
isLSolved (LSolved {}) = True
isLSolved _ = False

allLUnsolved :: IO [LMetaVar]
allLUnsolved = do
  ms <- getLMetas
  return $ map (coerce . fst) $ filter (\(k, v) -> not (isLSolved v)) $ IM.assocs ms

writeLMeta :: LMetaVar -> LMetaEntry -> IO ()
writeLMeta (LMetaVar m) e = modifyIORef lmctx $ IM.insert m e

solveLMeta :: LMetaVar -> VFinLevel -> IO ()
solveLMeta m v = writeLMeta m (LSolved v)

solveUnsolvedLMetas :: IO ()
solveUnsolvedLMetas = modifyIORef lmctx (IM.map solve)
  where
    solve s@(LSolved {}) = s
    solve (LUnsolved _ _) = LSolved mempty

newLMeta :: Lvl -> S.Set Lvl -> IO LMetaVar
newLMeta k scope = do
  m <- readIORef nextLMeta
  writeIORef nextLMeta $! m + 1
  modifyIORef lmctx $ IM.insert m (LUnsolved k scope)
  return $ LMetaVar m

lookupLMeta :: LMetaVar -> LMetaEntry
lookupLMeta (LMetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef lmctx
  case IM.lookup m ms of
    Just e  -> pure e
    Nothing -> error "impossible"

resetMetas :: IO ()
resetMetas = do
  writeIORef nextMeta 0
  writeIORef mctx mempty
  writeIORef nextLMeta 0
  writeIORef lmctx mempty
