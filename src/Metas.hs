module Metas where

import Val
import Common
import Core

import System.IO.Unsafe
import Data.IORef
import qualified Data.IntMap as IM
import qualified Data.Set as S
import Data.Set (Set)
import Data.Bifunctor (first, second)

data MetaEntry = Solved (Set MetaVar) Core Val | Unsolved

type MetaMap = IM.IntMap MetaEntry

nextMeta :: IORef Int
nextMeta = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextMeta #-}

mcxt :: IORef MetaMap
mcxt = unsafeDupablePerformIO $ newIORef mempty
{-# noinline mcxt #-}

lookupMeta :: MetaVar -> MetaEntry
lookupMeta (MetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e  -> pure e
    Nothing -> error "impossible"

reset :: IO ()
reset = do
  writeIORef nextMeta 0
  writeIORef mcxt mempty

metadeps :: MetaEntry -> Set MetaVar
metadeps (Solved deps _ _) = deps
metadeps Unsolved = S.empty

removeDep :: MetaVar -> MetaEntry -> MetaEntry
removeDep y (Solved deps core sol) = Solved (y `S.delete` deps) core sol
removeDep _ e = e

allNoDeps :: MetaMap -> [(MetaVar, MetaEntry)]
allNoDeps m = map (first MetaVar) $ filter (S.null . metadeps . snd) $ IM.assocs m

allDependents :: MetaMap -> MetaVar -> [(MetaVar, MetaEntry)]
allDependents m x = map (first MetaVar) $ filter (elem x . metadeps . snd) $ IM.assocs m

toposortMetas :: MetaMap -> Either [MetaVar] [MetaVar]
toposortMetas m = reverse <$> go m [] (allNoDeps m)
  where
    go :: MetaMap -> [MetaVar] -> [(MetaVar, MetaEntry)] -> Either [MetaVar] [MetaVar]
    go m l [] | not (all (null . metadeps) $ IM.elems m) =
      Left $ map (MetaVar . fst) $ filter (\(_, v) -> not (null $ metadeps v)) $ IM.assocs m
    go m l [] = return l
    go m l ((x, e) : s) =
      let dependents = map (second $ removeDep x) $ allDependents m x in
      let m' = foldr (\(x, e) m -> IM.insert (unMetaVar x) e m) m dependents in
      go m' (x : l) (s ++ filter (null . metadeps . snd) dependents)

orderMetas :: IO [MetaVar]
orderMetas = do
  ms <- readIORef mcxt
  case toposortMetas ms of
    Left cycle -> error $ "cycle in metas: " ++ show cycle
    Right order -> return order
