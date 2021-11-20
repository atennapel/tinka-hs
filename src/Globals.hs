module Globals where

import Core
import Val
import Common
import Parser
import Surface

import Data.IORef
import GHC.IO.Unsafe (unsafeDupablePerformIO)
import Data.List (isSuffixOf, delete)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (foldM)

-- import Debug.Trace (trace)

data GlobalEntry = GlobalEntry {
  gname :: Name,
  gcore :: Core,
  gtype :: Core,
  gval :: Val,
  gvtype :: Val,
  gmodule :: Maybe String
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

-- modules
handleFilename :: String -> String
handleFilename s = if ".tinka" `isSuffixOf` s then s else s ++ ".tinka"

normalizeModuleName :: String -> String
normalizeModuleName s = if ".tinka" `isSuffixOf` s then take (length s - 6) s else s

data ModuleEntry = ModuleEntry {
  mname :: String,
  mdeps :: [String],
  mdefs :: Defs
}

removeDep :: String -> ModuleEntry -> ModuleEntry
removeDep y (ModuleEntry x deps ds) = ModuleEntry x (y `delete` deps) ds

instance Show ModuleEntry where
  show (ModuleEntry x deps ds) = "(" ++ show deps ++ ", " ++ show (defNames ds) ++ ")"

type ModuleMap = Map String ModuleEntry

allNoDeps :: ModuleMap -> [ModuleEntry]
allNoDeps m = filter (null . mdeps) $ Map.elems m

allDependents :: ModuleMap -> String -> [ModuleEntry]
allDependents m x = filter (elem x . mdeps) $ Map.elems m

eitherToIO :: Either String a -> IO a
eitherToIO (Left msg) = error msg
eitherToIO (Right x) = return x

depsFromDefs :: Defs -> [String]
depsFromDefs [] = []
depsFromDefs (Import x : t) = normalizeModuleName x : depsFromDefs t
depsFromDefs (_ : t) = depsFromDefs t

fetchModule :: String -> IO ModuleEntry
fetchModule s = do
  inp <- readFile (handleFilename s)
  let name = normalizeModuleName s
  ds <- eitherToIO $ parseStrDefsEither inp
  return $ ModuleEntry name (depsFromDefs ds) ds

fetchModules :: String -> ModuleMap -> IO ([String], ModuleMap)
fetchModules s m = do
  let name = normalizeModuleName s
  case m Map.!? name of
    Just _ -> return ([], m)
    Nothing -> do
      e <- fetchModule name
      let newmap = Map.insert name e m
      foldM go ([name], newmap) (mdeps e)
  where
    go (xs, m) x = do
      (xs', m') <- fetchModules x m
      return (xs ++ xs', m')

fetchModulesAll :: [String] -> ModuleMap -> IO ([String], ModuleMap)
fetchModulesAll ss m = foldM go ([], m) ss
  where
    go (xs, m) x = do
      (xs', m') <- fetchModules x m
      return (xs ++ xs', m')

toposort :: ModuleMap -> Either [String] [String]
toposort m = reverse <$> go m [] (allNoDeps m)
  where
    go :: ModuleMap -> [String] -> [ModuleEntry] -> Either [String] [String]
    go m l [] | not (all (null . mdeps) $ Map.elems m) =
      Left $ map fst $ filter (\(_, v) -> not (null $ mdeps v)) $ Map.assocs m
    go m l [] = return l
    go m l (n : s) =
      let x = mname n in
      let dependents = map (removeDep x) $ allDependents m x in
      let m' = foldr (\e m -> Map.insert (mname e) e m) m dependents in
      go m' (x : l) (s ++ filter (null . mdeps) dependents)

-- module cache
modules :: IORef ModuleMap
modules = unsafeDupablePerformIO $ newIORef Map.empty
{-# noinline modules #-}

getModules :: IO ModuleMap
getModules = readIORef modules

resetModules :: IO ()
resetModules = writeIORef modules Map.empty

fetchModulesIO :: [String] -> IO [String]
fetchModulesIO xs = do
  ms <- getModules
  (xs, ms') <- fetchModulesAll xs ms
  writeIORef modules ms'
  return xs
