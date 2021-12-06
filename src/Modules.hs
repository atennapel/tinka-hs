module Modules where

import Data.IORef
import GHC.IO.Unsafe (unsafeDupablePerformIO)
import Data.Map (Map)
import qualified Data.Map as M
import Data.List (isSuffixOf, delete)

import Surface
import Parser
import Elaboration
import Control.Monad (foldM)

handleFilename :: String -> String
handleFilename s = if ".tinka" `isSuffixOf` s then s else s ++ ".tinka"

normalizeModuleName :: String -> String
normalizeModuleName s = if ".tinka" `isSuffixOf` s then take (length s - 6) s else s

data ModuleEntry = ModuleEntry {
  mname :: String,
  mdeps :: [String],
  mdefs :: Decls
}

removeDep :: String -> ModuleEntry -> ModuleEntry
removeDep y (ModuleEntry x deps ds) = ModuleEntry x (y `delete` deps) ds

instance Show ModuleEntry where
  show (ModuleEntry x deps ds) = "(" ++ show deps ++ ", " ++ show (declNames ds) ++ ")"

type ModuleMap = Map String ModuleEntry

allNoDeps :: ModuleMap -> [ModuleEntry]
allNoDeps m = filter (null . mdeps) $ M.elems m

allDependents :: ModuleMap -> String -> [ModuleEntry]
allDependents m x = filter (elem x . mdeps) $ M.elems m

eitherToIO :: Either String a -> IO a
eitherToIO (Left msg) = error msg
eitherToIO (Right x) = return x

depsFromDefs :: Decls -> [String]
depsFromDefs [] = []
depsFromDefs (Import x : t) = normalizeModuleName x : depsFromDefs t
depsFromDefs (_ : t) = depsFromDefs t

fetchModule :: String -> IO ModuleEntry
fetchModule s = do
  inp <- readFile (handleFilename s)
  let name = normalizeModuleName s
  ds <- parseStrDeclsIO inp
  return $ ModuleEntry name (depsFromDefs ds) ds

fetchModules :: String -> ModuleMap -> IO ([String], ModuleMap)
fetchModules s m = do
  let name = normalizeModuleName s
  case m M.!? name of
    Just _ -> return ([], m)
    Nothing -> do
      e <- fetchModule name
      let newmap = M.insert name e m
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
    go m l [] | not (all (null . mdeps) $ M.elems m) =
      Left $ map fst $ filter (\(_, v) -> not (null $ mdeps v)) $ M.assocs m
    go m l [] = return l
    go m l (n : s) =
      let x = mname n in
      let dependents = map (removeDep x) $ allDependents m x in
      let m' = foldr (\e m -> M.insert (mname e) e m) m dependents in
      go m' (x : l) (s ++ filter (null . mdeps) dependents)

-- module cache
modules :: IORef ModuleMap
modules = unsafeDupablePerformIO $ newIORef M.empty
{-# noinline modules #-}

getModules :: IO ModuleMap
getModules = readIORef modules

resetModules :: IO ()
resetModules = writeIORef modules M.empty

fetchModulesIO :: [String] -> IO [String]
fetchModulesIO xs = do
  ms <- getModules
  (xs, ms') <- fetchModulesAll xs ms
  writeIORef modules ms'
  return xs

-- elaboration
elaborateModuleEntry :: ModuleEntry -> IO Decls
elaborateModuleEntry (ModuleEntry x _ ds) = elaborateDecls (Just x) ds

elaborateModules :: [String] -> IO Decls
elaborateModules order = do
  ms <- getModules
  let entries = map (ms M.!) order
  foldM (\ds e -> (ds ++) <$> elaborateModuleEntry e) [] entries

-- entry point
loadModules :: [String] -> IO Decls
loadModules xs = do
  new <- fetchModulesIO xs
  ms <- getModules
  case toposort ms of
    Left ms -> error $ "module cycle: " ++ show ms
    Right xs -> do
      let order = filter (`elem` new) xs
      elaborateModules order

loadModule :: String -> IO Decls
loadModule x = loadModules [x]
