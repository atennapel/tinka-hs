module ModuleElaboration (loadModules, loadModule) where

import Globals
import Surface
import Elaboration

import Control.Monad (foldM)
import qualified Data.Map as Map
import Errors (throw)

elaborateModuleEntry :: ModuleEntry -> IO Defs
elaborateModuleEntry (ModuleEntry x _ ds) = elaborateDefs (Just x) ds

elaborateModules :: [String] -> IO Defs
elaborateModules order = do
  ms <- getModules
  let entries = map (ms Map.!) order
  foldM (\ds e -> (ds ++) <$> elaborateModuleEntry e) [] entries

-- entry point
loadModules :: [String] -> IO Defs
loadModules xs = do
  new <- fetchModulesIO xs
  ms <- getModules
  case toposort ms of
    Left ms -> throw $ "module cycle: " ++ show ms
    Right xs -> do
      let order = filter (`elem` new) xs
      elaborateModules order

loadModule :: String -> IO Defs
loadModule x = loadModules [x]
