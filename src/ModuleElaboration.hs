module ModuleElaboration (loadModules, loadModule) where

import Globals
import Surface
import TC
import Elaboration

import Control.Monad (foldM)
import qualified Data.Map as Map

throwTC :: TC t -> IO t
throwTC (Left msg) = error msg
throwTC (Right x) = return x

elaborateModuleEntry :: ModuleEntry -> IO Defs
elaborateModuleEntry (ModuleEntry x _ ds) = do
  res <- elaborateDefs ds
  throwTC res

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
    Left ms -> error $ "module cycle: " ++ show ms
    Right xs -> do
      let order = filter (`elem` new) xs
      elaborateModules order

loadModule :: String -> IO Defs
loadModule x = loadModules [x]
