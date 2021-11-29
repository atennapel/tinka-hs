module Main where

import System.Environment
import Text.Megaparsec (initialPos)
import System.IO
import GHC.IO.Encoding
import Data.List (isPrefixOf)
import Control.Exception (catch, SomeException)

import Common
import Surface
import Ctx
import Elaboration
import Parser
import Core
import Evaluation
import Globals
import ModuleElaboration

main :: IO ()
main = do
  setLocaleEncoding utf8
  mainWith getArgs parseStdin

mainWith :: IO [String] -> IO (Surface, String) -> IO ()
mainWith getOpt getSurface = do
  getOpt >>= \case
    ["parse"] -> do
      (t, file) <- getSurface
      print t
    ["nf"] -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty $ nfWith Full c
    ["type"] -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty ty
    ["elab"] -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty c
    ["parse-defs"] -> do
      (t, file) <- parseStdinDefs
      print t
    ["elab-defs"] -> try $ do
      elabDefs parseStdinDefs
      gs <- getGlobals
      putStrLn $ showElabDefs gs
      case getGlobal "main" of
        Just e ->
          putStrLn $ showC empty (nfWith Full (gcore e))
        Nothing -> return ()
    ["repl"] -> do
      putStrLn "tinka repl"
      repl
    _ -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty ty
      putStrLn $ showC empty c
      putStrLn $ showC empty $ nfWith Full c

repl :: IO ()
repl = do
  putStr "> "
  hFlush stdout
  inp <- getLine
  case inp of
    defs | ":let " `isPrefixOf` defs || ":import " `isPrefixOf` defs -> try $ do
      let prefixN = if ":let " `isPrefixOf` defs then 5 else 1
      ds <- parseStrDefsIO (drop prefixN defs)
      let xs = imports ds
      ids <- loadModules xs
      nds <- elaborateDefs Nothing ds
      gs <- getGlobals
      putStrLn $ showElabDefs $ take (countNames nds + countNames ids) gs
    ":globals" -> do
      gs <- getGlobals
      putStrLn $ showElabDefs gs
    ":resetglobals" -> do
      resetGlobals
      putStrLn "done"
    ":modules" -> do
      ms <- getModules
      print ms
    ":resetmodules" -> do
      resetModules 
      putStrLn "done"
    inp -> try $ do
      (c, ty) <- parseAndElabSurface "(repl)" inp
      putStrLn $ showC empty ty
      putStrLn $ showC empty c
      putStrLn $ showC empty $ nfWith Full c
  repl

tryIO :: IO t -> (t -> IO ()) -> IO ()
tryIO a k = do
  res <- catch (Right <$> a) $ \(e :: SomeException) -> return $ Left (show e)
  case res of
    Left msg -> putStrLn msg
    Right x -> k x

try :: IO () -> IO ()
try a = tryIO a $ \_ -> return ()

elabSurface :: String -> Surface -> IO (Core, Core)
elabSurface file t = do
  (tm, ty, _) <- elaborate (enter (initialPos file) empty) t
  return (tm, ty)

parseAndElabSurface :: String -> String -> IO (Core, Core)
parseAndElabSurface file src = do
  t <- parseStrIO src
  elabSurface file t

elab :: IO (Surface, String) -> IO (Core, Core)
elab getSurface = do
  (t, file) <- getSurface
  elabSurface file t

elabDefs :: IO (Defs, String) -> IO ()
elabDefs getDefs = do
  (ds, file) <- getDefs
  let xs = imports ds
  ids <- loadModules xs
  elaborateDefs Nothing ds
  return ()

reduceGlobalLet :: Name -> Core -> Core
reduceGlobalLet x (Let y _ v (Var 0)) | x == y = v
reduceGlobalLet _ t = t

showElabDef :: GlobalEntry -> String
showElabDef (GlobalEntry x etm ety _ _ _ file) =
  maybe "" (++ ".") file ++ x ++ " : " ++ showC empty ety ++ " = " ++ showC empty (reduceGlobalLet x etm)

showElabDefs :: GlobalCtx -> String
showElabDefs [] = ""
showElabDefs (hd : tl) =
  case showElabDefs tl of
    "" -> showElabDef hd
    prefix -> prefix ++ "\n" ++ showElabDef hd
