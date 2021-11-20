module Main where

import System.Environment
import System.Exit
import Text.Megaparsec (initialPos)
import System.IO
import GHC.IO.Encoding
import Data.List (isPrefixOf)
import Data.Bifunctor (first)
import Control.Exception (try, SomeException)

import Surface
import Ctx
import Elaboration
import Verification
import Parser
import Core
import Evaluation
import Globals
import ModuleElaboration
import TC

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
    ["elab-defs"] -> do
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
    defs | ":let " `isPrefixOf` defs || ":import " `isPrefixOf` defs -> do
      let prefixN = if ":let " `isPrefixOf` defs then 5 else 1
      showError (parseStrDefsEither (drop prefixN defs)) $ \ds -> do
        let xs = imports ds
        tryIO (loadModules xs) $ \ids -> do
          showErrorIO (elaborateDefs ds) $ \nds -> do
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
    inp -> showError (parseAndElabSurface "(repl)" inp) $ \(c, ty) -> do
      putStrLn $ showC empty ty
      putStrLn $ showC empty c
      putStrLn $ showC empty $ nfWith Full c
  repl

showIOError :: SomeException -> String
showIOError = show

showError :: Either String t -> (t -> IO ()) -> IO ()
showError (Left msg) k = putStrLn msg
showError (Right x) k = k x

showErrorIO :: IO (Either String t) -> (t -> IO ()) -> IO ()
showErrorIO x k = x >>= flip showError k

tryIO :: IO t -> (t -> IO ()) -> IO ()
tryIO a = showErrorIO (first showIOError <$> try a)

elabSurface :: String -> Surface -> TC (Core, Core)
elabSurface file t = do
  (tm, ty) <- elaborate (enter (initialPos file) empty) t
  verify tm
  return (tm, ty)

parseAndElabSurface :: String -> String -> Either String (Core, Core)
parseAndElabSurface file src = do
  t <- parseStrEither src
  elabSurface file t

elab :: IO (Surface, String) -> IO (Core, Core)
elab getSurface = do
  (t, file) <- getSurface
  case elabSurface file t of
    Left msg -> putStrLn msg >> exitSuccess
    Right res -> return res

elabDefs :: IO (Defs, String) -> IO ()
elabDefs getDefs = do
  (ds, file) <- getDefs
  let xs = imports ds
  tryIO (loadModules xs) $ \ids -> do
    showErrorIO (elaborateDefs ds) $ \nds -> return ()

showElabDef :: GlobalEntry -> String
showElabDef (GlobalEntry x etm ety _ _ file) =
  maybe "" (++ ".") file ++ x ++ " : " ++ showC empty ety ++ " = " ++ showC empty etm

showElabDefs :: GlobalCtx -> String
showElabDefs [] = ""
showElabDefs (hd : tl) =
  case showElabDefs tl of
    "" -> showElabDef hd
    prefix -> prefix ++ "\n" ++ showElabDef hd
