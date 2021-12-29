module Main where

import System.Environment
import Text.Megaparsec (initialPos)
import System.IO
import GHC.IO.Encoding
import Control.Exception (catch, SomeException)
import Data.List (isPrefixOf)
import System.Exit (exitSuccess)

import Common
import Surface
import Ctx
import Elaboration
import Parser
import Core
import Evaluation
import Globals
import Modules

main :: IO ()
main = do
  setLocaleEncoding utf8
  mainWith getArgs parseStdin

mainWith :: IO [String] -> IO (STm, String) -> IO ()
mainWith getOpt getSurface = do
  getOpt >>= \case
    ["parse"] -> do
      (t, file) <- getSurface
      print t
    ["nf"] -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty $ nf c
    ["type"] -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty ty
    ["elab"] -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty c
    ["repl"] -> do
      putStrLn "tinka repl"
      repl
    ["parse-decls"] -> do
      (t, file) <- parseStdinDecls
      print t
    ["elab-decls"] -> try $ do
      elabDecls parseStdinDecls
      gs <- getGlobals
      putStrLn $ showElabDecls gs
      case getGlobal "main" of
        Just e ->
          putStrLn $ showC empty (nf (gCoreVal e))
        Nothing -> return ()
    ["elab-decls-debug"] -> try $ do
      setDebug True
      elabDecls parseStdinDecls
      gs <- getGlobals
      putStrLn $ showElabDecls gs
      case getGlobal "main" of
        Just e ->
          putStrLn $ showC empty (nf (gCoreVal e))
        Nothing -> return ()
    _ -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty ty
      putStrLn $ showC empty c
      putStrLn $ showC empty $ nf c

repl :: IO ()
repl = do
  putStr "> "
  hFlush stdout
  inp <- getLine
  case inp of
    decls | ":let " `isPrefixOf` decls || ":import " `isPrefixOf` decls -> try $ do
      let prefixN = if ":let " `isPrefixOf` decls then 5 else 1
      ds <- parseStrDeclsIO (drop prefixN decls)
      let xs = imports ds
      ids <- loadModules xs
      nds <- elaborateDecls Nothing ds
      gs <- getGlobals
      putStrLn $ showElabDecls $ take (countNames nds + countNames ids) gs
    ":globals" -> do
      gs <- getGlobals
      putStrLn $ showElabDecls gs
    ":resetglobals" -> do
      resetGlobals
      putStrLn "done"
    ":exit" -> stop
    ":quit" -> stop
    ":q" -> stop
    s | s == ":debug" || s == ":d" -> do
      b <- getDebug
      setDebug (not b)
      putStrLn $ "debug = " ++ show (not b)
    inp -> try $ do
      (c, ty) <- parseAndElabSurface "(repl)" inp
      putStrLn $ showC empty ty
      putStrLn $ showC empty c
      putStrLn $ showC empty $ nf c
  repl

stop :: IO ()
stop = putStrLn "bye" >> exitSuccess

tryIO :: IO t -> (t -> IO ()) -> IO ()
tryIO a k = do
  res <- catch (Right <$> a) $ \(e :: SomeException) -> return $ Left (show e)
  case res of
    Left msg -> putStrLn msg
    Right x -> k x

try :: IO () -> IO ()
try a = tryIO a $ \_ -> return ()

elabSurface :: String -> STm -> IO (Tm, Tm)
elabSurface file t = do
  (tm, ty, _) <- elaborate (enter (initialPos file) empty) t
  return (tm, ty)

parseAndElabSurface :: String -> String -> IO (Tm, Tm)
parseAndElabSurface file src = do
  t <- parseStrIO src
  elabSurface file t

elab :: IO (STm, String) -> IO (Tm, Tm)
elab getSurface = do
  (t, file) <- getSurface
  elabSurface file t

elabDecls :: IO (Decls, String) -> IO ()
elabDecls getDecls = do
  (ds, file) <- getDecls
  let xs = imports ds
  ids <- loadModules xs
  elaborateDecls Nothing ds
  return ()

reduceGlobalLet :: Name -> Tm -> Tm
reduceGlobalLet x (Let y _ v (Var 0)) | x == y = v
reduceGlobalLet _ t = t

showElabDef :: GlobalEntry -> String
showElabDef (GlobalEntry x _ _ _ ety _ etm file) =
  maybe "" (++ ".") file ++ showName x ++ " : " ++ showC empty ety ++ " = " ++ showC empty (reduceGlobalLet x etm)

showElabDecls :: GlobalCtx -> String
showElabDecls [] = ""
showElabDecls (hd : tl) =
  case showElabDecls tl of
    "" -> showElabDef hd
    prefix -> prefix ++ "\n" ++ showElabDef hd
