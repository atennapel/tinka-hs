module Main where

import System.Environment
import System.Exit
import Text.Megaparsec (initialPos)
import System.IO
import GHC.IO.Encoding
import Data.List (isPrefixOf)
import Control.Monad (forM_)
import Control.Exception (try)
import Data.Bifunctor (first)

import Surface
import Ctx
import Elaboration
import Verification
import Parser
import Core
import Evaluation
import Globals

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
      putStrLn $ showC empty $ nf c
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
      putStrLn $ showC empty $ nf c

repl :: IO ()
repl = do
  putStr "> "
  hFlush stdout
  inp <- getLine
  case inp of
    defs | ":def " `isPrefixOf` defs -> do
       ds <- parseAndElabDefs (drop 5 defs)
       showError ds $ \ds -> do
        gs <- getGlobals
        putStrLn $ showElabDefs $ take (length ds) gs
    defs | ":import " `isPrefixOf` defs -> do
      let files = words (drop 8 defs)
      forM_ files $ \file -> do
        srcE <- first showIOError <$> try (readFile file)
        showError srcE $ \src -> do
          ds <- parseAndElabDefs src
          showError ds $ \ds -> do
            gs <- getGlobals
            putStrLn $ showElabDefs $ take (length ds) gs
    ":globals" -> do
      gs <- getGlobals
      putStrLn $ showElabDefs gs
    ":resetglobals" -> do
      resetGlobals
      putStrLn "done"
    inp -> showError (parseAndElabSurface "(repl)" inp) $ \(c, ty) -> do
      putStrLn $ showC empty ty
      putStrLn $ showC empty c
      putStrLn $ showC empty $ nf c
  repl

showIOError :: IOError -> String
showIOError = show

showError :: Either String t -> (t -> IO ()) -> IO ()
showError (Left msg) k = putStrLn msg
showError (Right x) k = k x

elabSurface :: String -> Surface -> TC (Core, Core)
elabSurface file t = do
  (tm, ty) <- elaborate (enter (initialPos file) empty) t
  verify tm
  return (tm, ty)

parseAndElabSurface :: String -> String -> Either String (Core, Core)
parseAndElabSurface file src = do
  t <- parseStrEither src
  elabSurface file t

fraggle :: IO (Either e a) -> (a -> IO (Either e b)) -> IO (Either e (a, b))
fraggle x k = do
  e1 <- x
  let e2 = k <$> e1
  e3 <- sequence e2
  let e4 = (>>= id) e3
  return $ (,) <$> e1 <*> e4

parseAndElabDefs :: String -> IO (Either String Defs)
parseAndElabDefs src = do
  res <- fraggle (return $ parseStrDefsEither src) elaborateDefs
  return $ fst <$> res

elab :: IO (Surface, String) -> IO (Core, Core)
elab getSurface = do
  (t, file) <- getSurface
  case elabSurface file t of
    Left msg -> putStrLn msg >> exitSuccess
    Right res -> return res

elabDefs :: IO (Defs, String) -> IO ()
elabDefs getDefs = do
  (ds, file) <- getDefs
  res <- elaborateDefs ds
  case res of
    Left msg -> putStrLn msg >> exitSuccess
    Right gs -> return ()

showElabDef :: GlobalEntry -> String
showElabDef (GlobalEntry x etm ety _ _) = x ++ " : " ++ showC empty ety ++ " = " ++ showC empty etm

showElabDefs :: GlobalCtx -> String
showElabDefs [] = ""
showElabDefs (hd : tl) =
  case showElabDefs tl of
    "" -> showElabDef hd
    prefix -> prefix ++ "\n" ++ showElabDef hd
