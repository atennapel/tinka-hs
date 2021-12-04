module Main where

import System.Environment
import Text.Megaparsec (initialPos)
import System.IO
import GHC.IO.Encoding
import Control.Exception (catch, SomeException)

import Surface
import Ctx
import Elaboration
import Parser
import Core
import Evaluation

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
    inp -> try $ do
      (c, ty) <- parseAndElabSurface "(repl)" inp
      putStrLn $ showC empty ty
      putStrLn $ showC empty c
      putStrLn $ showC empty $ nf c
  repl

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
  (tm, ty) <- elaborate (enter (initialPos file) empty) t
  return (tm, ty)

parseAndElabSurface :: String -> String -> IO (Tm, Tm)
parseAndElabSurface file src = do
  t <- parseStrIO src
  elabSurface file t

elab :: IO (STm, String) -> IO (Tm, Tm)
elab getSurface = do
  (t, file) <- getSurface
  elabSurface file t
