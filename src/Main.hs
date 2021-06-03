module Main where

import System.Environment
import System.Exit
import Text.Megaparsec (initialPos)

import Surface
import Ctx
import Val
import Elaboration
import Parser
import Core

main :: IO ()
main = mainWith getArgs parseStdin

mainWith :: IO [String] -> IO (Surface, String) -> IO ()
mainWith getOpt getSurface = do
  getOpt >>= \case
    ["nf"] -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty $ nf c
    ["type"] -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty ty
    ["elab"] -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty c
    _ -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty ty
      putStrLn $ showC empty c
      putStrLn $ showC empty $ nf c
  
elab :: IO (Surface, String) -> IO (Core, Core)
elab getSurface = do
  (t, file) <- getSurface
  case elaborate (enter (initialPos file) empty) t of
    Left msg -> putStrLn msg >> exitSuccess
    Right res -> return res
