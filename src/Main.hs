module Main where

import System.Environment
import System.Exit
import Text.Megaparsec (initialPos)

import Surface
import Ctx
import Elaboration
import Verification
import Parser
import Core
import Evaluation
import Globals

main :: IO ()
main = mainWith getArgs parseStdin

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
    Right res@(tm, ty) ->
      case verify tm of
        Left msg -> putStrLn msg >> exitSuccess
        Right _ -> return res

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
showElabDefs (hd : tl) = showElabDefs tl ++ "\n" ++ showElabDef hd
