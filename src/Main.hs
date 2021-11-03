module Main where

import System.Environment
import System.Exit
import Text.Megaparsec (initialPos)
import Control.Monad.Trans.Reader (ReaderT(runReaderT))
import Control.Monad.Trans.Except (runExceptT)
import Data.Functor.Identity (runIdentity)

import Common
import Surface
import Ctx
import Val
import Elaboration
import Verification
import Parser
import Core


main :: IO ()
main = mainWith getArgs parseStdin

addGlobal :: Name -> String -> GlobalCtx -> IO GlobalCtx
addGlobal x def gs = do
  t <- parseStr def
  let elab = elaborate empty t
  let res = runIdentity $ runExceptT $ runReaderT elab gs
  case res of
    Right (tm, ty) ->
      return $ GlobalEntry x tm ty (eval gs [] tm) (eval gs [] ty) : gs
    Left msg -> putStrLn msg >> exitSuccess

globals :: IO GlobalCtx
globals = addGlobal "id" "let id : (A : Type) -> A -> A = \\A x. x; id" []

mainWith :: IO [String] -> IO (Surface, String) -> IO ()
mainWith getOpt getSurface = do
  gs <- globals
  getOpt >>= \case
    ["parse"] -> do
      (t, file) <- getSurface
      print t
    ["nf"] -> do
      (c, ty) <- elab getSurface
      putStrLn $ showC empty $ nf gs c
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
      putStrLn $ showC empty $ nf gs c
  
elab :: IO (Surface, String) -> IO (Core, Core)
elab getSurface = do
  gs <- globals
  (t, file) <- getSurface
  let elab = elaborate (enter (initialPos file) empty) t
  let res = runIdentity $ runExceptT $ runReaderT elab gs
  case res of
    Left msg -> putStrLn msg >> exitSuccess
    Right res@(tm, ty) -> do
      let ver = verify tm
      let resver = runIdentity $ runExceptT $ runReaderT ver gs
      case resver of
        Left msg -> putStrLn msg >> exitSuccess
        Right _ -> return res
