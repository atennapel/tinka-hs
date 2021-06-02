module Main where

import Surface
import Ctx
import Val
import Elaboration
import Verification

infixl 7 $$
($$) = SApp
infixr 4 -->
(-->) = SPi "_"

lam x = SAbs x Nothing

idterm :: Surface
idterm = SLet "id" (Just $ SPi "A" SU $ "A" --> "A") (lam "A" $ lam "x" "x") "id"

nattest :: Surface
nattest =
  SLet "Nat" Nothing (SPi "N" SU $ "N" --> ("N" --> "N") --> "N") $
  SLet "Z" (Just "Nat") (lam "N" $ lam "z" $ lam "s" "z") $
  SLet "S" (Just $ "Nat" --> "Nat") (lam "n" $ lam "N" $ lam "z" $ lam "s" $ "s" $$ ("n" $$ "N" $$ "z" $$ "s")) $
  SApp "S" (SApp "S" (SApp "S" "Z"))

main :: IO ()
main = do
  let example = nattest
  print example
  let res = elaborate example
  case res of
    Left msg -> putStrLn msg
    Right (c, ty) -> do
      putStrLn $ showC empty ty
      putStrLn $ showC empty c
      putStrLn $ showTC $ fromCore [] <$> verify c
      putStrLn $ showC empty $ nf c
