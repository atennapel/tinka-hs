module Verification (verify) where

import Common
import Core
import Ctx
import Val

check :: Ctx -> Core -> Val -> TC ()
check ctx c ty = do
  ty' <- infer ctx c
  test (conv (lvl ctx) ty' ty) $ "check failed " ++ show c ++ " : " ++ show (quote (lvl ctx) ty) ++ ", got " ++ show (quote (lvl ctx) ty')

inferU :: Ctx -> Core -> TC Ix
inferU ctx c = do
  ty <- infer ctx c
  case ty of
    VU i -> return i
    _ -> err $ "failed to infer universe in " ++ show c ++ ": " ++ show (quote (lvl ctx) ty)

infer :: Ctx -> Core -> TC Val
infer ctx (U i) = return $ VU (i + 1)
infer ctx c@(Var i) =
  let
    go [] i = err $ "undefined var " ++ show c
    go (ty : _) 0 = return ty
    go (_ : tl) n = go tl (n - 1)
  in go (ts ctx) i
infer ctx (Pi x t b) = do
  i <- inferU ctx t
  j <- inferU (bind x (eval (vs ctx) t) ctx) b
  return $ VU (max i j)
infer ctx (Abs x t b) = do
  inferU ctx t
  let ty = eval (vs ctx) t
  rty <- infer (bind x ty ctx) b
  return $ VPi x ty (closeVal ctx rty)
infer ctx c@(App f a) = do
  fty <- infer ctx f
  case fty of
    VPi x t b -> do
      check ctx a t
      return $ vinst b (eval (vs ctx) a)
    _ -> err $ "not a pi type in " ++ show c ++ ", got " ++ show (quote (lvl ctx) fty)
infer ctx (Let x t v b) = do
  inferU ctx t
  let ty = eval (vs ctx) t
  check ctx v ty
  infer (define x ty (eval (vs ctx) v) ctx) b

verify :: Core -> TC Core
verify = fmap (quote 0) . infer empty
