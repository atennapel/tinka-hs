module Verification (verify) where

import Core
import Ctx
import Val

checkV :: Ctx -> Core -> Val -> TC ()
checkV ctx c ty = do
  ty' <- inferV ctx c
  test (conv (lvl ctx) ty' ty) $ "check failed " ++ show c ++ " : " ++ show (quote (lvl ctx) ty) ++ ", got " ++ show (quote (lvl ctx) ty')

inferV :: Ctx -> Core -> TC Val
inferV ctx U = return VU -- type-in-type
inferV ctx c@(Var i) =
  let
    go [] i = err $ "undefined var " ++ show c
    go (ty : _) 0 = return ty
    go (_ : tl) n = go tl (n - 1)
  in go (ts ctx) i
inferV ctx (Pi x t b) = do
  checkV ctx t VU
  checkV (bind x (eval (vs ctx) t) ctx) b VU
  return VU
inferV ctx (Abs x t b) = do
  checkV ctx t VU
  let ty = eval (vs ctx) t
  rty <- inferV (bind x ty ctx) b
  return $ VPi x ty (closeVal ctx rty)
inferV ctx c@(App f a) = do
  fty <- inferV ctx f
  case fty of
    VPi x t b -> do
      checkV ctx a t
      return $ vinst b (eval (vs ctx) a)
    _ -> err $ "not a pi type in " ++ show c ++ ", got " ++ show (quote (lvl ctx) fty)
inferV ctx (Let x t v b) = do
  checkV ctx t VU
  let ty = eval (vs ctx) t
  checkV ctx v ty
  inferV (define x ty (eval (vs ctx) v) ctx) b

verify :: Core -> TC Core
verify = fmap (quote 0) . inferV empty
