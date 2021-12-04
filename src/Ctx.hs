module Ctx where

import Data.Coerce (coerce)

import Common
import Levels
import Core
import Val
import Evaluation

type Binders = [(Name, Maybe VTy)]

data Ctx = Ctx {
  lvl :: Lvl,
  env :: Env,
  binders :: Binders
}

empty :: Ctx
empty = Ctx 0 [] []

define :: Name -> VTy -> Val -> Ctx -> Ctx
define x t v (Ctx l e b) = Ctx (l + 1) (Right v : e) ((x, Just t) : b)

bind :: Name -> VTy -> Ctx -> Ctx
bind x t (Ctx l e b) = Ctx (l + 1) (Right (VVar l) : e) ((x, Just t) : b)

bindLevel :: Name -> Ctx -> Ctx
bindLevel x (Ctx l e b) = Ctx (l + 1) (Left (vFinLevelVar l) : e) ((x, Nothing) : b) 

indexCtx :: Ctx -> Ix -> Maybe (Maybe VTy)
indexCtx ctx i = go (binders ctx) (coerce i)
  where
    go :: Binders -> Int -> Maybe (Maybe VTy)
    go [] _ = Nothing
    go ((_, mty) : _) 0 = Just mty
    go (_ : bs) i = go bs (i - 1)
  
lookupCtx :: Ctx -> Name -> Maybe (Ix, Maybe VTy)
lookupCtx ctx x = go (binders ctx) 0
  where
    go :: Binders -> Int -> Maybe (Ix, Maybe VTy)
    go [] _ = Nothing
    go ((y, mty) : _) i | x == y = Just (Ix i, mty)
    go (_ : bs) i = go bs (i + 1)

showV :: Ctx -> Val -> String
showV ctx v = show (quote (lvl ctx) v)

evalCtx :: Ctx -> Tm -> Val
evalCtx ctx tm = eval (env ctx) tm

finLevelCtx :: Ctx -> FinLevel -> VFinLevel
finLevelCtx ctx l = finLevel (env ctx) l
