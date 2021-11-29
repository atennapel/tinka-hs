module Zonking (zonk) where

import Common
import Core
import Val
import Evaluation
import Metas
import Universes

zonk :: Lvl -> Env -> Core -> Core
zonk = go
  where
    goUnder :: Lvl -> Env -> Core -> Core
    goUnder k vs = go (k + 1) (VVar k : vs)

    goPruning :: Val -> Env -> Pruning -> Val
    goPruning v [] [] = v
    goPruning v (_ : vs) (Nothing : pr) = goPruning v vs pr
    goPruning v (w : vs) (Just i : pr) = vapp (goPruning v vs pr) w i
    goPruning _ _ _ = undefined

    goSp :: Lvl -> Env -> Core -> Either Val Core
    goSp k vs = \case
      Meta m | Solved _ _ _ _ v <- lookupMeta m -> Left v
      App t u i ->
        case goSp k vs t of
          Left t -> Left (vapp t (eval vs u) i)
          Right t -> Right (App t (go k vs u) i)
      t -> Right (go k vs t)

    go :: Lvl -> Env -> Core -> Core
    go k vs = \case
      Meta m -> case lookupMeta m of
        Solved _ _ _ c _ -> go k vs c
        Unsolved {} -> Meta m
      AppPruning c p -> go k vs (quote k $ goPruning (eval vs c) vs p)
      App t u i ->
        case goSp k vs t of
          Left t -> go k vs $ quote k (vapp t (eval vs u) i)
          Right t -> App t (go k vs u) i
      Var x -> Var x
      Refl -> Refl
      Con c -> Con (go k vs c)
      Lower c -> Lower (go k vs c)
      LiftTerm c -> LiftTerm (go k vs c)
      Lift c -> Lift (go k vs c)
      U u -> U (normalizeUniv u)
      Pair a b -> Pair (go k vs a) (go k vs b)
      Global x l -> Global x l
      Prim x l -> Prim x l
      PrimElim x l k -> PrimElim x l k
      Proj c p -> Proj (go k vs c) p
      Abs x i b -> Abs x i (goUnder k vs b)
      Pi x i t u1 b u2 -> Pi x i (go k vs t) (normalizeUniv u1) (goUnder k vs b) (normalizeUniv u2)
      Sigma x t u1 b u2 -> Sigma x (go k vs t) (normalizeUniv u1) (goUnder k vs b) (normalizeUniv u2)
      Let x t v b -> Let x (go k vs t) (go k vs v) (goUnder k vs b)
