module Zonking (zonk) where

import Common
import Levels
import Core
import Val
import Evaluation
import Metas

zonk :: Lvl -> Env -> Tm -> Tm
zonk = go
  where
    goUnder :: Lvl -> Env -> Tm -> Tm
    goUnder k vs = go (k + 1) (Right (VVar k) : vs)

    goUnderLevel :: Lvl -> Env -> Tm -> Tm
    goUnderLevel k vs = go (k + 1) (Left (vFinLevelVar k) : vs)

    goPruning :: Val -> Env -> [Maybe Icit] -> Val
    goPruning v [] [] = v
    goPruning v (_ : vs) (Nothing : pr) = goPruning v vs pr
    goPruning v (Right w : vs) (Just i : pr) = vapp (goPruning v vs pr) w i
    goPruning v (Left w : vs) (Just _ : pr) = vappLevel (goPruning v vs pr) w
    goPruning _ _ _ = undefined

    goSp :: Lvl -> Env -> Tm -> Either Val Tm
    goSp k vs = \case
      Meta m | Solved v _ <- lookupMeta m -> Left v
      App t u i ->
        case goSp k vs t of
          Left t -> Left (vapp t (eval vs u) i)
          Right t -> Right (App t (go k vs u) i)
      AppLvl t l ->
        case goSp k vs t of
          Left t -> Left (vappLevel t (finLevel vs l))
          Right t -> Right (AppLvl t l)
      t -> Right (go k vs t)

    go :: Lvl -> Env -> Tm -> Tm
    go k vs = \case
      Meta m -> case lookupMeta m of
        Solved _ c -> go k vs c
        Unsolved {} -> Meta m
      InsertedMeta m p -> go k vs (quote k $ goPruning (vmeta m) vs p)
      App t u i ->
        case goSp k vs t of
          Left t -> go k vs $ quote k (vapp t (eval vs u) i)
          Right t -> App t (go k vs u) i
      AppLvl t l ->
        case goSp k vs t of
          Left t -> go k vs $ quote k (vappLevel t (finLevel vs l))
          Right t -> AppLvl t l
      Var x -> Var x
      t@(Type u) -> t
      Pair a b -> Pair (go k vs a) (go k vs b)
      Global x -> Global x
      Prim x -> Prim x
      Proj c p -> Proj (go k vs c) p
      Lam x i b -> Lam x i (goUnder k vs b)
      Pi x i t b -> Pi x i (go k vs t) (goUnder k vs b)
      Sigma x t b -> Sigma x (go k vs t) (goUnder k vs b)
      Let x t v b -> Let x (go k vs t) (go k vs v) (goUnder k vs b)
      LamLvl x b -> LamLvl x (goUnderLevel k vs b)
      PiLvl x b -> PiLvl x (goUnderLevel k vs b)