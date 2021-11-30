module Zonking (zonk, zonkLevel) where

import Common
import Core
import Val
import Evaluation
import Metas

zonkLevel :: Lvl -> Env -> Level -> Level
zonkLevel k vs (Fin l) = Fin (zonk k vs l)
zonkLevel k vs Omega = Omega

zonk :: Lvl -> Env -> Core -> Core
zonk = go
  where
    goUnder :: Lvl -> Env -> Core -> Core
    goUnder k vs = go (k + 1) (VVar k : vs)

    goUnderLevel :: Lvl -> Env -> Level -> Level
    goUnderLevel k vs = zonkLevel (k + 1) (VVar k : vs)

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
      Lower c -> Lower (go k vs c)
      LiftTerm c -> LiftTerm (go k vs c)
      Lift c -> Lift (go k vs c)
      U u -> U (zonkLevel k vs u)
      ULevel -> ULevel
      L0 -> L0
      LS a -> LS (go k vs a)
      LMax a b -> LMax (go k vs a) (go k vs b)
      Pair a b -> Pair (go k vs a) (go k vs b)
      Global x -> Global x
      Prim x -> Prim x
      PrimElim x -> PrimElim x
      Proj c p -> Proj (go k vs c) p
      Abs x i b -> Abs x i (goUnder k vs b)
      Pi x i t u1 b u2 -> Pi x i (go k vs t) (zonkLevel k vs u1) (goUnder k vs b) (goUnderLevel k vs u2)
      Sigma x t u1 b u2 -> Sigma x (go k vs t) (zonkLevel k vs u1) (goUnder k vs b) (goUnderLevel k vs u2)
      Let x t v b -> Let x (go k vs t) (go k vs v) (goUnder k vs b)
