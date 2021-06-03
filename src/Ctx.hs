module Ctx where

import Text.Megaparsec (SourcePos)

import Common
import Core
import Surface
import Val

type TC t = Either String t

err :: String -> TC t
err = Left

test :: Bool -> String -> TC ()
test True _ = return ()
test False msg = err msg

showTC :: Show t => TC t -> String
showTC (Left msg) = msg
showTC (Right x) = show x

data Ctx = Ctx {
  lvl :: Lvl,
  ns :: [Name],
  ts :: [Val],
  vs :: Env,
  pos :: Maybe SourcePos
}

empty :: Ctx
empty = Ctx 0 [] [] [] Nothing

define :: Name -> Val -> Val -> Ctx -> Ctx
define x t v ctx = Ctx (lvl ctx + 1) (x : ns ctx) (t : ts ctx) (v : vs ctx) (pos ctx)

bind :: Name -> Val -> Ctx -> Ctx
bind x t ctx = Ctx (lvl ctx + 1) (x : ns ctx) (t : ts ctx) (vvar (lvl ctx) : vs ctx) (pos ctx)

enter :: SourcePos -> Ctx -> Ctx
enter p ctx = ctx { pos = Just p }

closeVal :: Ctx -> Val -> Clos
closeVal ctx v = Clos (vs ctx) (quote (lvl ctx + 1) v)

showC :: Ctx -> Core -> String
showC ctx c = show $ fromCore (ns ctx) c

showV :: Ctx -> Val -> String
showV ctx v = show $ fromCore (ns ctx) (quote (lvl ctx) v)

lookupVar :: Ctx -> Name -> TC (Ix, Val)
lookupVar ctx x = go (ns ctx) (ts ctx) 0
  where
    go :: [Name] -> [Val] -> Ix -> TC (Ix, Val)
    go [] [] _ = err $ "undefined variable " ++ x
    go (y : _) (ty : _) i | x == y = return (i, ty)
    go (_ : ns) (_ : ts) i = go ns ts (i + 1)
    go _ _ _ = undefined
