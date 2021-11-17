module Ctx where

import Text.Megaparsec (SourcePos)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class
import Data.Functor.Identity (Identity)
import Data.List (intercalate)

import Common
import Core
import Surface
import Val

type TC t = ReaderT GlobalCtx (ExceptT String Identity) t

err :: String -> TC t
err = lift . throwE

test :: Bool -> String -> TC ()
test True _ = return ()
test False msg = err msg

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

closeVal :: GlobalCtx -> Ctx -> Val -> Clos
closeVal gs ctx v = Clos (vs ctx) (quote gs (lvl ctx + 1) v)

showC :: Ctx -> Core -> String
showC ctx c = show $ fromCore (ns ctx) c

showVWith :: QuoteLevel -> GlobalCtx -> Ctx -> Val -> String
showVWith ql gs ctx v = show $ fromCore (ns ctx) (quoteWith ql gs (lvl ctx) v)

showV :: GlobalCtx -> Ctx -> Val -> String
showV gs ctx v = show $ fromCore (ns ctx) (quote gs (lvl ctx) v)

showLocal :: GlobalCtx -> Ctx -> String
showLocal gs ctx = let zipped = zip3 (ns ctx) (ts ctx) (vs ctx) in
  intercalate "\n" $ map format zipped
    where
      format (x, t, v) = case showV gs ctx v of
        y | x == y -> x ++ " : " ++ showV gs ctx t
        sv -> x ++ " : " ++ showV gs ctx t ++ " = " ++ sv

lookupVarMaybe :: Ctx -> Name -> TC (Maybe (Ix, Val))
lookupVarMaybe ctx x = go (ns ctx) (ts ctx) 0
  where
    go :: [Name] -> [Val] -> Ix -> TC (Maybe (Ix, Val))
    go [] [] _ = return Nothing
    go (y : _) (ty : _) i | x == y = return $ Just (i, ty)
    go (_ : ns) (_ : ts) i = go ns ts (i + 1)
    go _ _ _ = undefined

lookupVar :: Ctx -> Name -> TC (Ix, Val)
lookupVar ctx x = do
  res <- lookupVarMaybe ctx x
  case res of
    Just e -> return e
    Nothing -> err $ "undefined variable " ++ x

indexCtx :: Ctx -> Ix -> TC Val
indexCtx ctx = go (ts ctx)
  where
    go [] i = err $ "undefined var " ++ show i
    go (ty : _) 0 = return ty
    go (_ : tl) n = go tl (n - 1)

lookupGlobal :: Name -> TC GlobalEntry
lookupGlobal x = do
  gs <- ask
  case getGlobal gs x of
    Just e -> return e
    Nothing -> err $ "undefined global " ++ x
