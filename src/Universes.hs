module Universes where

import Common

import qualified Data.IntMap as IM
import Data.IORef
import System.IO.Unsafe
import Control.Exception (catch, SomeException)
import Data.List (intercalate)

-- umetas
newtype UMetaVar = UMetaVar { unUMetaVar :: Int } deriving (Eq, Show, Num, Ord) via Int

data UMetaEntry = USolved Univ | UUnsolved
  deriving (Eq)

type UMetaMap = IM.IntMap UMetaEntry

nextUMeta :: IORef Int
nextUMeta = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextUMeta #-}

umcxt :: IORef UMetaMap
umcxt = unsafeDupablePerformIO $ newIORef mempty
{-# noinline umcxt #-}

getUMetas :: IO UMetaMap
getUMetas = readIORef umcxt

showUMetaMap :: UMetaMap -> String
showUMetaMap m = intercalate "\n" $ map go $ IM.assocs m
  where
    go (k, UUnsolved) = "?" ++ show k
    go (k, USolved u) = "?" ++ show k ++ " = " ++ show u

allUMetasSolved :: IO Bool
allUMetasSolved = do
  ms <- getUMetas
  if IM.null ms then
    return True
  else
    return $ any (== UUnsolved) $ IM.elems ms

newUMeta :: IO UMetaVar
newUMeta = do
  m <- readIORef nextUMeta
  writeIORef nextUMeta $! m + 1
  modifyIORef umcxt $ IM.insert m UUnsolved
  return $ UMetaVar m

lookupUMeta :: UMetaVar -> UMetaEntry
lookupUMeta (UMetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef umcxt
  case IM.lookup m ms of
    Just e  -> pure e
    Nothing -> error "impossible"

resetUMetas :: IO ()
resetUMetas = do
  writeIORef nextUMeta 0
  writeIORef umcxt mempty

-- univeses
data Univ
  = UConst ULvl
  | US Univ
  | UMax Univ Univ
  | UMeta UMetaVar
  deriving (Eq)

instance Show Univ where
  show (UConst l) = show l
  show (US u) = "(S" ++ " " ++ show u ++ ")"
  show (UMax u1 u2) = "(max " ++ show u1 ++ " " ++ show u2 ++ ")"
  show (UMeta m) = "?" ++ show m

tryNormalizeUniv :: Univ -> Maybe Univ
tryNormalizeUniv (US (UConst l)) = Just (UConst (l + 1))
tryNormalizeUniv (US u) = US <$> tryNormalizeUniv u
tryNormalizeUniv u@(UMeta m) =
  case lookupUMeta m of
    USolved u' -> Just u'
    UUnsolved -> Nothing
tryNormalizeUniv (UMax u1 u2) | u1 == u2 = Just u1
tryNormalizeUniv (UMax (UConst l1) (UConst l2)) = Just (UConst (max l1 l2))
tryNormalizeUniv (UMax (US u1) (US u2)) = Just (US (UMax u1 u2))
tryNormalizeUniv _ = Nothing

normalizeUniv :: Univ -> Univ
normalizeUniv u = maybe u normalizeUniv (tryNormalizeUniv u)

uAddConst :: ULvl -> Univ -> Univ
uAddConst 0 u = normalizeUniv u
uAddConst n u = uAddConst (n - 1) (US u)

us :: Univ -> Univ
us = uAddConst 1

umax :: Univ -> Univ -> Univ
umax u1 u2 = normalizeUniv (UMax u1 u2)

solveUniv :: UMetaVar -> Univ -> IO ()
solveUniv m u | occurs u = error $ "occurs check failed: ?" ++ show m ++ " := " ++ show u
  where
    occurs (UMeta m') = m == m'
    occurs (US u) = occurs u
    occurs (UMax u1 u2) = occurs u1 || occurs u2
    occurs _ = False
solveUniv m u = modifyIORef' umcxt $ IM.insert (unUMetaVar m) (USolved u)

unifyUniv :: Univ -> Univ -> IO ()
unifyUniv u1 u2 =
  case (normalizeUniv u1, normalizeUniv u2) of
    (UConst l1, UConst l2) | l1 == l2 -> return ()
    (US u1, US u2) -> unifyUniv u1 u2
    (UMax u1 u2, UMax u3 u4) ->
      catch (unifyUniv u1 u3 >> unifyUniv u2 u4) $ \(_ :: SomeException) ->
        unifyUniv u1 u4 >> unifyUniv u2 u3
    (UMeta m, u) -> solveUniv m u
    (u, UMeta m) -> solveUniv m u
    (u1, u2) -> error $ "failed to unify universes: " ++ show u1 ++ " ~ " ++ show u2
