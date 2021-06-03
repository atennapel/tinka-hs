module Parser (parseStr, parseStdin) where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Void
import System.Exit
import Text.Megaparsec

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

import Surface
import Common

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Surface -> Parser Surface
withPos p = do
  pos <- getSourcePos
  p >>= \case
    t@SPos{} -> pure t
    t -> pure (SPos pos t)

lexeme = L.lexeme ws
symbol s = lexeme (C.string s)
char c = lexeme (C.char c)
parens p = char '(' *> p <* char ')'
pBind = pIdent <|> symbol "_"
pArrow = symbol "->"

keyword :: String -> Bool
keyword x = x == "let" || x == "\\" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x <- C.letterChar
  xs <- takeWhile1P Nothing (\c -> isAlphaNum c || c == '\'')
  guard (not (keyword (x : xs)))
  (x : xs) <$ ws

pKeyword :: String -> Parser ()
pKeyword w = do
  C.string w
  (takeWhileP Nothing (\c -> isAlphaNum c || c == '\'') *> empty) <|> ws

pAtom :: Parser Surface
pAtom = withPos ((SVar <$> pIdent) <|> (SU <$ symbol "U")) <|> parens pSurface

pApp :: Parser Surface
pApp = do
  h <- pAtom
  as <- many pAtom
  pure $ foldl SApp h as

pAbsBind :: Parser (Name, Maybe Surface)
pAbsBind =
  parens ((,) <$> pBind <*> optional (char ':' *> pSurface))
  <|> ((,Nothing) <$> pBind)

pAbs = do
  char '\\'
  xs <- some pAbsBind
  char '.'
  t <- pAbsLet
  pure $ foldr (\(x, t) u -> SAbs x t u) t xs

pPiBind :: Parser ([Name], Surface)
pPiBind = parens ((,) <$> some pBind <*> (char ':' *> pSurface))

pPi :: Parser Surface
pPi = do
  optional (try (some pPiBind)) >>= \case
    Nothing -> do
      t <- pApp
      (pArrow *> (SPi "_" t <$> pPi)) <|> pure t
    Just bs -> do
      bs <- some pPiBind
      case bs of
        [([x], a)] -> SPi x a <$> (pArrow *> pPi)
        dom -> do
          pArrow
          b <- pPi
          pure $ foldr (\(xs, a) t -> foldr (`SPi` a) t xs) b dom

pLet :: Parser Surface
pLet = do
  pKeyword "let"
  x <- pBind
  ann <- optional (char ':' *> pSurface)
  char '='
  t <- pSurface
  symbol ";"
  u <- pAbsLet
  SLet x ann t <$> pAbsLet

pAbsLet :: Parser Surface
pAbsLet = withPos (pAbs <|> pLet <|> pPi)

pSurface :: Parser Surface
pSurface = withPos pAbsLet

pSrc :: Parser Surface
pSrc = ws *> pSurface <* eof

parseStr :: String -> IO Surface
parseStr src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStdin :: IO (Surface, String)
parseStdin = do
  file <- getContents
  tm <- parseStr file
  pure (tm, file)
