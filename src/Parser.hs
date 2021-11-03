module Parser (parseStr, parseStdin) where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Void
import System.Exit
import Text.Megaparsec
import Data.Maybe (fromMaybe)

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

import Surface
import Common

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Surface -> Parser Surface
withPos p = SPos <$> getSourcePos <*> p

lexeme :: Parser a -> Parser a
lexeme = L.lexeme ws

symbol :: String -> Parser String
symbol s = lexeme (C.string s)

char :: Char -> Parser Char
char c = lexeme (C.char c)

parens :: Parser a -> Parser a
parens p = char '(' *> p <* char ')'

pArrow :: Parser String
pArrow   = symbol "→" <|> symbol "->"

keyword :: String -> Bool
keyword x = x == "let" || x == "λ" || x == "Type"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pType :: Parser ULvl
pType = do
  C.string "Type"
  l <- optional L.decimal
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws
  return $ fromMaybe 0 l

pAtom :: Parser Surface
pAtom =
  withPos (
    (SU <$> pType) <|>
    (SHole <$ symbol "_") <|>
    (SVar <$> pIdent))
  <|> parens pSurface

pBinder :: Parser Name
pBinder = pIdent <|> symbol "_"

pSpine :: Parser Surface
pSpine = foldl1 SApp <$> some pAtom

pLam :: Parser Surface
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pBinder
  char '.'
  t <- pSurface
  pure (foldr (`SAbs` Nothing) t xs)

pPi :: Parser Surface
pPi = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pSurface)))
  pArrow
  cod <- pSurface
  pure $ foldr (\(xs, a) t -> foldr (`SPi` a) t xs) cod dom

funOrSpine :: Parser Surface
funOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> SPi "_" sp <$> pSurface

pLet :: Parser Surface
pLet = do
  pKeyword "let"
  x <- pBinder
  symbol ":"
  a <- pSurface
  symbol "="
  t <- pSurface
  symbol ";"
  SLet x (Just a) t <$> pSurface

pSurface :: Parser Surface
pSurface = withPos (pLam <|> pLet <|> try pPi <|> funOrSpine)

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
  src <- getContents
  t <- parseStr src
  pure (t, src)
