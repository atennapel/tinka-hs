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
withPos p = SPos <$> getSourcePos <*> p

lexeme     = L.lexeme ws
symbol s   = lexeme (C.string s)
char c     = lexeme (C.char c)
parens p   = char '(' *> p <* char ')'
pArrow     = symbol "→" <|> symbol "->"
pBind      = pIdent <|> symbol "_"

keyword :: String -> Bool
keyword x = x == "let" || x == "λ" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  x <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pAtom :: Parser Surface
pAtom  =
      withPos (    (SVar <$> pIdent)
               <|> (SU <$ char 'U')
               <|> (SHole <$ char '_'))
  <|> parens pTm

pArg :: Parser Surface
pArg = pAtom

pSpine :: Parser Surface
pSpine = do
  h <- pAtom
  args <- many pArg
  pure $ foldl SApp h args

pLamBinder :: Parser ([Name], Maybe Surface)
pLamBinder = parens ((,) <$> some pBind <*> optional (char ':' *> pTm))
  <|> ((\x -> ([x], Nothing)) <$> pBind)

pLam :: Parser Surface
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pLamBinder
  char '.'
  t <- pTm
  pure $ foldr (\(xs, ty) b -> foldr (`SAbs` ty) b xs) t xs

pPiBinder :: Parser ([Name], Surface)
pPiBinder = parens ((,) <$> some pBind <*> (char ':' *> pTm))

pPi :: Parser Surface
pPi = do
  dom <- some pPiBinder
  pArrow
  cod <- pTm
  pure $ foldr (\(xs, a) t -> foldr (`SPi` a) t xs) cod dom

pFunOrSpine :: Parser Surface
pFunOrSpine = do
  sp <- pSpine
  optional pArrow >>= \case
    Nothing -> pure sp
    Just _  -> SPi "_" sp <$> pTm

pLet :: Parser Surface
pLet = do
  pKeyword "let"
  x <- pIdent
  ann <- optional (char ':' *> pTm)
  char '='
  t <- pTm
  symbol ";"
  SLet x ann t <$> pTm

pTm :: Parser Surface
pTm = withPos (pLam <|> pLet <|> try pPi <|> pFunOrSpine)

pSrc :: Parser Surface
pSrc = ws *> pTm <* eof

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
