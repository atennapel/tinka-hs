module Parser (parseStr, parseStrIO, parseStdin, parseStrDefs, parseStdinDefs, parseStrDefsIO) where

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
pArrow = symbol "→" <|> symbol "->"

pCross :: Parser String
pCross = symbol "⨯" <|> symbol "**"

pLambda :: Parser Char
pLambda = char 'λ' <|> char '\\'

keyword :: String -> Bool
keyword x = x == "let" || x == "λ" || x == "Type" || x == "fst" || x == "snd" || x == "Lift" || x == "lift" || x == "lower" || x == "elim" || x == "Con" || x == "Refl"

pLifting :: Parser ULvl
pLifting = do
  lift <- optional (do
    char '^'
    l <- optional L.decimal
    return $ fromMaybe 1 l)
  return $ fromMaybe 0 lift

pIdent :: Parser (Name, ULvl)
pIdent = try $ do
  x <- takeWhile1P Nothing isAlphaNum
  guard (not (keyword x))
  lift <- pLifting
  ws
  return (x, lift)

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

pCommaSeparated :: Parser [Surface]
pCommaSeparated = do
  first <- pSurface
  rest <- optional (do
    symbol ","
    pCommaSeparated)
  return $ maybe [first] (first :) rest

pPair :: Parser Surface
pPair = parens (foldr1 SPair <$> pCommaSeparated)

pProjType :: Parser ProjType
pProjType = Fst <$ symbol "fst" <|> Snd <$ symbol "snd"

pProj :: Parser Surface
pProj = do
  ty <- pProjType
  tm <- pSurface
  return $ SProj tm ty

pLift :: Parser Surface
pLift = do
  symbol "Lift"
  SLift <$> pSurface

pLiftTerm :: Parser Surface
pLiftTerm = do
  symbol "lift"
  SLiftTerm <$> pSurface

pLower :: Parser Surface
pLower = do
  symbol "lower"
  SLower <$> pSurface

pPrimElim :: Parser Surface
pPrimElim = do
  symbol "elim"
  (x, l) <- pIdent
  k <- optional L.decimal
  return $ SPrimElim x l (fromMaybe 0 k)

pCon :: Parser Surface
pCon = do
  symbol "Con"
  SCon <$> pSurface

pHole :: Parser Surface
pHole = do
  C.char '_'
  x <- optional (takeWhile1P Nothing isAlphaNum)
  ws
  return $ SHole x

pAtom :: Parser Surface
pAtom =
  withPos (
    (SU <$> pType) <|>
    pHole <|>
    (SRefl <$ symbol "Refl") <|>
    (uncurry SVar <$> pIdent))
  <|> pProj
  <|> pLift
  <|> pLiftTerm
  <|> pLower
  <|> pCon
  <|> pPrimElim
  <|> pPair
  <|> parens pSurface

pBinder :: Parser Name
pBinder = (fst <$> pIdent) <|> symbol "_"

pSpine :: Parser Surface
pSpine = foldl1 SApp <$> some pAtom

pLam :: Parser Surface
pLam = do
  pLambda
  xs <- some pBinder
  char '.'
  t <- pSurface
  pure (foldr SAbs t xs)

pArrowOrCross :: Parser Bool
pArrowOrCross = (True <$ pArrow) <|> (False <$ pCross)

pPiOrSigma :: Parser Surface
pPiOrSigma = do
  dom <- some (parens ((,) <$> some pBinder <*> (char ':' *> pSurface)))
  ty <- pArrowOrCross
  cod <- pSurface
  let tyfun a = if ty then (`SPi` a) else (`SSigma` a)
  pure $ foldr (\(xs, a) t -> foldr (tyfun a) t xs) cod dom

funOrSpine :: Parser Surface
funOrSpine = do
  sp <- pSpine
  optional pArrowOrCross >>= \case
    Nothing -> pure sp
    Just b  -> (if b then SPi else SSigma) "_" sp <$> pSurface

pLet :: Parser Surface
pLet = do
  pKeyword "let"
  x <- pBinder
  a <- optional (do
    symbol ":"
    pSurface)
  symbol "="
  t <- pSurface
  symbol ";"
  SLet x a t <$> pSurface

pSurface :: Parser Surface
pSurface = withPos (pLam <|> pLet <|> try pPiOrSigma <|> funOrSpine)

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

parseStrEither :: String -> Either String Surface
parseStrEither src = case parse pSrc "(stdin)" src of
  Left e -> Left (errorBundlePretty e)
  Right t -> return t

parseStrIO :: String -> IO Surface
parseStrIO src = case parseStrEither src of
  Left e -> error e
  Right t -> return t

parseStdin :: IO (Surface, String)
parseStdin = do
  src <- getContents
  t <- parseStr src
  pure (t, src)

pDefDef :: Parser [Def]
pDefDef = do
  x <- pBinder
  a <- optional (do
    symbol ":"
    pSurface)
  symbol "="
  body <- pSurface
  return [Def x a body]

pImport :: Parser [Def]
pImport = do
  symbol "import"
  names <- many (lexeme $ takeWhile1P Nothing (\x -> isAlphaNum x || x == '/' || x == '\\' || x == '.'))
  return $ Import <$> names

pDef :: Parser [Def]
pDef = pImport <|> pDefDef

pDefs :: Parser Defs
pDefs = do
  ws
  ds <- pDef
  ws
  symbol ";"
  ws
  dsrest <- pDefs <|> ([] <$ eof)
  return (ds ++ dsrest)

parseStrDefs :: String -> IO Defs
parseStrDefs src =
  case parse pDefs "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStrDefsEither :: String -> Either String Defs
parseStrDefsEither src = case parse pDefs "(stdin)" src of
  Left e -> Left (errorBundlePretty e)
  Right t -> return t

parseStrDefsIO :: String -> IO Defs
parseStrDefsIO src = case parseStrDefsEither src of
  Left e -> error e
  Right t -> return t

parseStdinDefs :: IO (Defs, String)
parseStdinDefs = do
  src <- getContents
  t <- parseStrDefs src
  pure (t, src)
