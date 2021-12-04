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

braces :: Parser a -> Parser a
braces p = char '{' *> p <* char '}'

brackets :: Parser a -> Parser a
brackets p = char '[' *> p <* char ']'

angled :: Parser a -> Parser a
angled p = char '<' *> p <* char '>'

pArrow :: Parser String
pArrow = symbol "→" <|> symbol "->"

pCross :: Parser String
pCross = symbol "⨯" <|> symbol "**"

pLambda :: Parser Char
pLambda = char 'λ' <|> char '\\'

keywords :: [String]
keywords = ["let", "λ", "Type"]

keyword :: String -> Bool
keyword x = x `elem` keywords

pName :: Parser Name
pName = try $ do
  x <- takeWhile1P Nothing (\c -> isAlphaNum c || c == '-' || c == '\'')
  guard (not (keyword x) && x /= "-" && x /= "'")
  return x

pIdent :: Parser Name
pIdent = try $ do
  x <- pName
  ws
  return x

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhile1P Nothing isAlphaNum *> empty) <|> ws

pLevel :: Parser SLevel
pLevel = suc <|> max <|> pLevelAtom
  where
    suc = do
      symbol "S"
      SLS <$> pLevelAtom
    max = do
      symbol "max"
      SLMax <$> pLevelAtom <*> pLevelAtom

pLevelAtom :: Parser SLevel
pLevelAtom = nat <|> var <|> parens pLevel
  where
    var = SLVar <$> pIdent
    nat = do
      i <- L.decimal
      ws
      return $ SLNat i

pType :: Parser Surface
pType = do
  symbol "Type"
  SU <$> pLevelAtom

pCommaSeparated :: Parser [Surface]
pCommaSeparated = do
  first <- pSurface
  rest <- optional (do
    symbol ","
    pCommaSeparated)
  return $ maybe [first] (first :) rest

pPair :: Parser Surface
pPair = parens (foldr1 SPair <$> pCommaSeparated)

pUnitPair :: Parser Surface
pUnitPair = brackets (foldr SPair (SVar "[]") <$> pCommaSeparated)

pHole :: Parser Surface
pHole = do
  C.char '_'
  x <- optional (takeWhile1P Nothing isAlphaNum)
  ws
  return $ SHole x

pNat :: Parser Surface
pNat = do
  i <- L.decimal
  ws
  return $ SNatLit i

pAtom :: Parser Surface
pAtom =
  withPos (
    pHole <|>
    pNat <|>
    (SVar <$> pIdent))
  <|> try pType
  <|> try (SVar "()" <$ parens ws)
  <|> try (SVar "[]" <$ brackets ws)
  <|> try pPair
  <|> try pUnitPair
  <|> parens pSurface

pBinder :: Parser Name
pBinder = pIdent <|> symbol "_"

pProj :: Parser SProjType
pProj = do
  char '.'
  p <- simple <|> index <|> named
  ws
  return p
  where
    simple = char '_' >> (SFst <$ char '1' <|> SSnd <$ char '2')
    index = SIndex <$> L.decimal
    named = SNamed <$> pIdent

pArg :: Parser (Either SProjType (Either SLevel (Either Name Icit, Surface)))
pArg = proj <|> abs <|> level <|> try implByName <|> impl <|> arg
  where
    impl = Right . Right . (Right Impl,) <$> braces pSurface

    level = Right . Left <$> angled pLevel

    arg = Right . Right . (Right Expl,) <$> pAtom

    abs = Right . Right . (Right Expl,) <$> pLam

    proj = Left <$> pProj

    implByName = braces $ do
      x <- pIdent
      char '='
      t <- pSurface
      return $ Right $ Right (Left x, t)

pSpine :: Parser Surface
pSpine = do
  h <- pAtom
  args <- many pArg
  pure $ apps h args
  where
    apps :: Surface -> [Either SProjType (Either SLevel (Either Name Icit, Surface))] -> Surface
    apps t [] = t
    apps t (Left p : as) = apps (SProj t p) as
    apps t (Right (Right (Right Expl, u)) : Left p : as) = apps t (Right (Right (Right Expl, SProj u p)) : as)
    apps t (Right (Right (i, u)) : as) = apps (SApp t u i) as
    apps t (Right (Left l) : as) = apps (SAppLevel t l) as

pLamBinder :: Parser ([Name], Either () (Either Name Icit, Maybe Surface))
pLamBinder = levels <|> implBinder <|> binderWithType <|> justBinder
  where
    -- \x
    justBinder = (\x -> ([x], Right (Right Expl, Nothing))) <$> pBinder

    -- \<x y z>
    levels = angled $ do
      xs <- some pIdent
      return (xs, Left ())

    -- \(x y z : A)
    binderWithType = parens $ do
      xs <- some pBinder
      symbol ":"
      ty <- pSurface
      return (xs, Right (Right Expl, Just ty))
    
    -- \{x y z} | \{x y z : A} | \{x y z = b} | \{x y z : A = b}
    implBinder = braces $ do
      xs <- some pBinder
      ty <- optional (symbol ":" >> pSurface)
      b <- optional (symbol "=" >> pBinder)
      return $ maybe (xs, Right (Right Impl, ty)) (\b -> (xs, Right (Left b, ty))) b

pLam :: Parser Surface
pLam = do
  pLambda
  xs <- some pLamBinder
  char '.'
  t <- pSurface
  pure (foldr go t xs)
  where
    go :: ([Name], Either () (Either Name Icit, Maybe Surface)) -> Surface -> Surface
    go (xs, Left ()) t = foldr SAbsLevel t xs
    go (xs, Right (i, a)) t = foldr (\x t -> SAbs x i a t) t xs

pArrowOrCross :: Parser Bool
pArrowOrCross = (True <$ pArrow) <|> (False <$ pCross)

pPiSigmaBinder :: Parser ([Name], Either () (Icit, Surface))
pPiSigmaBinder = levels <|> implBinder <|> binderWithType
  where
    -- (x y z : A)
    binderWithType = parens $ do
      xs <- some pBinder
      symbol ":"
      ty <- pSurface
      return (xs, Right (Expl, ty))

    -- <x y z>
    levels = angled $ do
      xs <- some pIdent
      return (xs, Left ())
    
    -- {x y z} | {x y z : A}
    implBinder = braces $ do
      xs <- some pBinder
      ty <- optional (symbol ":" >> pSurface)
      return (xs, Right (Impl, fromMaybe (SHole Nothing) ty))

pPiOrSigma :: Parser Surface
pPiOrSigma = do
  dom <- some pPiSigmaBinder
  ty <- pArrowOrCross
  cod <- pSurface
  pure $ foldr (go ty) cod dom
  where
    tyfun ty x i a b = if ty then SPi x i a b else SSigma x a b

    go :: Bool -> ([Name], Either () (Icit, Surface)) -> Surface -> Surface
    go ty (xs, Left ()) t = foldr SPiLevel t xs
    go ty (xs, Right (i, a)) t = foldr (\x t -> tyfun ty x i a t) t xs

funOrSpine :: Parser Surface
funOrSpine = do
  sp <- pSpine
  optional pArrowOrCross >>= \case
    Nothing -> pure sp
    Just b -> (if b then SPi "_" Expl else SSigma "_") sp <$> pSurface

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
