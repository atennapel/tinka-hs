module Parser (parseStr, parseStdin) where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Foldable
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
withPos ptm = do
  pos <- getSourcePos
  ptm >>= \case
    t@SPos{} -> pure t
    t          -> pure (SPos pos t)

lexeme     = L.lexeme ws
symbol s   = lexeme (C.string s)
char c     = lexeme (C.char c)
parens p   = char '(' *> p <* char ')'
braces p   = char '{' *> p <* char '}'
pArrow     = symbol "→" <|> symbol "->"
pProd      = symbol "**" <|> symbol "×"
pBind      = pIdent <|> symbol "_"

keyword :: String -> Bool
keyword x = x == "let" || x == "λ" || x == "U"

pIdent :: Parser Name
pIdent = try $ do
  x  <- C.letterChar
  xs <- takeWhileP Nothing (\c -> isAlphaNum c || c == '\'')
  guard (not (keyword (x:xs)))
  (x:xs) <$ ws

pKeyword :: String -> Parser ()
pKeyword kw = do
  C.string kw
  (takeWhileP Nothing (\c -> isAlphaNum c || c == '\'') *> empty) <|> ws

pAtom :: Parser Surface
pAtom  =
      withPos (    (SVar  <$> pIdent)
               <|> (SU    <$  char 'U')
               <|> (SHole <$  char '_'))
  <|> parens pSurface

goProj :: Surface -> Parser Surface
goProj t =
  (char '.' *>
    (     ((char '₁' <|> char '1') *> goProj (SProj t Fst))
      <|> ((char '₂' <|> char '2') *> goProj (SProj t Snd))
      -- <|> do {x <- pIdent; goProj (ProjField t x)}
    )
  )
  <|> pure t

pProjExp :: Parser Surface
pProjExp = goProj =<< pAtom

pArg :: Parser (Either Name (), Surface)
pArg =  try (braces $ do { x <- pIdent; char '='; t <- pSurface; pure (Left x, t) })
    <|> ((Right (),) <$> (char '{' *> pSurface <* char '}'))
    <|> ((Right (),) <$> pProjExp)

pApp :: Parser Surface
pApp = do
  h <- pProjExp
  args <- many pArg
  pure $ foldl' (\t (i, u) -> SApp t u) h args

pSigmaExp :: Parser Surface
pSigmaExp = do
  optional (try (char '(' *> pBind <* char ':')) >>= \case
    Nothing -> do
      t <- pApp
      (SSigma "_" t <$> (pProd *> pSigmaExp)) <|> pure t
    Just x -> do
      a <- pSurface
      char ')'
      pProd
      SSigma x a <$> pSigmaExp

pLamBinder :: Parser (Name, Maybe Surface, Either Name ())
pLamBinder =
      parens ((,,Right ()) <$> pBind <*> optional (char ':' *> pSurface))
  <|> ((,Nothing,Right ()) <$> pBind)
  <|> try ((,,Right ()) <$> (char '{' *> pBind) <*> (optional (char ':' *> pSurface) <* char '}'))
  <|> braces (do {x <- pIdent; char '='; y <- pBind; ann <- optional (char ':' *> pSurface); pure (y, ann, Left x)})

pLam :: Parser Surface
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pLamBinder
  char '.'
  t <- pLamLet
  pure $ foldr (\(x, ann, ni) u -> SAbs x ann u) t xs

pPiBinder :: Parser ([Name], Surface)
pPiBinder =
      braces ((,) <$> some pBind
                  <*> ((char ':' *> pSurface) <|> pure SHole))
  <|> parens ((,) <$> some pBind
                  <*> (char ':' *> pSurface))

pPiExp :: Parser Surface
pPiExp = do
  optional (try (some pPiBinder)) >>= \case

    Nothing -> do
      t <- pSigmaExp
      (pArrow *> (SPi "_" t <$> pPiExp)) <|> pure t

    Just bs -> do
      case bs of
        [([x], a)] ->
              (SPi x a <$> (pArrow *> pPiExp))
          <|> (do dom <- SSigma x a <$> (pProd *> pSigmaExp)
                  (SPi "_" dom <$> (pArrow *> pPiExp)) <|> pure dom)

        dom -> do
          pArrow
          b <- pPiExp
          pure $! foldr' (\(xs, a) t -> foldr' (`SPi` a) t xs) b dom

pLet :: Parser Surface
pLet = do
  pKeyword "let"
  x <- pIdent
  ann <- optional (char ':' *> pSurface)
  char '='
  t <- pSurface
  symbol ";"
  SLet x ann t <$> pLamLet

pLamLet :: Parser Surface
pLamLet = withPos (pLam <|> pLet <|> pPiExp)

pSurface :: Parser Surface
pSurface = withPos $ do
  t <- pLamLet
  (SPair t <$> (char ',' *> pSurface)) <|> pure t

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
