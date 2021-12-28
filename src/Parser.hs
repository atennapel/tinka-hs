module Parser (parseStr, parseStrIO, parseStdin, parseStdinDecls, parseStrDeclsIO) where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Void
import System.Exit
import Text.Megaparsec
import Data.Maybe (fromMaybe, isJust, fromJust)

import qualified Text.Megaparsec.Char       as C
import qualified Text.Megaparsec.Char.Lexer as L

import Surface
import Common

type Parser = Parsec Void String

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser STm -> Parser STm
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
keywords = ["let", "λ", "Type", "Con", "Refl"]

invalidOperators :: [String]
invalidOperators = ["->", "**", "\\", ":", "<", ">", "→", "⨯", ".", ",", ";", "=", "_"]

validOperatorSymbols :: String
validOperatorSymbols = "?:<>-*&^%$#@!~'`+|/,._=;"

validIdentSymbols :: String
validIdentSymbols = "?:-*&^%$#@!~'`+|/_"

isValidOperator :: Char -> Bool
isValidOperator c = c `elem` validOperatorSymbols

keyword :: String -> Bool
keyword x = x `elem` keywords

invalidOperator :: String -> Bool
invalidOperator x = x `elem` invalidOperators

isHole :: Name -> Bool
isHole x = head x == '_' && all isAlphaNum (tail x)

pName :: Parser Name
pName = try $ do
  x <- takeWhile1P Nothing (\c -> isAlphaNum c || c `elem` validIdentSymbols)
  guard (not (keyword x) && not (isValidOperator (head x)) && not (isDigit (head x)) && not (isHole x))
  return x

pOperator' :: Parser Name
pOperator' = try $ do
  x <- takeWhile1P Nothing (\c -> isValidOperator c || isAlphaNum c)
  guard (not (invalidOperator x) && not (isAlphaNum (head x)) && not (isHole x) && head x /= '_')
  return x

pIdent :: Parser Name
pIdent = try $ do
  x <- pName
  ws
  return x

pOperator :: Parser Name
pOperator = try $ do
  x <- pOperator'
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
pLevelAtom = try nat <|> var <|> parens pLevel
  where
    var = SLVar <$> pIdent
    nat = SLNat <$> L.decimal

pType :: Parser STm
pType = do
  symbol "Type"
  l <- optional pLevelAtom
  ws
  return $ maybe (SType (SLNat 0)) SType l

pCon :: Parser STm
pCon = do
  symbol "Con"
  SCon <$> pAtom

pCommaSeparated :: Parser [STm]
pCommaSeparated = do
  first <- pSurface
  rest <- optional (do
    symbol ","
    pCommaSeparated)
  return $ maybe [first] (first :) rest

pPair :: Parser STm
pPair = parens (foldr1 SPair <$> pCommaSeparated)

pUnitPair :: Parser STm
pUnitPair = brackets (foldr SPair (SVar "[]") <$> pCommaSeparated)

pHole :: Parser STm
pHole = do
  C.char '_'
  x <- optional (C.string "_") <|> optional (takeWhile1P Nothing isAlphaNum)
  ws
  return $ SHole x

pAtom :: Parser STm
pAtom =
  withPos (
    pHole <|>
    try pType <|>
    (SNatLit <$> (L.decimal <* ws)) <|>
    (SType (SLNat 0) <$ symbol "Type") <|>
    (SRefl <$ symbol "Refl") <|>
    (SVar <$> pIdent))
  <|> pCon
  <|> try (SVar "()" <$ parens ws)
  <|> try (SVar "[]" <$ brackets ws)
  <|> try pPair
  <|> try pUnitPair
  <|> parens pSurface

pBinder :: Parser Name
pBinder = pIdent <|> symbol "_"

pOpBinder :: Parser Name
pOpBinder = parens pOperator <|> pBinder

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

data Sp
  = SpProj SProjType
  | SpLevel SLevel (Maybe Name)
  | SpArg STm (Either Name Icit)
  | SpOp Name
  deriving (Show)

pSp :: Parser Sp
pSp = proj <|> abs <|> try levelByName <|> try level <|> try implByName <|> impl <|> try parensOp <|> try op <|> arg
  where
    -- {t}
    impl = flip SpArg (Right Impl) <$> braces pSurface

    -- <t>
    level = flip SpLevel Nothing <$> angled pLevel

    -- t
    arg = flip SpArg (Right Expl) <$> pAtom

    -- \x y z. ...
    abs = flip SpArg (Right Expl) <$> pLam

    -- ._1 ._2 .xx .3
    proj = SpProj <$> pProj

    -- {x = t}
    implByName = braces $ do
      x <- parens pOperator <|> pIdent
      char '='
      t <- pSurface
      return $ SpArg t (Left x)
    
    -- <x = l>
    levelByName = angled $ do
      x <- pIdent
      char '='
      t <- pLevel
      return $ SpLevel t (Just x)
    
    -- operator
    op = SpOp <$> pOperator

    -- operator in parens
    parensOp = flip SpArg (Right Expl) . SVar <$> parens pOperator

prec :: Name -> Int
prec x = go (head x)
  where    
    go '*' = 99
    go '/' = 99
    go '%' = 99

    go '+' = 98
    go '-' = 98

    go ':' = 97

    go '=' = 96
    go '!' = 96
    
    go '<' = 95
    go '>' = 95
    
    go '&' = 94

    go '^' = 93
  
    go '|' = 92
    
    go '$' = 91
    go '_' = 91

    go _ = 999

rightAssoc :: Name -> Bool
rightAssoc x = last x == ':'

pSpine :: Parser STm
pSpine = do
  h <- Left <$> try pOperator <|> Right <$> pAtom
  sp <- many pSp
  let os = ops h sp
  guard (isJust os)
  pure $ shunting (fromJust os)
  where
    shunting :: [Either Name STm] -> STm
    shunting [Left op] = SVar op
    shunting [Left op, Right t] = SApp (SApp (SVar "flip") (SVar op) (Right Expl)) t (Right Expl)
    shunting [Right t, Left op] = SApp (SVar op) t (Right Expl)
    shunting st = stack [] (reverse $ go st [] [])
      where
        go :: [Either Name STm] -> [Either Name STm] -> [Name] -> [Either Name STm]
        go [] out [] = out
        go [] out (op : ops) = go [] (Left op : out) ops
        go (Right t : st) out ops = go st (Right t : out) ops
        go (Left o1 : st) out (o2 : ops) | prec o2 > prec o1 || prec o1 == prec o2 && not (rightAssoc o1) = go (Left o1 : st) (Left o2 : out) ops
        go (Left o1 : st) out ops = go st out (o1 : ops)

        stack :: [STm] -> [Either Name STm] -> STm
        stack (t : _) [] = t
        stack st (Right t : ops) = stack (t : st) ops
        stack (a : b : st) (Left x : ops) = stack (SApp (SApp (SVar x) b (Right Expl)) a (Right Expl) : st) ops
        stack _ _ = undefined

    ops :: Either Name STm -> [Sp] -> Maybe [Either Name STm]
    ops t sp = fmap (map (fmap fromJust) . filter nonEmpty) $ traverse (traverse appsSp) (split (either SpOp (flip SpArg (Right Expl)) t : sp) [])
      where
        nonEmpty :: Either Name (Maybe STm) -> Bool
        nonEmpty (Right Nothing) = False
        nonEmpty _ = True

        split :: [Sp] -> [Sp] -> [Either Name [Sp]]
        split (SpOp x : as) acc = Right (reverse acc) : Left x : split as []
        split (s : as) acc = split as (s : acc)
        split [] acc = [Right (reverse acc)]

        appHead :: Sp -> Maybe STm
        appHead (SpArg t (Right Expl)) = Just t
        appHead _ = Nothing

        apps :: STm -> [Sp] -> STm
        apps t [] = t
        apps t (SpProj p : as) = apps (SProj t p) as
        apps t (SpLevel l x : as) = apps (SAppLvl t l x) as
        apps t (SpArg u (Right Expl) : SpProj p : as) = apps t (SpArg (SProj u p) (Right Expl) : as)
        apps t (SpArg u i : as) = apps (SApp t u i) as
        apps t (SpOp x : as) = apps (SApp (SVar x) t (Right Expl)) as

        appsSp :: [Sp] -> Maybe (Maybe STm)
        appsSp [] = Just Nothing
        appsSp (hd : tl) =
          case appHead hd of
            Just hd' -> Just (Just $ apps hd' tl)
            Nothing -> Nothing

pLamBinder :: Parser ([Name], Either (Maybe Name) (Either Name Icit, Maybe STm))
pLamBinder = levels <|> implBinder <|> try binderWithType <|> justBinder
  where
    -- \x
    justBinder = (\x -> ([x], Right (Right Expl, Nothing))) <$> pOpBinder

    -- \<x y z> | \<x y z = b>
    levels = angled $ do
      xs <- some pIdent
      b <- optional (symbol "=" >> pBinder)
      return (xs, Left b)

    -- \(x y z : A)
    binderWithType = parens $ do
      xs <- some pOpBinder
      symbol ":"
      ty <- pSurface
      return (xs, Right (Right Expl, Just ty))
    
    -- \{x y z} | \{x y z : A} | \{x y z = b} | \{x y z : A = b}
    implBinder = braces $ do
      xs <- some pOpBinder
      ty <- optional (symbol ":" >> pSurface)
      b <- optional (symbol "=" >> pBinder)
      return $ maybe (xs, Right (Right Impl, ty)) (\b -> (xs, Right (Left b, ty))) b

pLam :: Parser STm
pLam = do
  pLambda
  xs <- many pLamBinder
  char '.'
  t <- pSurface
  return $ foldLamBinders t xs
  where

foldLamBinders :: STm -> [([Name], Either (Maybe Name) (Either Name Icit, Maybe STm))] -> STm
foldLamBinders t xs = foldr go t xs
  where
    go :: ([Name], Either (Maybe Name) (Either Name Icit, Maybe STm)) -> STm -> STm
    go (xs, Left i) t = foldr (\x -> SLamLvl x i) t xs
    go (xs, Right (i, a)) t = foldr (\x t -> SLam x i a t) t xs

foldLamBindersUnannotated :: STm -> [([Name], Either (Maybe Name) (Either Name Icit, Maybe STm))] -> STm
foldLamBindersUnannotated t xs = foldr go t xs
  where
    go :: ([Name], Either (Maybe Name) (Either Name Icit, Maybe STm)) -> STm -> STm
    go (xs, Left i) t = foldr (\x -> SLamLvl x i) t xs
    go (xs, Right (i, a)) t = foldr (\x t -> SLam x i Nothing t) t xs

pArrowOrCross :: Parser Bool
pArrowOrCross = (True <$ pArrow) <|> (False <$ pCross)

pPiSigmaBinder :: Parser ([Name], Either () (Icit, STm))
pPiSigmaBinder = levels <|> implBinder <|> binderWithType
  where
    -- (x y z : A)
    binderWithType = parens $ do
      xs <- some pOpBinder
      symbol ":"
      ty <- pSurface
      return (xs, Right (Expl, ty))

    -- <x y z>
    levels = angled $ do
      xs <- some pIdent
      return (xs, Left ())
    
    -- {x y z} | {x y z : A}
    implBinder = braces $ do
      xs <- some pOpBinder
      ty <- optional (symbol ":" >> pSurface)
      return (xs, Right (Impl, fromMaybe (SHole Nothing) ty))

pPiOrSigma :: Parser STm
pPiOrSigma = do
  dom <- some pPiSigmaBinder
  ty <- pArrowOrCross
  cod <- pSurface
  pure $ foldr (go ty) cod dom
  where
    tyfun ty x i a b = if ty then SPi x i a b else SSigma x a b

    go :: Bool -> ([Name], Either () (Icit, STm)) -> STm -> STm
    go ty (xs, Left ()) t = foldr SPiLvl t xs
    go ty (xs, Right (i, a)) t = foldr (\x t -> tyfun ty x i a t) t xs

funOrSpine :: Parser STm
funOrSpine = do
  sp <- pSpine
  optional pArrowOrCross >>= \case
    Nothing -> pure sp
    Just b -> (if b then SPi "_" Expl else SSigma "_") sp <$> pSurface

pLet :: Parser STm
pLet = do
  pKeyword "let"
  x <- pOpBinder
  ps <- many pLamBinder
  a <- optional (do
    symbol ":"
    pSurface)
  symbol "="
  t <- pSurface
  symbol ";"
  SLet x (setupPiForDef ps a) (foldLamBindersUnannotated t ps) <$> pSurface

setupPiForDef :: [([Name], Either (Maybe Name) (Either Name Icit, Maybe STm))] -> Maybe STm -> Maybe STm
setupPiForDef [] Nothing = Nothing
setupPiForDef xs a = Just $ createPiForDef xs (fromMaybe (SHole Nothing) a)

createPiForDef :: [([Name], Either (Maybe Name) (Either Name Icit, Maybe STm))] -> STm -> STm
createPiForDef xs t = foldr go t xs
  where
    go :: ([Name], Either (Maybe Name) (Either Name Icit, Maybe STm)) -> STm -> STm
    go (xs, Left i) t = foldr SPiLvl t xs
    go (xs, Right (i, a)) t = foldr (\x t -> SPi x (either (const Impl) id i) (fromMaybe (SHole Nothing) a) t) t xs

pSurface :: Parser STm
pSurface = withPos (pLam <|> pLet <|> try pPiOrSigma <|> funOrSpine)

pSrc :: Parser STm
pSrc = ws *> pSurface <* eof

parseStr :: String -> IO STm
parseStr src =
  case parse pSrc "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStrEither :: String -> Either String STm
parseStrEither src = case parse pSrc "(stdin)" src of
  Left e -> Left (errorBundlePretty e)
  Right t -> return t

parseStrIO :: String -> IO STm
parseStrIO src = case parseStrEither src of
  Left e -> error e
  Right t -> return t

parseStdin :: IO (STm, String)
parseStdin = do
  src <- getContents
  t <- parseStr src
  pure (t, src)

pDef :: Parser [Decl]
pDef = do
  x <- pOpBinder
  ps <- many pLamBinder
  a <- optional (do
    symbol ":"
    pSurface)
  symbol "="
  t <- pSurface
  return [Def x (setupPiForDef ps a) (foldLamBindersUnannotated t ps)]

pImport :: Parser [Decl]
pImport = do
  symbol "import"
  names <- many (lexeme $ takeWhile1P Nothing (\x -> isAlphaNum x || x == '/' || x == '\\' || x == '.'))
  return $ Import <$> names

pDecl :: Parser [Decl]
pDecl = pImport <|> pDef

pDecls :: Parser Decls
pDecls = do
  ws
  ds <- pDecl
  ws
  symbol ";"
  ws
  dsrest <- pDecls <|> ([] <$ eof)
  return (ds ++ dsrest)

parseStrDecls :: String -> IO Decls
parseStrDecls src =
  case parse pDecls "(stdin)" src of
    Left e -> do
      putStrLn $ errorBundlePretty e
      exitFailure
    Right t ->
      pure t

parseStrDeclsEither :: String -> Either String Decls
parseStrDeclsEither src = case parse pDecls "(stdin)" src of
  Left e -> Left (errorBundlePretty e)
  Right t -> return t

parseStrDeclsIO :: String -> IO Decls
parseStrDeclsIO src = case parseStrDeclsEither src of
  Left e -> error e
  Right t -> return t

parseStdinDecls :: IO (Decls, String)
parseStdinDecls = do
  src <- getContents
  t <- parseStrDecls src
  pure (t, src)
