{-# HLINT ignore #-}
module ShiTT.Parser where 

import Control.Applicative hiding (many, some)
import Control.Monad (void, guard, join)
import Data.Void
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.State

import qualified ShiTT.Decl as D
import ShiTT.Context
import ShiTT.Syntax
import qualified Data.Map as M
import Data.Char
import ShiTT.Check
import ShiTT.Inductive
import Debug.Trace (trace)
import Data.Maybe (fromJust)


type PatVars = [Name]
type ParserState = State Context 

type Parser = ParsecT Void String ParserState

sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "--")
  (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

bar :: Parser ()
bar = void (symbol "|")

patVar :: Name -> Term
patVar name = Var $ '-' : name

isPatVar :: Name -> PatVars -> Bool
isPatVar name pvs = '-':name `elem` pvs


inCtx :: Name -> Parser Bool 
inCtx name = do 
  ctx <- get 
  pure $ name `elem` ctx.decls.definedNames


keywords :: [String]
keywords = ["U", "let", "in", "fun", "λ", "data", "where", "def", "nomatch"]

pIdent :: Parser Name
pIdent = do
  x <- takeWhile1P Nothing isAlphaNum
  guard $ x `notElem` keywords
  x <$ sc

parens p   = char '(' *> p <* char ')'
braces p   = char '{' *> p <* char '}'
arrow     = symbol "→" <|> symbol "->"
pBind      = pIdent <|> symbol "_"

pVar :: PatVars -> Parser Raw 
pVar pvs = do 
  name <- pIdent
  if isPatVar name pvs then 
    pure $ RPVar $ '-' : name 
  else pure $ RRef name

pAtom :: PatVars -> Parser Raw 
pAtom pvs = withPos (try (pVar pvs) <|> (RU <$ symbol "U") <|> (Hole <$ symbol "_"))
    <|> parens (pTerm pvs)

pTerm :: PatVars -> Parser Raw 
pTerm pvs = withPos (pLam pvs <|> pLet pvs <|> try (pPi pvs) <|> pFunOrSpine pvs)

withPos :: Parser Raw -> Parser Raw
withPos p = SrcPos <$> getSourcePos <*> p

pArg :: PatVars -> Parser (BindKind, Raw)
pArg pvs =  (try $ braces $ do {x <- pIdent; char '='; t <- pTerm pvs; pure (Named x, t)})
    <|> ((Unnamed Impl,) <$> (char '{' *> pTerm pvs <* char '}'))
    <|> ((Unnamed Expl,) <$> pAtom pvs)

pSpine :: PatVars -> Parser Raw
pSpine pvs = do
  h <- pAtom pvs
  args <- many $ pArg pvs
  pure $ foldl (\t (i, u) -> RApp t u i) h args

pLamBinder :: Parser (Name, BindKind)
pLamBinder =
      ((,Unnamed Expl) <$> pBind)
  <|> try ((,Unnamed Impl) <$> braces pBind)
  <|> braces (do {x <- pIdent; char '='; y <- pBind; pure (y, Named x)})


pLam :: PatVars -> Parser Raw
pLam pvs = do
  char 'λ' <|> char '\\'
  xs <- some pLamBinder
  char '.'
  t <- pTerm pvs
  pure $ foldr (uncurry RLam) t xs

pPiBinder :: PatVars -> Parser ([Name], Raw, Icit)
pPiBinder pvs =
      braces ((,,Impl) <$> some pBind
                       <*> ((char ':' *> pTerm pvs) <|> pure Hole))
  <|> parens ((,,Expl) <$> some pBind
                       <*> (char ':' *> pTerm pvs))
pPi :: PatVars ->  Parser Raw
pPi pvs = do
  dom <- some $ pPiBinder pvs
  arrow
  cod <- pTerm pvs
  pure $ foldr (\(xs, a, i) t -> foldr (\x -> RPi x i a) t xs) cod dom

pFunOrSpine :: PatVars -> Parser Raw
pFunOrSpine pvs = do
  sp <- pSpine pvs
  optional arrow >>= \case
    Nothing -> pure sp
    Just _  -> RPi "_" Expl sp <$> pTerm pvs

pLet :: PatVars -> Parser Raw
pLet pvs = do
  symbol "let" <* sc
  x <- pIdent
  ann <- optional (char ':' *> pTerm pvs)
  char '='
  t <- pTerm pvs
  symbol ";"
  u <- pTerm pvs
  pure $ RLet x (maybe Hole id ann) t u

-------------------

pData :: Parser Data
pData = undefined

