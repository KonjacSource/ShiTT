-- | Parser single term. This is for test.
module ShiTT.TermParser where 

import Control.Applicative hiding (many, some)
import Control.Monad (void, guard, when)
import Data.Void
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Reader

import ShiTT.Context
import ShiTT.Syntax
import Data.Char
import Data.IORef
import Control.Category ((>>>))
import ShiTT.Meta


type PatVars = [Name]

data Config = Config 
  { ctx :: IORef Context
  , pvs :: PatVars 
  } 

type Parser = ParsecT Void String (ReaderT Config IO)

infixl 9 .!
(.!) :: Monad m => m t -> (t -> b) -> m b
(.!) a f = do 
  x <- a 
  pure (f x)

getCtx :: Parser Context 
getCtx = do 
  cfg <- ask 
  ctx <- liftIO $ readIORef cfg.ctx
  pure ctx 

setCtx :: Context -> Parser () 
setCtx ctx' = do 
  ctx_ref <- ask.!ctx 
  liftIO $ writeIORef ctx_ref ctx'

addName :: Name -> Parser () 
addName name = do 
  ctx <- getCtx
  setCtx $ ctx { decls = ctx.decls { definedNames = name : ctx.decls.definedNames } }

isFresh :: Name -> Parser () 
isFresh name = do 
  names <- getCtx.!(decls >>> definedNames)
  when (name `elem` names) do 
    fail $ name ++ " already defined."
  
keepCtx :: Parser a -> Parser a 
keepCtx p = do 
  ctx <- getCtx
  t <- p 
  setCtx ctx 
  pure t 

withPV :: PatVars -> Parser a -> Parser a 
withPV pvs' = local (\cfg -> cfg { pvs = pvs' })

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
isPatVar name pvs = name `elem` pvs


inCtx :: Name -> Parser Bool 
inCtx name = do 
  ctx <- getCtx 
  pure $ name `elem` ctx.decls.definedNames


keywords :: [String]
keywords =  [ "U", "let", "in", "fun", "λ"
            , "data", "where", "def", "fun"
            , "nomatch", "auto", "traceContext"
            , "inductive", "higher", "when"
            , "unmatchable", "axiom" ]

pIdent :: Parser Name
pIdent = do
  x <- takeWhile1P Nothing isAlphaNum
  guard $ x `notElem` keywords
  x <$ sc

parens p   = symbol "(" *> p <* symbol ")"
braces p   = symbol "{" *> p <* symbol "}"
braket p   = symbol "[" *> p <* symbol "]"
arrow     = symbol "→" <|> symbol "->"
pBind      = (symbol "auto" >> pure "_") <|> pIdent <|> symbol "_"

pVar :: Parser Raw 
pVar = do 
  name <- pIdent
  pvs <- ask.!pvs
  if isPatVar name pvs then 
    
    pure $ RRef $ '-' : name 
  else pure $ RRef name

pAtom :: Parser Raw 
pAtom = withPos (try pVar <|> (RU <$ symbol "U") <|> (Hole <$ (symbol "_" <|> symbol "auto")))
    <|> (do 
          t <- symbol "traceContext" >> braket pTerm
          pure $ RPrintCtx t
        )
    <|> parens pTerm

pTerm :: Parser Raw 
pTerm = withPos (pLam <|> pLet <|> try pPi <|> pFunOrSpine )

withPos :: Parser Raw -> Parser Raw
withPos p = SrcPos <$> getSourcePos <*> p

pArg :: Parser (BindKind, Raw)
pArg =  (try $ braces do {x <- pIdent; symbol "="; t <- pTerm; pure (Named x, t)})
    <|> ((Unnamed Impl,) <$> (braces pTerm))
    <|> ((Unnamed Expl,) <$> pAtom)

pSpine :: Parser Raw
pSpine = do
  h <- pAtom 
  args <- many $ pArg 
  pure $ foldl (\t (i, u) -> RApp t u i) h args

pLamBinder :: Parser (Name, BindKind)
pLamBinder =
      ((,Unnamed Expl) <$> pBind)
  <|> try ((,Unnamed Impl) <$> braces pBind)
  <|> braces (do {x <- pIdent; symbol "="; y <- pBind; pure (y, Named x)})


pLam :: Parser Raw
pLam = do
  symbol "λ" <|> symbol "\\"
  xs <- some pLamBinder
  symbol "."
  t <- pTerm
  pure $ foldr (uncurry RLam) t xs

pPiBinder :: Parser ([Name], Raw, Icit)
pPiBinder =
      braces ((,,Impl) <$> some pBind
                       <*> ((symbol ":" *> pTerm) <|> pure Hole))
  <|> parens ((,,Expl) <$> some pBind
                       <*> (symbol ":" *> pTerm))
pPi :: Parser Raw
pPi = do
  dom <- some $ pPiBinder 
  arrow
  cod <- pTerm 
  pure $ foldr (\(xs, a, i) t -> foldr (\x -> RPi x i a) t xs) cod dom

pFunOrSpine :: Parser Raw
pFunOrSpine = do
  sp <- pSpine
  optional arrow >>= \case
    Nothing -> pure sp
    Just _  -> RPi "_" Expl sp <$> pTerm

pLet :: Parser Raw
pLet = do
  symbol "let" <* sc
  x <- pIdent
  ann <- optional (symbol ":" *> pTerm)
  symbol "="
  t <- pTerm
  symbol ";"
  u <- pTerm
  pure $ RLet x (maybe Hole id ann) t u

readTerm :: Context -> String -> Raw 
readTerm ctx str = runIO do 
  r <- newIORef ctx 
  let config = Config r [] 
  res <- runReaderT (runParserT (pTerm <* sc <* eof) "" str) config 
  case res of 
    Left err -> error $ errorBundlePretty err
    Right a -> pure a