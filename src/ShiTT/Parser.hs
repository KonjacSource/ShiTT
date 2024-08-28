{-# HLINT ignore #-}
module ShiTT.Parser where 

import Control.Applicative hiding (many, some)
import Control.Monad (void, guard, join)
import Data.Void
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Reader

import qualified ShiTT.Decl as D
import ShiTT.Context
import ShiTT.Syntax
import qualified Data.Map as M
import Data.Char
import ShiTT.Check
import ShiTT.Eval
import ShiTT.Inductive
import Debug.Trace (trace)
import Data.Maybe (fromJust)
import Data.IORef


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
isPatVar name pvs = '-':name `elem` pvs


inCtx :: Name -> Parser Bool 
inCtx name = do 
  ctx <- getCtx 
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

pVar :: Parser Raw 
pVar = do 
  name <- pIdent
  pvs <- ask.!pvs
  if isPatVar name pvs then 
    pure $ RPVar $ '-' : name 
  else pure $ RRef name

pAtom :: Parser Raw 
pAtom = withPos (try pVar <|> (RU <$ symbol "U") <|> (Hole <$ symbol "_"))
    <|> parens pTerm

pTerm :: Parser Raw 
pTerm = withPos (pLam <|> pLet <|> try pPi <|> pFunOrSpine)

withPos :: Parser Raw -> Parser Raw
withPos p = SrcPos <$> getSourcePos <*> p

pArg :: Parser (BindKind, Raw)
pArg =  (try $ braces $ do {x <- pIdent; char '='; t <- pTerm; pure (Named x, t)})
    <|> ((Unnamed Impl,) <$> (char '{' *> pTerm <* char '}'))
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
  <|> braces (do {x <- pIdent; char '='; y <- pBind; pure (y, Named x)})


pLam :: Parser Raw
pLam = do
  char 'λ' <|> char '\\'
  xs <- some pLamBinder
  char '.'
  t <- pTerm
  pure $ foldr (uncurry RLam) t xs

pPiBinder :: Parser ([Name], Raw, Icit)
pPiBinder =
      braces ((,,Impl) <$> some pBind
                       <*> ((char ':' *> pTerm) <|> pure Hole))
  <|> parens ((,,Expl) <$> some pBind
                       <*> (char ':' *> pTerm))
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
  ann <- optional (char ':' *> pTerm)
  char '='
  t <- pTerm
  symbol ";"
  u <- pTerm
  pure $ RLet x (maybe Hole id ann) t u

-------------------

-- | This will change the current context.
pTelescope' :: Parser Telescope
pTelescope' = do 
  res <- (pPiBinder >>= pure . Just) <|> pure Nothing
  case res of 
    Nothing -> pure []
    Just (names, ty_r, i) -> do 
      ctx <- getCtx 
      ty_t <- liftIO $ check ctx ty_r VU -- TODO : use `catch`, better error message
      let ty_v = eval ctx ty_t
      let ctx' = ctx <: (map (:! (ty_v, Source)) names)
      setCtx ctx'
      rest <- pTelescope' 
      pure $ (map (\n -> (n,i,ty_v)) names) ++ rest

-- | This keep the current context.
pTelescope :: Parser Telescope
pTelescope = keepCtx pTelescope'

{- 
`data` Name Telescope `:` Telescope `->` `U` `where`
many (
`|` Name : Telescope `->` `...` (many Term)
)
-}

-- | This will change the context:
--   - add the data name to ctx defined name 
--   - add the data's type message to ctx
--   - add the data parameters (not indexes) to ctx
pDataHeader :: Parser (Name, Telescope, Telescope)
pDataHeader = do
  _

pData :: Parser Data
pData = undefined

--- 

-- emptyCfg :: IO Config 
-- emptyCfg = do 
--   _

-- runParser :: Parser a -> String -> String -> IO (Either String a)
-- runParser p fp src = do 
--   let m = runParserT (p <* eof) fp src in 
--   case fst r of 
--     Left e -> Left $ errorBundlePretty e 
--     Right a -> Right a 