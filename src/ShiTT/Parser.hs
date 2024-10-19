{-# HLINT ignore #-}
module ShiTT.Parser where 

import Control.Applicative hiding (many, some)
import Control.Monad (void, guard, when, forM_)
import Data.Void
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Reader
import ShiTT.CheckFunction
import qualified ShiTT.Decl as D
import ShiTT.Decl (Rhs(Rhs, NoMatchFor))
import ShiTT.Context
import ShiTT.Syntax
import Data.Char
import ShiTT.Check
import ShiTT.Eval
import Data.IORef
import Control.Category ((>>>))
import Control.Exception hiding (try)
import ShiTT.Meta (allSolved, reset, withoutKRef, allUnmatchableTypes, wildcardRef, patternCounterRef)
import Data.List (dropWhileEnd)
import System.IO
import ShiTT.Termination.Call (MutualSet)
import qualified Data.Set as S
import ShiTT.Termination.Check

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

addData :: Data -> Parser () 
addData dat = do 
  ctx <- getCtx 
  setCtx $ ctx { decls = insertData dat ctx.decls }

addFun :: Fun -> Parser () 
addFun fun = do 
  ctx <- getCtx 
  setCtx $ ctx { decls = insertFun fun ctx.decls }

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
patVar name = Var name

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
            , "unmatchable", "axiom", "mutual", "begin", "end", "partial" ]

pIdent :: Parser Name
pIdent = do
  x <- takeWhile1P Nothing isAlphaNum
  guard $ x `notElem` keywords
  x <$ sc

wildcard :: Parser Name 
wildcard = do
  symbol "_" 
  cnt_val <- liftIO $ readIORef wildcardRef 
  liftIO $ writeIORef wildcardRef (cnt_val + 1)
  pure $ "_!" ++ show cnt_val


parens p   = symbol "(" *> p <* symbol ")"
braces p   = symbol "{" *> p <* symbol "}"
braket p   = symbol "[" *> p <* symbol "]"
arrow     = symbol "→" <|> symbol "->"
pBind      = (symbol "auto" >> pure "_") <|> pIdent <|> wildcard
strLit = char '\"' *> manyTill L.charLiteral (char '\"')

pVar :: Parser Raw 
pVar = do 
  name <- pIdent
  pvs <- ask.!pvs
  pure $ RRef name

pAtom :: Parser Raw 
pAtom = withPos (try pVar <|> (RU <$ symbol "U") <|> (Hole <$ (wildcard <|> symbol "auto")))
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


----------------------------------------------------------------------------------------------------

checkType :: Raw -> VType -> Parser Term
checkType v t = do 
  ctx <- getCtx 
  res <- liftIO $ do 
      (check ctx v t >>= pure . Right) 
    `catch` \(Error ctx' elab_err) -> pure $ Left (ctx', elab_err) 
  case res of 
    Right ty -> pure ty 
    Left (ctx', elab_err) -> fail $ show ctx' ++ "\n" ++ show (Error ctx' elab_err)

inferType :: Raw -> Parser (Term, VType)
inferType v = do 
  ctx <- getCtx 
  res <- liftIO $ do 
      (infer ctx v >>= pure . Right) 
    `catch` \(Error ctx' elab_err) -> pure $ Left (show elab_err) 
  case res of 
    Right ty -> pure ty 
    Left err -> fail err


-- | This will change the current context.
pTelescope' :: Parser Telescope
pTelescope' = do 
  res <- (pPiBinder >>= pure . Just) <|> pure Nothing
  case res of 
    Nothing -> pure []
    Just (names, ty_r, i) -> do 
      ctx <- getCtx 
      ty_t <- checkType ty_r VU
      let ty_v = eval ctx ty_t
      let ctx' = ctx <: (map (:! (ty_v, Source)) names)
      setCtx ctx'
      rest <- pTelescope' 
      pure $ (map (\n -> (n,i,ty_t)) names) ++ rest

-- | This keep the current context.
pTelescope :: Parser Telescope
pTelescope = keepCtx pTelescope'

-- data type
-----------------

{- 
Data ::= 

  `data` Name Telescope' `:` Telescope `->` `U` `where`
  many (
  `|` Name : Telescope `->` `...` (many UnnamedArg) 
  )

Each constructor must give all indexes.
-}

-- | This will change the context:
--   - add the data name to ctx defined name.
--   - add the data's type message to ctx (A fake definition, a Data object without Constructors).
--   - add the data parameters (not indexes) to ctx.
--   Then return the fake definition.
pDataHeader :: Parser Data
pDataHeader = do
  isUnmatchable <- (symbol "unmatchable" >> pure True) <|> pure False 
  data_name <- (symbol "data" <|> symbol "inductive") >> pIdent
  
  when isUnmatchable $ do 
    liftIO $ modifyIORef allUnmatchableTypes (data_name:)

  isFresh data_name
  data_para <- pTelescope' -- Adding data parameters to context.
  data_ix <- symbol ":" >> pTelescope 
  if null data_ix then 
    symbol "U" >> symbol "where" 
  else 
    arrow >> symbol "U" >> symbol "where"
  let fake_data = Data 
        { dataName = data_name 
        , dataPara = data_para 
        , dataIx = data_ix 
        , dataCons = []
        }
  addData fake_data
  pure fake_data


-- | No named argument.
pUnnamedArg :: Parser (Raw, Icit)
pUnnamedArg = ((, Impl) <$> (braces pTerm))
          <|> ((, Expl) <$> pAtom)

checkSpine :: [(Raw, Icit)] -> Telescope -> Parser [(Term, Icit)] 
checkSpine xs ps = case (xs, ps) of 
  ([], []) -> pure [] 
  ((x, i):xs, (_, i', t):ps) 
    | i == i' -> do 
      ctx <- getCtx
      x' <- checkType x (eval ctx t) 
      rest <- checkSpine xs ps
      pure $ (x', i) : rest
    | otherwise -> fail $ show $ IcitMismatch i i'
  _ -> fail "Number of arguments unmatch, did you apply too many or too few arguments?" 

pConstructor :: Data -> Parser Constructor
pConstructor dat = do 
  con_name <- bar >> pIdent 
  isFresh con_name
  -- parse under the con_pare
  ctx <- getCtx 
  keepCtx do 
    con_para <- symbol ":" >> pTelescope' 
    if null con_para then 
      symbol "..."
    else 
      arrow >> symbol "..."
    ret_ix_r <- many pUnnamedArg 
    ret_ix_t <- checkSpine ret_ix_r dat.dataIx
    pure $ Constructor
      { conName = con_name
      , belongsTo = dat.dataName
      , conPara = con_para
      , retIx = ret_ix_t
      }

-- | This does not change the context
pData :: Parser Data
pData = keepCtx do 
  header <- pDataHeader 
  cons <- many (pConstructor header)
  pure $ header { dataCons = cons }

-- function 
-------------

{-
ExplPattern ::= Var | Con (many Pattern) | paren (ExplPattern)

Pattern ::= `{`ExplPattern`}` | `{` Id = ExplPattern `}` | ExplPattern
-}

genPatVar :: Parser Name 
genPatVar = do 
  pvs <- ask.!pvs
  pure $ freshName' pvs "_pat_var_"

pExplPattern :: Parser (Pattern, PatVars) 
pExplPattern = choice [parens pExplPattern, try var_pat, con_pat]
  where 
    con_pat = do -- Constructor Pattern
      con_name <- pIdent
      ctx <- getCtx
      case lookupCon' con_name ctx of 
        Nothing -> empty
        Just (_, con) -> do 
          if null con.conPara then 
            pure (PCon con_name [] Expl, [])
          else do
            (args, names) <- pPatterns con.conPara
            pure (PCon con_name args Expl, names)
    var_pat = do -- Variable Pattern
      x <- pBind
      ctx <- getCtx 
      guard $ x `notElem` ctx.decls.definedNames
      x <- case x of 
        "_" -> genPatVar
        _ -> do 
          pvs <- ask.!pvs 
          when (x `elem` pvs) $ fail $ "Duplicate pattern variable: " ++ x
          pure x
      pure (PVar x Expl, [x])

pPattern :: Parser ((Pattern, Maybe Name), PatVars) 
pPattern = choice 
  [ try $ braces do
      name <- pIdent <* symbol "="
      (pat, pvs) <- pExplPattern 
      pure ((setIcit Impl pat, Just name), pvs)
  , braces do 
      (pat, pvs) <- pExplPattern 
      pure ((setIcit Impl pat, Nothing), pvs)
  , do 
      (pat, pvs) <- pExplPattern 
      pure ((pat, Nothing), pvs)
  ]

-- | Parse patterns but do not insert any.
manyPattern :: PatVars -> Parser ([(Pattern, Maybe Name)], PatVars)
manyPattern pvs = withPV pvs do 
  now <- (pPattern >>= pure . Just) <|> pure Nothing 
  case now of 
    Nothing -> pure ([], [])
    Just (pat, pvs') -> do 
      (pats, pvs'') <- manyPattern (pvs' ++ pvs)
      pure (pat:pats, pvs' ++ pvs'')

-- | This will insert the omitted patterns
pPatterns :: Telescope -> Parser ([Pattern], PatVars)
pPatterns ts = do
  (given_pat, pvs) <- manyPattern []
  let newPat x n = PVar ("-" ++ x ++ show n) Impl
  let insertUntilName n ts name = case ts of 
        [] -> fail . show $ NoNamedImplicitArg name
        ts@((x, Impl, _):_) | x == name -> pure ([], ts)
        ((x,_,_): rest) -> do
          (ps, rest') <- insertUntilName (n + 1) rest name
          pure (newPat x n : ps, rest')

  let go :: Int -> Telescope -> [(Pattern, Maybe Name)] -> Parser [Pattern]
      go n ts ps = case (ts, ps) of 
        ([], []) -> pure []

        ((x,i,t):ts, (p,Nothing):ps) | i == icit p -> do
          rest <- go (n+1) ts ps 
          pure $ p : rest
        
        ((x,Impl,t):ts, ps@((p, Nothing):_)) | icit p == Expl -> do -- Insert Implict Pattern 
          rest <- go (n+1) ts ps 
          pure $ newPat x n : rest
        
        (ts@((x,Impl,t):ts'), ps@((p, Just x'):ps')) -- Named Pattern
          | x == x' -> do 
              rest <- go (n+1) ts' ps'
              pure $ p : rest
          | otherwise -> do 
              (pats, rest_ts) <- insertUntilName n ts x'
              rest <- go (n + length pats) rest_ts ps
              pure $ pats ++ rest

        _ -> fail $ "Unable to parse patterns: " ++ show ts ++ " | " ++ show ps
  n <- liftIO $ readIORef patternCounterRef
  liftIO $ writeIORef patternCounterRef (n + length ts + 1)
  ps <- go n ts given_pat
  pure (ps, pvs)

{-
Function ::= 

  `fun` Name Telescope `:` Term `where`
  many (
  `|` Patterns Rhs 
  )

-- Note that we check Rhs under the pattern variables given by patterns.

Rhs ::= `nomatch` Id | `=` Term
-}

pRhs :: Parser Rhs 
pRhs = do 
  choice 
    [ do 
        x <- symbol "!@" >> pIdent
        pvs <- ask.!pvs
        guard $ x `elem` pvs 
        pure (NoMatchFor x)
    , do 
        rhs <- symbol "=" >> pTerm 
        pure (Rhs rhs)
    ]

pClause :: Telescope -> Parser D.Clause 
pClause ts = do 
  (pats, pvs) <- bar >> liftIO (writeIORef patternCounterRef 0) 
                     >> pPatterns ts
  ctx <- getCtx
  rhs <- withPV pvs pRhs
  pure $ D.Clause
    { D.patterns = pats 
    , D.clauseRhs = rhs 
    }

-- | Parse the function header, return a fake definition
pFunHeader :: Parser D.Fun 
pFunHeader = keepCtx do 
  fun_name <- (symbol "fun" <|> symbol "def") >> pIdent 
  isFresh fun_name
  fun_para <- pTelescope' <* symbol ":" 
  ret_ty_r <- pTerm <* (symbol "where" <|> pure "")
  ret_ty_t <- checkType ret_ty_r VU 
  pure $ D.Fun
    { D.funName = fun_name 
    , D.funPara = fun_para
    , D.funRetType = ret_ty_t
    , D.clauses = []
    }

pFun :: Parser D.Fun 
pFun = do 
  preFun <- pFunHeader
  clauses <- many (pClause (D.funPara preFun))
  pure $ preFun { D.clauses = clauses }

-- Parse HIT 
--------------------------
{-
`higher` pDataHeader 
-}

-- | This will change the context
pHDataHeader :: Parser Data 
pHDataHeader = symbol "higher" >> pDataHeader

pHConstructor :: Data -> Parser (Constructor, Maybe D.HConstructor)
pHConstructor dat = do 
  con_name <- bar >> pIdent 
  isFresh con_name 
  -- parse under the con_pare
  ctx <- getCtx 
  keepCtx do 
    con_para <- symbol ":" >> pTelescope' 
    if null con_para then 
      symbol "..." 
    else 
      arrow >> symbol "..."
    ret_ix_r <- many pUnnamedArg 
    ret_ix_t <- checkSpine ret_ix_r dat.dataIx 
    let con = Constructor
              { conName = con_name
              , belongsTo = dat.dataName
              , conPara = con_para
              , retIx = ret_ix_t
              }
    isHCon <- (symbol "when" >> pure True) <|> pure False 
    if isHCon then do 
      pos <- getSourcePos
      let ts = allImpl dat.dataPara ++ con.conPara
      clss <- many $ pClause ts
      pure (con, Just D.HConstructor 
                 { D.hconName = con_name 
                 , D.hconClauses = clss
                 })
    else pure (con, Nothing)


pHData :: Parser (Data, [D.HConstructor])
pHData = keepCtx do 
  header <- pHDataHeader 
  cons <- many (pHConstructor header)
  pure ( header { dataCons = fst <$> cons }
       , filterJust (snd <$> cons)
       ) where filterJust = \case 
                [] -> []
                Just x : xs -> x : filterJust xs 
                Nothing: xs -> filterJust xs 

printLn :: Show t => t -> Parser ()
printLn = liftIO . putStrLn . show

putLn :: String -> Parser ()
putLn = liftIO . putStrLn

checkFunction :: Parser () 
checkFunction = do
    isAxiom <- (symbol "axiom" >> pure True) <|> pure False
    chkTerm <- (symbol "partial" >> pure False) <|> pure True
    fun <- pFun 
    ctx <- getCtx
    pos <- getSourcePos

    checked_fun <- liftIO $ checkFun ctx (not isAxiom) fun 
      `catch` \e -> putStrLn ("In function " ++ fun.funName ++ ":" ++ sourcePosPretty pos) >> case e of  
        PMErr pm -> error (show pm)
        UnifyE u v -> error ("(PatternMatch) Can't unify " ++ show u ++ " with " ++ show v) 
        UsedK -> error "Are you using K?"
        BoundaryMismatch fun_name sp -> error "Boundary Mismatch."
        ConflictName n -> error $ "Don't use the name: " ++ n
    
    -- check termination
    let preFun = Fun
               { funName = fun.funName
               , funPara = fun.funPara
               , funRetType = fun.funRetType
               , funClauses = Nothing
               }
    let term_chk_ctx = ctx { decls = insertFun preFun ctx.decls }
    let mut = S.singleton checked_fun
    when chkTerm do
      if checkTermination term_chk_ctx mut then 
        pure () 
      else do
        putLn $ "I don't know if the following functions terminate: " 
        forM_ mut (putLn . ("- " ++) . show)
        putLn ""
        pure ()

    addFun checked_fun

pMutualBody :: [D.Fun] -> Parser MutualSet
pMutualBody [] = pure S.empty
pMutualBody header = do 
  fun_name <- symbol "fun" >> pIdent 
  let lookup :: [D.Fun] -> [D.Fun] -> Maybe (D.Fun, [D.Fun])
      lookup _ [] = Nothing 
      lookup fore (f:fs)
        | f.funName == fun_name = Just (f, fore ++ fs)
        | otherwise = lookup (fore ++ [f]) fs
  case lookup [] header of 
    Nothing -> error $ "The funcion " ++ fun_name ++ " should not define in mutual block."
    Just (fun_header, rest_headers) -> do  

      clauses <- many (pClause (D.funPara fun_header))
      let raw_fun = fun_header { D.clauses = clauses }
      ctx <- getCtx
      pos <- getSourcePos
      checked_fun <- liftIO $ checkFun ctx True raw_fun 
        `catch` \e -> putStrLn ("In function " ++ raw_fun.funName ++ ":" ++ sourcePosPretty pos) >> 
          case e of  
            PMErr pm -> error (show pm)
            UnifyE u v -> error ("(PatternMatch) Can't unify " ++ show u ++ " with " ++ show v) 
            UsedK -> error "Are you using K?"
            BoundaryMismatch fun_name sp -> error "Boundary Mismatch."
            ConflictName n -> error $ "Don't use the name: " ++ n
      addFun checked_fun
      rest <- pMutualBody rest_headers
      pure $ S.insert checked_fun rest

pMutual :: Parser () 
pMutual = do 
  chkTerm <- (symbol "partial" >> pure False) <|> pure True
  raw_headers <- symbol "mutual" >> many pFunHeader <* symbol "begin"
  let mkFun fun = Fun
        { funName = fun.funName
        , funPara = fun.funPara
        , funRetType = fun.funRetType
        , funClauses = Nothing
        }
  let headers = mkFun <$> raw_headers
  mapM_ addFun headers
  -- This is the context for checking, the evaluation of the defining functions would stuck.
  term_chk_ctx <- getCtx
  mut <- pMutualBody raw_headers <* symbol "end"  
  
  -- check termination
  when chkTerm do
    if chkTerm && checkTermination term_chk_ctx mut then 
      pure () 
    else do
      putLn $ "I don't know if the following functions terminate: " 
      forM_ mut (putLn . ("- " ++) . show)
      putLn ""
      pure ()

pTopLevel :: Parser () 
pTopLevel = choice [data_type, checkFunction, pMutual, command] where 

  data_type = do 
    dat <- pData
    addData dat

  command = symbol "#" >> do
    cmd <- pIdent
    case cmd of 
      "infer" -> do 
        term <- pTerm 
        (_, t) <- inferType term 
        printLn t
      "eval" -> do 
        term <- pTerm 
        (t, _) <- inferType term 
        ctx <- getCtx
        printLn . refresh ctx $ eval ctx t
      "withoutK" -> do 
        liftIO $ writeIORef withoutKRef True
      "withK" -> do 
        liftIO $ writeIORef withoutKRef False
      "load" -> do 
        fp <- strLit <* sc
        putLn $ "Loading: " ++ fp
        _ <- runWithCtx fp 
        pure ()

      _ -> fail $ "Unknown command " ++ cmd
    

pProg :: Parser Context 
pProg = sc >> do
  many pTopLevel
  all_solved <- liftIO allSolved
  if all_solved then 
    putLn "All Done."
  else 
    putLn "Warning: Unsolved meta variables"
  ctx <- getCtx
  pure ctx

pProgWithCfg :: Parser Config 
pProgWithCfg = sc >> do
  many pTopLevel
  all_solved <- liftIO allSolved
  when (not all_solved) $ 
    putLn "Warning: Unsolved meta variables"
  ask

-- Runners
--------------------- 

emptyCfg :: IO Config 
emptyCfg = do 
  ref <- newIORef emptyCtx 
  pure Config
    { ctx = ref 
    , pvs = []
    }

-- for test
-- testCfg :: IO Config 
-- testCfg = do 
  -- ref <- newIORef testContext2
  -- pure Config
    -- { ctx = ref 
    -- , pvs = ["t"]
    -- }

fromFileWith :: Parser a -> Config -> String -> IO a
fromFileWith p cfg fp = do
  src <- readFile fp 
  m <- runReaderT (runParserT (p <* eof) fp src) cfg
  ctx <- readIORef cfg.ctx
  case m of 
    Left err -> error $ errorBundlePretty err
    Right a -> pure a

data ReplErr = ReplErr String 
  deriving Exception

instance Show ReplErr where 
  show (ReplErr s) = s

fromStrWith :: Parser a -> Config -> String -> IO a
fromStrWith p cfg src = do
  m <- runReaderT (runParserT (p <* eof) "stdin" src) cfg
  ctx <- readIORef cfg.ctx
  case m of 
    Left err -> throwIO . ReplErr $ errorBundlePretty err
    Right a -> pure a


fromFile :: Parser a -> String -> IO a
fromFile p fp = do
  src <- readFile fp 
  cfg <- emptyCfg
  m <- runReaderT (runParserT (p <* eof) fp src) cfg
  ctx <- readIORef cfg.ctx
  case m of 
    Left err -> error $ errorBundlePretty err
    Right a -> pure a

-- fromFileTest :: Parser a -> String -> IO a
-- fromFileTest p fp = do
--   src <- readFile fp 
--   cfg <- testCfg
--   m <- runReaderT (runParserT p fp src) cfg
--   ctx <- readIORef cfg.ctx
--   case m of 
--     Left err -> error $ errorBundlePretty err
--     Right a -> pure a

run :: String -> IO () 
run fp = reset >> fromFile pProg fp >> pure ()

runWithCtx :: String -> Parser Context
runWithCtx fp = do 
  cfg <- ask 
  liftIO $ fromFileWith pProg cfg fp  

-- runTest :: String -> IO ()
-- runTest fp = reset >> fromFileTest pProg fp >> pure ()

readLine :: IO (Maybe String)
readLine = do
  putStr "shitt> " >> hFlush stdout
  (trim -> line) <- getLine 
  if line == ";;" then 
      pure Nothing
  else 
      pure $ Just line 
  where 
    trim = dropWhileEnd isSpace . dropWhile isSpace

readLines :: IO String 
readLines = go "" 
  where 
    go pre = do 
      line <- readLine
      case line of 
        Nothing -> pure pre 
        Just line -> go (pre ++ "\n" ++ line)

readTopIO :: Config -> IO Config
readTopIO cfg = do 
  lines <- readLines
  fromStrWith pProgWithCfg cfg lines
    `catch` \(ReplErr e) -> putStrLn e >> pure cfg
  

repl :: IO ()
repl = do 
  cfg <- emptyCfg
  go cfg 
  where 
    go cfg = do 
      cfg' <- readTopIO cfg 
      go cfg'