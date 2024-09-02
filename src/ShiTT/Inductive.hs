{-# HLINT ignore #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE BlockArguments #-}
module ShiTT.Inductive where 

import qualified ShiTT.Decl as R 
import ShiTT.Context 
import qualified ShiTT.Check as C 
import ShiTT.Eval
import qualified Data.Map as M 
import ShiTT.Syntax
import Control.Exception
import Control.Monad (forM)
import Data.Maybe (fromJust, isJust)
import Debug.Trace (trace)
import Control.Monad.Identity (Identity(runIdentity))

match :: Context -> [R.Pattern] -> Spine -> Maybe [Def]
match ctx [] [] = Just [] 
match ctx (p:ps) (p':ps') = do 
  ret <- match1 ctx p p' 
  rest <- match ctx ps ps'
  pure $ ret ++ rest
match _ p sp = error $ "Unmatch : " ++ show p ++ " | " ++ show sp

match1 :: Context -> R.Pattern -> (Value, Icit) -> Maybe [Def]
match1 ctx (R.PVar x i) (force -> v, i') | i == i' = Just $ pure (x := v)
match1 ctx (R.PCon name ps i) (force -> VCon name' ps', i') 
     | i == i' && name == name' = do 
      (dat, con) <- lookupCon' name ctx 
      match ctx ps (drop (length dat.dataPara) ps')
     | otherwise = Nothing 
match1 ctx (R.PInacc _ _) _ = Just []
match1 ctx _ _ = Nothing 

data PMErr 
  = NumOfPatErr 
  | IcitErr Icit Icit
  | UnknownDataName Name 
  | UnknownConNameOfData Name Data 
  | TheGivenTypeIsNotAData Value
  | Matchable Name [R.Pattern]
  deriving Show 

data CheckError = PMErr PMErr
                | UnifyE Value Value
  deriving (Exception, Show)

-- | f : NameOrder
--   f a b is True when the variable a in pattern is shown before b. 
type NameOrder = Name -> Name -> Bool 

-- A var in the back of pattern is actually in the front of list
listOrder :: [Name] -> NameOrder
listOrder [] n m = error "Impossible"
listOrder (x:xs) n m 
  | n == x    = False
  | m == x    = True
  | otherwise = listOrder xs n m 

-- f : Delta    -> T 
-- f   patterns := t
-- (ctx, resultCtx) |- eval (ctx, extraDef) t : eval (ctx, typeLevelDef) T 
data CheckResult = CheckResult
  { resultCtx :: [Bind] 
  , extraDef :: [Def]
  , freevarsRhs :: [Def]
  , typeLevelDef :: [Def]
  } deriving Show 

unionRes :: Context -> CheckResult -> CheckResult -> CheckResult
unionRes ctx a b = CheckResult
  { resultCtx = a.resultCtx ++ b.resultCtx
  , extraDef = updateDef ctx a.extraDef b.extraDef
  , freevarsRhs = a.freevarsRhs ++ b.freevarsRhs
  , typeLevelDef = a.typeLevelDef ++ b.typeLevelDef
  }

refreshSp :: Context -> Spine -> Spine 
refreshSp ctx = \case 
  [] -> []
  ((v,i) : rest) -> (refresh ctx v, i) : refreshSp ctx rest 

refreshTelescope :: Context -> Telescope -> Telescope
refreshTelescope ctx = \case 
  [] -> []
  ((x,i,v) : rest) -> (x, i, refresh ctx v) : refreshTelescope (ctx <: freeVar x) rest 

(^?) :: Maybe a -> CheckError -> Either CheckError a 
Nothing ^? e = Left e 
Just x ^? _ = pure x

execCheck :: Either CheckError a -> IO a 
execCheck (Left e) = throwIO e 
execCheck (Right a) = pure a

-- | ctx |- ps : `conParaType ctx con dat dat_para`
--   where 
--     con {dat_para} ps 
--   is legal
conParaType :: Context -> Constructor -> Data -> Spine -> Telescope
conParaType ctx con dat dat_para = 
  let dat_para' = dat.dataPara 
      sub = map (\((x,_,_), (v,_)) -> x := v) $ zip dat_para' dat_para
  in substTelescope' ctx sub con.conPara

-- Need test
updateDef :: Context -> [Def] -> [Def] -> [Def]
updateDef ctx a b = substDefs' ctx a b ++ substDefs' ctx b a

-- | Check (con ps) agasint type t.
checkCon :: Context 
         -> [Name] -- ^name order
         -> (Constructor, [R.Pattern]) 
         -> (Data, Spine) 
         -> Either CheckError ([Name], Value, CheckResult)
checkCon ctx ord (con, ps) (dat, dat_args) = do 
  let (dat_para, dat_ix) = splitAt (length dat.dataPara) dat_args
  let ps_type = conParaType ctx con dat dat_para
  (ord', psv, res) <- checkP ctx ord ps ps_type
  -- infer the data index 
  let ret_ix = con.retIx (allImpl dat_para ++ psv) 
  -- unify inferred data index with dat_ix  
  defs <- unifySp (listOrder ord') ctx [] ret_ix dat_ix

  pure ( ord'
       , VCon con.conName (allImpl dat_para ++ psv)
       , res { extraDef = updateDef ctx defs res.extraDef, typeLevelDef = [] } ) -- this is a sub check, so we dont need the type level def
  where allImpl = \case 
          [] -> []
          ((v,_) : rest) -> (v, Impl) : allImpl rest
  

-- | checkP ctx [] [(succ n), (cons x xs)] [(m : N), (ls : List N)] ==> 
--   [xs, x, n] ,
--   [(succ n), (cons x xs)] ,
--   CheckResult 
--   { resultCtx = [(n : N), (x : N), (xs : List N)]
--   , typeLevelDef = [(m := succ n), (ls := cons xs)] 
--   } 
checkP :: Context -> [Name] -> [R.Pattern] -> Telescope -> Either CheckError ([Name], Spine, CheckResult)
checkP ctx ord [] [] = pure $ (ord, [], CheckResult [] [] [] [])
checkP ctx ord (p:ps) ((x', i', t'): ts) 
  | R.icit p == i' = 
    let t = refresh ctx t' in
    case p of 
      R.PVar x i -> do 
        let now = CheckResult 
                  { resultCtx    = [x :~ (t, Source)]
                  , extraDef     = []
                  , freevarsRhs  = [x := VPatVar x []]
                  , typeLevelDef = [x' := VPatVar x []]
                  } 
        let ts' = substTelescope' ctx now.typeLevelDef ts
        (ord', psv, rest) <- checkP (ctx <: x := VPatVar x []) (x : ord) ps ts'
        pure (ord', (VPatVar x [], i) : psv, unionRes ctx now rest)
      
      R.PCon con_name con_args i -> 
        case t of 
          VCon dat_name dat_args -> do
            dat <- M.lookup dat_name ctx.decls.allDataDecls ^? (PMErr $ UnknownDataName dat_name)
            con <- lookupCon con_name dat                   ^? (PMErr $ UnknownConNameOfData con_name dat)
            -- check constructor
            (ord', v, now) <- checkCon ctx ord (con, con_args) (dat, dat_args)
            let now' = now {typeLevelDef = (x' := v) : now.typeLevelDef}
            let ts' = substTelescope' ctx (now'.typeLevelDef ++ now'.extraDef) ts
            (ord'', psv, rest) <- checkP (ctx <: now'.resultCtx) ord' ps ts' 
            pure (ord'', (v, i) : psv, unionRes ctx now' rest)

          _ -> Left . PMErr $ TheGivenTypeIsNotAData t

      R.PInacc n _ -> error "Deprecated" 
  | otherwise = Left . PMErr $ IcitErr (R.icit p) i' 
checkP ctx ord _ _ = Left . PMErr $ NumOfPatErr

checkClause :: Context -> R.Fun -> R.Clause -> IO (Maybe (Term, Context))
checkClause ctx fun (R.Clause pat rhs) = case rhs of
  R.NoMatchFor x -> do -- Check absurd pattern
    (_,sp,res) <- execCheck $ checkP ctx [] pat fun.funPara -- here
    case splitCase (ctx <: res.resultCtx <: res.extraDef) (x, Expl, fromJust (getType x res.resultCtx)) of
      Just [] -> pure Nothing 
      Just ps -> throwIO . PMErr $ Matchable x (map (\(x,_,_) -> x) ps)
      Nothing -> throwIO . PMErr $ Matchable x [R.PVar x Expl]
      -- TODO: Test Check absurd pattern
  R.Rhs t -> do
    (_,sp,res) <- execCheck $ checkP ctx [] pat fun.funPara -- here
    let rhs_ctx = ctx <: res.resultCtx <: res.freevarsRhs <: res.extraDef
    let expect_type = refresh rhs_ctx $ fun.funRetType sp 
    rhs <- C.check rhs_ctx t expect_type
    pure $ Just (rhs, rhs_ctx)

-- Turn a clause to a function.
mkFunVal :: Context -> [R.Pattern] -> Term -> (Context -> Spine -> Maybe Value)
mkFunVal ctx ps rhs call_ctx sp = do 
  defs <- match ctx ps sp
  let ctx' = call_ctx <: defs 
  pure $ refresh ctx' $ eval ctx' rhs 

checkClauses :: Context -> R.Fun -> [R.Clause] -> IO (Context -> Spine -> Maybe Value)
checkClauses ctx fun cls = do 
  rhss <- forM cls $ \c -> do 
    rhs <- checkClause ctx fun c
    pure (c.patterns, rhs)

  let patsWithRhsCtx = do 
        (p, t) <- rhss
        case t of 
          Nothing -> [] 
          Just (_,ctx) -> pure (p,ctx)
  -- TODO : Coverage Check

  let vs = map (\(pat, fst . fromJust -> rhs) -> mkFunVal ctx pat rhs) $ filter (isJust . snd) (rhss)
  let go [] = \call_ctx sp -> Nothing 
      go (v:vs) = \call_ctx sp -> case v call_ctx sp of 
        Just r -> Just r
        Nothing -> go vs call_ctx sp 
  pure $ go vs

checkFun :: Context -> R.Fun -> IO Fun 
checkFun ctx fun = do 
  let preFun = Fun 
               { funName = fun.funName 
               , funPara = fun.funPara
               , funRetType = fun.funRetType
               , funVal = \ _ _ -> Nothing -- A fake definition, so that we may check the type of the definning function
               }
  let ctx' =ctx { decls = insertFun preFun ctx.decls }
  val <- checkClauses ctx' fun fun.clauses 
  pure $ preFun { funVal = val }

unify1 :: NameOrder -> Context -> [Def] -> Value -> Value -> Either CheckError [Def]
unify1 ord ctx fore v w = case (force v, force w) of 
  (VPatVar n [], VPatVar m [])
    | m == n    -> pure fore
    | otherwise -> if ord m n then pure $ (n := VRig m []) : fore
                              else pure $ (m := VRig n []) : fore 

  (VPatVar n [], VVar n') | n == n' -> pure fore
  (VVar n', VPatVar n []) | n == n' -> pure fore

  (VPatVar n [], r) | n `notElem` freeVarOf ctx r -> do
    pure $ [n := r] ++ fore

  (l, VPatVar n []) | n `notElem` freeVarOf ctx l -> do 
    pure $ [n := l] ++ fore
  
  (VLam x i t, VLam _ i' t') | i == i' -> let x' = freshName ctx x in 
    unify1 ord (ctx <: freeVar x') fore (t $ VVar x') (t' $ VVar x')
  (VLam x i t, t') -> let x' = freshName ctx x in 
    unify1 ord (ctx <: freeVar x') fore (t (VVar x')) (vApp t' (VVar x') i)
  (t', VLam x i  t ) -> let x' = freshName ctx x in 
    unify1 ord (ctx <: freeVar x') fore (vApp t' (VVar x') i) (t (VVar x'))
  (VPi x i a b, VPi _ i' a' b') | i == i' -> do 
    let x' = freshName ctx x 
    unify1 ord ctx fore a a'
    unify1 ord (ctx <: freeVar x') fore (b (VVar x')) (b' (VVar x'))

  (VCon con sp, VCon con' sp')   | con == con' -> unifySp ord ctx fore sp sp' 
  (VRig n sp, VRig m sp')        | n == m      -> unifySp ord ctx fore sp sp'
  (VFunc fun sp, VFunc fun' sp') | fun == fun' -> unifySp ord ctx fore sp sp' 
  (VFlex m sp, VFlex m' sp')     | m == m'     -> unifySp ord ctx fore sp sp' 
  (VPatVar n sp, VPatVar m sp')  | n == m      -> unifySp ord ctx fore sp sp'

  (v, w) -> Left $ UnifyE v w 
  
unifySp :: NameOrder -> Context -> [Def] -> Spine -> Spine -> Either CheckError [Def]
unifySp ord ctx fore s1 s2 = case (s1, s2) of 
  ([], []) -> pure fore
  ((v, i):vs, (w, i'):ws) | i == i' -> do 
    s <- unify1 ord ctx fore v w
    let vs' = substSp' ctx s vs 
    let ws' = substSp' ctx s ws
    unifySp ord ctx s vs' ws'
  _ -> error "impossible"


-- Coverage Check 
---------------------

data Unmatch 
  = Stucked [([R.Pattern], Spine, CheckResult)] -- Or say: splitted
  -- match x with pattern (succ n)
  | MoveNext 
  -- match nil with pattern (cons x xs)
  deriving Show

-- | Is the pattern availd in the context
availdPattern :: Context -> (Name, Icit, VType) -> R.Pattern -> Maybe ((Value, Icit), CheckResult)
availdPattern ctx t p = case checkP ctx [] [p] [t] of 
  Right (_, s, r) -> pure (head s, r) 
  _ -> Nothing 
  
-- | Generate pattern of given constructor, return used names (in pattern)
mkConPat :: Context -> Data -> Constructor -> Icit -> R.Pattern
mkConPat ctx dat con i = (R.PCon con.conName pargs i) where 
  ixls xs = go 0 xs where 
    go _ [] = [] 
    go n (x:xs) = (x,n) : go (n+1) xs
  names = map (\(x, n) -> freshName ctx (x ++ show n)) (ixls (map (\(x,_,_) -> x) con.conPara))
  pargs = map (\(n, (_,i,_)) -> R.PVar n i) $ zip names con.conPara

-- | Give the expected type, generate all the possible patterns.
splitCase :: Context -> (Name, Icit, VType) -> Maybe [(R.Pattern, (Value, Icit), CheckResult)]
splitCase ctx (x, icit, force -> t) = case t of 
  t@(VCon data_name data_args) ->
    case M.lookup data_name ctx.decls.allDataDecls of 
      Nothing  -> Nothing
      Just dat -> Just do -- List do  

        con <- dat.dataCons
        let conP = mkConPat ctx dat con icit
        case availdPattern ctx (x, icit, t) conP of
          Nothing -> [] 
          Just (v, res) -> pure (conP, v, res)
  
  _ -> Nothing -- only_var
  -- where 
  --   pat_name = freshName ctx "~pat'"
  --   only_var = let (b, c) = fromJust $ availdPattern ctx (x, Impl, t) (R.PVar pat_name icit) in 
  --     [(R.PVar pat_name icit, b, c)]

-- | Is the pattern availd in the context
availdPatternWithInacc :: Context -> (Name, Icit, VType) -> R.Pattern -> Maybe ((Value, Icit), CheckResult)
availdPatternWithInacc ctx t p = case checkP ctx [] [p] [t] of 
  Right (_, s, r) -> pure (head s, r) 
  _ -> Nothing 
  

splitCaseWithInacc :: Context -> (Name, Icit, VType) -> Maybe [(R.Pattern, (Value, Icit), CheckResult)]
splitCaseWithInacc ctx (x, icit, force -> t) = case t of 
  t@(VCon data_name data_args) ->
    case M.lookup data_name ctx.decls.allDataDecls of 
      Nothing  -> Nothing
      Just dat -> Just do -- List do  

        con <- dat.dataCons
        let conP = mkConPat ctx dat con icit
        case availdPattern ctx (x, icit, t) conP of
          Nothing -> [] 
          Just (v, res) -> pure (conP, v, res)
  
  _ -> Nothing -- only_var
  -- where 
  --   pat_name = freshName ctx "~pat'"
  --   only_var = let (b, c) = fromJust $ availdPattern ctx (x, Impl, t) (R.PVar pat_name icit) in 
  --     [(R.PVar pat_name icit, b, c)]

data CoverageError = Fine | Exhausted Name Spine -- Coverage check failed
  deriving (Show, Exception)

coverageCheck :: Context -> Telescope -> [([R.Pattern], Context)] -> IO ()
coverageCheck outer_ctx ts ps = undefined

isInacc :: Context -> Name -> Bool 
isInacc rhs_ctx name = case M.lookup name rhs_ctx.env of 
  Just (VVar x      ) | x == name -> False -- free 
  Just (VPatVar x []) | x == name -> True 
  _ -> True

match' :: Context -> Context -> Telescope -> [R.Pattern] -> Spine -> Either Unmatch [Def] -- the [Def] may not needed
match' tlvl_ctx rhs_ctx ts ps sp =  case (ts, ps, sp) of 
  ([], [], []) -> pure []
  (t:(substTelescope' tlvl_ctx [] -> ts),p:ps,v:sp) -> case match1' tlvl_ctx rhs_ctx t p v of 
    
    Right def -> 
      
      case match' tlvl_ctx rhs_ctx 
                  ts 
                  ps 
                  sp 
        of 
        Right def' -> Right $ def ++ def' 
        Left MoveNext -> Left MoveNext
        Left (Stucked poss_pats) -> Left . Stucked $ do 
          (pat,vs,res) <- poss_pats
          pure $ (p:pat, v:vs, res)
    
    Left MoveNext -> Left MoveNext
    
    Left (Stucked poss_pats) -> Left . Stucked $ do 
      (pat1, v1, res1) <- poss_pats
      case match' tlvl_ctx (rhs_ctx <: res1.resultCtx <: res1.freevarsRhs <: res1.extraDef)
                  ts
                  ps
                  sp
        of 
        Left (Stucked poss_pats_rest) -> do 
          (pat, v, res) <- poss_pats_rest
          pure (pat1++pat, v1++v, unionRes rhs_ctx res1 res)

        _ -> map (\(p, v) -> (p:ps, v:sp, res1)) (zip pat1 v1)
         

  _ -> error "Impossible"

-- | Try to match, if can't match, try spilt or move to next set of patterns 
match1' :: Context -> Context -> (Name, Icit, VType) -> R.Pattern -> (Value, Icit) -> Either Unmatch [Def]
match1' tlvl_ctx rhs_ctx tel@(tylvl_name, i, force -> t) p (v, i') = case (p, force v) of 
  (R.PVar x _, v) -> 
        pure [x := v] 
  (R.PCon con_name ps _, VCon vcon_name vs) 
    | con_name == vcon_name -> do 
        let (dat, con) = fromJust $ lookupCon' con_name rhs_ctx 
        let (pre_tys,arg_tys) = splitAt (length dat.dataPara) con.conPara
        case match' 
              tlvl_ctx rhs_ctx 
              (substTelescope' 
                  rhs_ctx
                  (map (\((x,_,_), v) -> x := fst v) (zip pre_tys vs)) 
                  arg_tys) 
              ps 
              (drop (length dat.dataPara) vs) 
          of
          Right e -> pure e 

          Left (Stucked poss_pats) -> Left . Stucked $ do 
            (pat, v, res) <- poss_pats 
            pure ([R.PCon con_name pat i], [(VCon con_name v, i)], res)

          Left MoveNext -> Left MoveNext
    | otherwise -> Left MoveNext 
  (p, VVar x) -> do 
        case splitCase rhs_ctx tel of 
          Nothing -> Left MoveNext -- i guess it's impossible 
          Just poss_pats -> Left . Stucked $ do 
            
            (pat, v, res) <- poss_pats
            pure ([pat], [v], res)
  _ -> Left MoveNext


-- match1 :: Context -> R.Pattern -> (Value, Icit) -> Maybe [Def]
-- match1 ctx (R.PVar x i) (force -> v, i') | i == i' = Just $ pure (x := v)
-- match1 ctx (R.PCon name ps i) (force -> VCon name' ps', i') 
--      | i == i' && name == name' = do 
--       (dat, con) <- lookupCon' name ctx 
--       match ctx ps (drop (length dat.dataPara) ps')
--      | otherwise = Nothing 
-- match1 ctx (R.PInacc _ _) _ = Just []
-- match1 ctx _ _ = Nothing 