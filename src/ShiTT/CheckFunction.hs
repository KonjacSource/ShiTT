{-# HLINT ignore #-}
module ShiTT.CheckFunction where

import qualified ShiTT.Decl as D
-- import ShiTT.Decl
import ShiTT.Context
import qualified ShiTT.Check as C
import ShiTT.Eval
import qualified Data.Map as M
import ShiTT.Syntax
import Control.Exception
import Control.Monad (forM, when, join, guard)
import Data.Maybe (fromJust, isNothing)
import ShiTT.Meta
import Data.IORef (readIORef)
import Data.List (nub)


data PMErr
  = NumOfPatErr
  | IcitErr Icit Icit
  | UnknownDataName Name
  | UnknownConNameOfData Name Data
  | TheGivenTypeIsNotAData Value
  | Matchable Name [Pattern]
  deriving Show

data CheckError = PMErr PMErr
                | UnifyE Value Value
                | UsedK
                | BoundaryMismatch Name [((Spine, Value), (Spine, Value))]
                | ConflictName Name
  deriving (Exception, Show)

type UnifyContext =  M.Map Name Value

-- | What we get when we check those patterns.
data CheckPResult = CheckPResult
  { rhsType :: Maybe VType
  , rhsDefs :: [ElabDef]
  , unifyRes :: UnifyContext
  , asValue :: Spine
  } deriving Show

lift :: Either CheckError a -> IO a
lift (Left e)  = throwIO e
lift (Right a) = pure a

evalWithPvar :: Context -> UnifyContext -> Term -> Value
evalWithPvar ctx pvars t = eval (ctx <: pvars) $ quote ctx $ eval ctx t

(^?) :: Maybe a -> CheckError -> Either CheckError a
Nothing ^? e = Left e
Just x ^? _ = pure x

-- | Check patterns, get the information of return type and the context of rhs.
checkP :: Context          -- ^ type level context
       -> Telescope        -- ^ expected telescope
       -> [Pattern]        -- ^ checking patterns
       -> Maybe Type       -- ^ rhs type
       -> UnifyContext     -- ^ unificatrion context for pattern var
       -> Either CheckError CheckPResult
checkP ctx [] [] rhsT pvars = Right CheckPResult
                   { rhsType = eval ctx <$> rhsT
                   , rhsDefs = []
                   , unifyRes = pvars
                   , asValue = []
                   }
checkP ctx ((x',i', t'):ts) (p:ps) rhsT pvars
  | icit p == i' = do
      let t = evalWithPvar ctx pvars t'
      case p of
        ---------------------------------------------------------------------------------
        PVar x i -> do
            let type_level_defs = [(x', t) :=! VPatVar x []]
            let ctx'            = ctx <: type_level_defs <: (x, t) :=! VPatVar x []
            let rhs_defs        = [(x, t) :=! VPatVar x []]
            rest               <- checkP ctx' ts ps rhsT pvars
            pure CheckPResult
              { rhsType  = rest.rhsType
              , rhsDefs  = rhs_defs ++ rest.rhsDefs
              , unifyRes = M.union rest.unifyRes pvars
              , asValue   = (VPatVar x [], i) : rest.asValue
              }
        ---------------------------------------------------------------------------------
        PCon con_name con_args i ->
          case t of
            VCon dat_name dat_args -> do
              dat         <-  M.lookup dat_name ctx.decls.allDataDecls
                          ^?  PMErr (UnknownDataName dat_name)

              con         <-  lookupCon con_name dat
                          ^?  PMErr (UnknownConNameOfData con_name dat)

              con_res     <-  checkCon ctx (dat, dat_args) (con, con_args, i) pvars
              let con_val  =  head con_res.asValue
              let ctx'     =  ctx <: x' := fst con_val
              rest        <-  checkP ctx' ts ps rhsT con_res.unifyRes
              pure CheckPResult
                { rhsType  = rest.rhsType
                , rhsDefs  = con_res.rhsDefs ++ rest.rhsDefs
                , unifyRes = M.union con_res.unifyRes rest.unifyRes
                , asValue   = con_val : rest.asValue
                }
            _ -> Left . PMErr $ TheGivenTypeIsNotAData t

  | otherwise = Left . PMErr $ IcitErr (icit p) i'
checkP ctx _ _ _ _ = Left . PMErr $ NumOfPatErr

-- | Check the single constructor under a data type (fully applied)
--   check arguments in current context, then unify. 
checkCon :: Context
         -> (Data, Spine) -- ^ expected type
         -> (Constructor, [Pattern], Icit)
         -> UnifyContext
         -> Either CheckError CheckPResult
checkCon ctx a@(dat, dat_args) b@(con, ps, i) pvars = do
  let (dat_para, dat_ix) = splitAt (length dat.dataPara) dat_args
  --                     ^ Split the arguments on data
  let para_def           = [ x := v | ((x,_,_), (v,_)) <- zip dat.dataPara dat_para ]
  --                     ^ Get the definitions of coresponding data parameters
  let ps_tele_ctx        = map (freeVar . (\(x,_,_) -> x)) con.conPara
  let ps_tele            = [ (x,i, normalize (ctx <: para_def <: ps_tele_ctx) t) | (x,i,t) <- con.conPara ] -- TODO : to be optimized
  --                     ^ Telescope of constructor arguments
  arg_res               <- checkP (ctx <: ps_tele_ctx) ps_tele ps Nothing pvars
  --                     ^ Check constructor arguments
  let con_arg_def        = [ x := v | ((x,_,_), (v,_)) <- zip con.conPara arg_res.asValue ]
  --                     ^ Get the definitions of coresponding constructor arguments
  let ret_ix             = [ (eval (ctx <: para_def <: con_arg_def) t, i) | (t, i) <- con.retIx ]
  --                     ^ Get the returning indexes
  unify_res             <- unifySp (ctx <: arg_res.rhsDefs) arg_res.unifyRes ret_ix dat_ix
  --                     ^ Unification!
  let new_ctx = ctx <: arg_res.rhsDefs <: con_arg_def
  
  -- trace ("\n---------------------------------------------------\nI'm checking constructor: " ++ show b ++ " under the type: " ++ show a) $ do 
  -- trace ("* ps_tele_ctx = "  ++ show ps_tele_ctx ++ "\n") do
  -- trace ("* para_def = "  ++ show para_def ++ "\n") do
  -- trace ("* ps_tele = "  ++ show ps_tele ++ "\n") do
  -- trace ("* checkP ctx  = "  ++ show (ctx <: ps_tele_ctx) ++ "\n") do
  -- trace ("* ctx         =\n" ++ printContext ctx ++ "\n") do
  -- trace ("* arg_res     = "  ++ show arg_res     ++ "\n") do
  -- trace ("* con_arg_def = "  ++ show con_arg_def ++ "\n") do
  -- trace ("* ret_ix      = "  ++ show ret_ix      ++ "\n") do
  -- trace ("* new_ctx   = "  ++ show new_ctx   ++ "\n") do
  -- trace ("* unify_res   = "  ++ show unify_res   ++ "\n") do

  let ret_val            = VCon con.conName $ allImplSp dat_para ++ arg_res.asValue
  pure arg_res
    { rhsDefs = [ (x, refresh new_ctx t) :=! refresh new_ctx v | (x,t) :=! v <- arg_res.rhsDefs ]
    , unifyRes = unify_res
    , asValue   = [(ret_val, i)]
    }

checkClause :: Context -> D.Fun -> D.Clause -> IO (Either Context (Term, Context))
checkClause ctx fun (D.Clause pat rhs) = do

  -- patvar's name must be different from other (noncorrespond) name in telescope
  -- or this will be error:
  -- 
  --  fun J {A : U} {a : A} (P : (b : A) -> Id a b -> U) (p : P a (refl _)) (b : A) (e : Id a b) : P b e 
  --  | {Ad} {ad} P p a (refl x) = p 

  let allNames = [ x | (x,_,_) <- fun.funPara]
  checkPatternNames allNames fun.funPara pat
  
  case rhs of
    D.NoMatchFor x -> do -- Check absurd pattern
      res <- lift $ checkP ctx fun.funPara pat Nothing M.empty  -- here we check patterns
      let rhs_ctx = ctx <: res.rhsDefs
      case splitCase rhs_ctx (x, Expl, quote rhs_ctx $ fromJust (getType x [ x :~ (t, Inserted) | (x, t) :=! _ <- res.rhsDefs ])) of
        Just [] -> pure (Left rhs_ctx)
        Just ps -> throwIO . PMErr $ Matchable x (map (\(x,_,_) -> x) ps)
        Nothing -> throwIO . PMErr $ Matchable x [PVar x Expl]
    D.Rhs t -> do
      res <- lift $ checkP ctx fun.funPara pat (Just fun.funRetType) M.empty
      let rhs_ctx1 = ctx <: res.rhsDefs
                         <: res.unifyRes
      let rhs_ctx = rhs_ctx1 {  bds = fetchBD rhs_ctx1 res.rhsDefs  }
      -- trace
      --   ("I'm checking clause for funcion: " ++ fun.funName
      --   ++ "\n- with context: \n\n" ++ printContext rhs_ctx ++ "\n"
      --   -- ++ "\n  - with bds: " ++ show rhs_ctx.bds
      --   ) do
      rhs <- C.check rhs_ctx t (fromJust res.rhsType)
      pure $ Right (rhs, rhs_ctx)
  where
    fetchBD :: Context -> [ElabDef] -> BDs
    fetchBD ctx defs =
      let names = [ name | (name, _) :=! _ <- defs ]
      in foldr (\n bds -> M.insert n (if isFree ctx n then Bound else Defined) bds) M.empty names

checkPatternNames :: [Name] -> Telescope -> [Pattern] -> IO ()
checkPatternNames names ts ps = case (ts, ps) of
  ([], []) -> pure ()
  ((x,_,_):ts, p:ps)
    | x /= "_" -> do
        let can't_be = filter (/= x) names
        if all (`notElem` can't_be) $ allNames p then 
          checkPatternNames names ts ps
        else 
          throwIO (ConflictName $ head (filter (`elem` can't_be) $ allNames p))
    | otherwise -> checkPatternNames names ts ps
  _ -> error "Impossible"
  where
    allNames = \case
      PVar x _ -> [x]
      PCon _ ps _ -> nub (allNames =<< ps)

checkFun :: Context -> Bool -> D.Fun -> IO Fun
checkFun ctx cover_chk_gate fun  = do
  let preFun = Fun
               { funName = fun.funName
               , funPara = fun.funPara
               , funRetType = fun.funRetType
               , funClauses = Nothing
               }
  let ctx' = ctx { decls = insertFun preFun ctx.decls }

  let cls = fun.clauses
  -- elaboratted clause
  rhss <- forM cls $ \c -> do
    rhs <- checkClause ctx' fun c
    pure (c.patterns, rhs)

  let patsWithCtx = do -- TO-USE: In coverage check
        (p, t) <- rhss
        case t of
          Left ctx -> pure (p,ctx)
          Right (_,ctx) -> pure (p,ctx)

  when cover_chk_gate do 
    checkCoverage [] fun.funName fun.funPara patsWithCtx (genInitSp ctx fun.funPara)

  pure Fun
    { funName = fun.funName
    , funPara = fun.funPara
    , funRetType = fun.funRetType
    , funClauses = if null rhss then Nothing else Just do
        (ps, Right (rhs, rhs_ctx)) <- rhss
        pure Clause
          { patterns = ps
          , rhsContext = rhs_ctx
          , clauseRhs = rhs
          }
    }

-- | Unify pattern variables.
unify1 :: Context -> UnifyContext -> Value -> Value -> Either CheckError UnifyContext
unify1 ctx fore v w = case (refresh ctx v, refresh ctx w) of

  (VPatVar n [], VPatVar m []) | runIO (readIORef withoutKRef) && m == n -> Left UsedK
  (VPatVar n [], VRig m [])    | runIO (readIORef withoutKRef) && m == n -> Left UsedK
  (VRig n []   , VPatVar m []) | runIO (readIORef withoutKRef) && m == n -> Left UsedK
  (VRig n []   , VRig m [])    | runIO (readIORef withoutKRef) && m == n -> Left UsedK

  (VPatVar n [], VPatVar m [])
    | m == n    -> pure fore
    | m <  n    -> pure $ M.insert n (VPatVar m []) fore
    | otherwise -> pure $ M.insert m (VPatVar n []) fore

  (VPatVar n [], VVar n') | n == n' -> pure fore
  (VVar n', VPatVar n []) | n == n' -> pure fore

  (VPatVar n [], r) | n `notElem` freeVarOf r -> pure $ M.insert n r fore
  (l, VPatVar n []) | n `notElem` freeVarOf l -> pure $ M.insert n l fore

  (VLam x i t, VLam x' i' t') | i == i' -> let x0 = freshName ctx x in
    unify1 (ctx <: freeVar x0) fore (t @ x := VVar x0) (t' @ x' := VVar x0)

  (VLam x i t, t') ->
    let x' = freshName ctx x
        ctx' = ctx <: freeVar x' in
    unify1 ctx' fore (t @ x := VVar x') (vApp ctx' t' (VVar x') i)

  (t', VLam x i t) -> let x' = freshName ctx x in
    unify1 (ctx <: freeVar x') fore (vApp ctx t' (VVar x') i) (t @ x := VVar x')

  (VPi x i a b, VPi x' i' a' b') | i == i' -> do
    let x0 = freshName ctx x
    unify1 ctx fore a a'
    unify1 (ctx <: freeVar x0) fore (b @ x := VVar x0) (b' @ x' := VVar x0)

  (VCon con sp, VCon con' sp')   | con == con' -> unifySp ctx fore sp sp'
  (VRig n sp, VRig m sp')        | n == m      -> unifySp ctx fore sp sp'
  (VFunc fun sp, VFunc fun' sp') | fun.funName == fun'.funName -> unifySp ctx fore sp sp'
  (VFlex m sp, VFlex m' sp')     | m == m'     -> unifySp ctx fore sp sp'
  (VPatVar n sp, VPatVar m sp')  | n == m      -> unifySp ctx fore sp sp'

  (v, w) -> Left $ UnifyE v w

unifySp :: Context -> UnifyContext -> Spine -> Spine -> Either CheckError UnifyContext
unifySp ctx fore s1 s2 = case (s1, s2) of
  ([], []) -> pure fore
  ((v, i):vs, (w, i'):ws) | i == i' -> do
    s <- unify1 ctx fore v w
    unifySp (ctx <: s) s vs ws
  _ -> error "impossible"

-- Coverage Check 
-----------------------

isInacc :: Context -> Name -> Bool 
isInacc rhs_ctx name = not $ isFree rhs_ctx name
  -- case M.lookup name rhs_ctx.env of 
  --   Just (VVar x      ) | x == name -> False -- free 
  --   Just (VPatVar x []) | x == name -> False 
  --   _ -> True

data MatchResult
  = Done [Def]
  | Failed 
  | Stucked [Spine]
  deriving Show 

-- | Is the pattern availd in the context
availdPattern :: Context -> (Name, Icit, Type) -> Pattern -> Maybe ((Value, Icit), CheckPResult)
availdPattern ctx t p = case checkP ctx [t] [p] Nothing M.empty of 
  Right res -> pure (head res.asValue, res) 
  _ -> Nothing 
  
-- | Generate pattern of given constructor, return used names (in pattern)
mkConPat :: Context -> Data -> Constructor -> Icit -> Pattern
mkConPat ctx dat con i = PCon con.conName pargs i where 
  ixls xs = go 0 xs where 
    go _ [] = [] 
    go n (x:xs) = (x,n) : go (n+1) xs
  names = map (\(x, n) -> freshName ctx (x ++ show (n :: Int))) (ixls (map (\(x,_,_) -> x) con.conPara))
  pargs = map (\(n, (_,i,_)) -> PVar n i) $ zip names con.conPara

-- | Give the expected type, generate all the possible patterns.
splitCase :: Context -> (Name, Icit, Type) -> Maybe [(Pattern, (Value, Icit), CheckPResult)]
splitCase ctx (x, icit, t) = case eval ctx t of 
  (VCon data_name data_args) ->
    -- trace ("\nI'm splitting cases on: " ++ x ++ " under " ++ show (eval ctx t) ++ "\n" ++ printContext ctx) $
    case M.lookup data_name ctx.decls.allDataDecls of 
      Nothing  -> Nothing
      Just dat -> Just do -- List do  
        con <- dat.dataCons
        -- trace ("-------\n- on: " ++ show con) $ do
        let conP = mkConPat ctx dat con icit
        -- trace ("- conP: " ++ show conP) $ do
        case availdPattern ctx (x, icit, normalize ctx t) conP of
          Nothing -> [] 
          Just (v, res) -> pure (conP, v, res)
  _ -> Nothing 

splitMatch1 :: Context -> [Name] -> (Name, Icit, Type) -> Pattern -> (Value, Icit) -> MatchResult
splitMatch1 ctx unmatchables (_, _, eval ctx -> VCon ty_name []) p (v, i) 
  | icit p == i && ty_name `elem` unmatchables
  = case (p, v) of 
      (PVar x _, VPatVar v []) 
        | isInacc ctx x  -> Done [x := VPatVar v []] -- Mark as flexibile
        | otherwise      -> Done [x := VVar v]
      (PVar x _, VVar v)  
        | isInacc ctx x  -> Done [x := VPatVar v []]
        | otherwise      -> Done [x := VVar v]
      (PVar x _, v)      -> Done [x := v]
      _                  -> error "Trying match an unmatchable"
splitMatch1 ctx unmatchables t p (v, i) | icit p == i = case (p, v) of 
  (PVar x _, VPatVar v []) 
    | isInacc ctx x  -> Done [x := VPatVar v []] -- Mark as flexibile
    | otherwise      -> Done [x := VVar v]
  (PVar x _, VVar v)  
    | isInacc ctx x  -> Done [x := VPatVar v []]
    | otherwise      -> Done [x := VVar v]
  (PVar x _, v)      -> Done [x := v]
  (PCon con_name ps _, VCon con_name' vs) -- note that length ps /= length vs, since vs includes data parameters
    | con_name == con_name' -> 
        -- 1. get data definition and constructor definition
        let (dat, con) = fromJust $ lookupCon' con_name ctx
        -- 2. split telescope to data parameters and constructor parameters  
            (pre_tys,arg_tys) = (allImpl dat.dataPara, con.conPara)
            (pre_vs, arg_vs)  = splitAt (length dat.dataPara) vs
            teles = [ (x,i, normalize (ctx <: (map (\((x,_,_), v) -> x := fst v) (zip pre_tys vs))) t)
                    | (x,i,t) <- arg_tys]
        -- 3. try match vs against ps under the modified teles
        in case splitMatch 
                  ctx
                  unmatchables 
                  teles
                  ps 
                  arg_vs
        of 
          Failed -> Failed
          Done defs -> Done defs
          Stucked poss -> Stucked do 
            vs' <- poss 
            pure [(VCon con_name (pre_vs ++ vs'), i)]
    | otherwise -> Failed 
  (p,  VVar x) -> case splitCase ctx t of 
      Nothing -> Failed 
      Just poss -> Stucked do 
        (_,v,_) <- poss 
        pure [v] 
  (p,  VPatVar x []) -> case splitCase ctx t of 
      Nothing -> Failed 
      Just poss -> Stucked do 
        (_,v,_) <- poss 
        pure [v]
  _ -> error $ "\n\nimpossible : " ++ show ctx ++ show t ++ " | " ++ show p ++ " | " ++ show (v, i) ++ "\n"
splitMatch1 _ _ _ _ _ = error "impossible"

-- | try match, if stuck, return the pattern with splitted variables.
splitMatch :: Context -> [Name] -> Telescope -> [Pattern] -> Spine -> MatchResult
splitMatch ctx unmatchables ts ps vs = case (ts, ps, vs) of 
  ([], [], []) -> Done []
  (t@(x,i,ty):ts, p:ps, v@(val,_):vs) -> 
    case splitMatch1 ctx unmatchables t p v of 
      Failed -> Failed 
      -- 
      Done defs -> case splitMatch (ctx <: x := val <: defs) unmatchables ts ps vs of 
        Failed -> Failed 
        Done defs' -> Done $ defs ++ defs' 
        Stucked poss -> Stucked do 
          vs <- poss
          pure (v:vs)
      -- 
      Stucked poss -> Stucked do 
        v' <- poss 
        v <- v'
        pure (v:vs)
  _ -> error $ "impossible : " ++ show ctx ++ show ts ++ "\n" ++ show ps ++ "\n" ++ show vs 


travPattern :: [Name] -> Telescope -> [([Pattern], Context)] -> Spine -> Maybe [Spine]
travPattern unmatchables ts [] sp = Just [sp]  -- passed
travPattern unmatchables ts pats@((ps,rhs_ctx): rest) sp = case splitMatch rhs_ctx unmatchables ts ps sp of 
  Failed -> travPattern unmatchables ts rest sp 
  Done _ -> Nothing 
  Stucked new_sps -> 
    let res = map (travPattern unmatchables ts pats) new_sps
    in  if all isNothing res then 
          Nothing
        else Just do
          s <- res 
          case s of 
            Nothing -> [] 
            Just sp -> sp

checkCoverage :: [Name] -> Name -> Telescope -> [([Pattern], Context)] -> Spine -> IO () 
checkCoverage unmatchables fun_name ts ps sp = do 
  case travPattern unmatchables ts ps sp of 
    Nothing -> pure () 
    Just sp -> putStrLn ("Warning: Missing patterns on function " ++ fun_name ++ "\n" ++ show sp)

genInitSp :: Context -> Telescope -> Spine 
genInitSp ctx = \case 
  [] -> [] 
  (freshName ctx . ('*':) -> x,i,t):ts -> (VPatVar x [], i) : genInitSp (ctx <: freeVar x) ts

