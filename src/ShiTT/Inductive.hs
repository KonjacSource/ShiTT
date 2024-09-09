{-# HLINT ignore #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE BlockArguments #-}
module ShiTT.Inductive where 

import qualified ShiTT.Decl as D
import ShiTT.Decl (Pattern(..))
import ShiTT.Context 
import qualified ShiTT.Check as C 
import ShiTT.Eval
import qualified Data.Map as M 
import ShiTT.Syntax
import Control.Exception
import Control.Monad (forM, when, join)
import Data.Maybe (fromJust, isJust, isNothing)
import ShiTT.Meta 
import Data.IORef (readIORef)
import Data.Foldable (forM_)
import Debug.Trace (trace)

match :: Context -> [Pattern] -> Spine -> Maybe [Def]
match ctx [] [] = Just [] 
match ctx (p:ps) (p':ps') = do 
  ret <- match1 ctx p p' 
  rest <- match ctx ps ps'
  pure $ ret ++ rest
match _ p sp = error $ "Unmatch : " ++ show p ++ " | " ++ show sp

match1 :: Context -> Pattern -> (Value, Icit) -> Maybe [Def]
match1 ctx (PVar x i) (force -> v, i') | i == i' = Just $ pure (x := v)
match1 ctx (PCon name ps i) (force -> VCon name' ps', i') 
     | i == i' && name == name' = do 
      (dat, con) <- lookupCon' name ctx 
      match ctx ps (drop (length dat.dataPara) ps')
     | otherwise = Nothing 
match1 ctx (PInacc _ _) _ = Just []
match1 ctx _ _ = Nothing 

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
         -> (Constructor, [Pattern]) 
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
checkP :: Context -> [Name] -> [Pattern] -> Telescope -> Either CheckError ([Name], Spine, CheckResult)
checkP ctx ord [] [] = pure $ (ord, [], CheckResult [] [] [] [])
checkP ctx ord (p:ps) sp@((x', i', t'): ts) 
  | D.icit p == i' = 
    let t = refresh ctx t' in
    case p of 
      PVar x i -> do 
        let now = CheckResult 
                  { resultCtx    = [x :~ (t, Source)]
                  , extraDef     = []
                  , freevarsRhs  = [x := VPatVar x []]
                  , typeLevelDef = [x' := VPatVar x []]
                  } 
        let ts' = substTelescope' ctx now.typeLevelDef ts
        (ord', psv, rest) <- checkP (ctx <: x := VPatVar x []) (x : ord) ps ts'
        pure (ord', (VPatVar x [], i) : psv, unionRes ctx now rest)
      
      PCon con_name con_args i -> 
        case t of 
          VCon dat_name dat_args -> do
            (basePart -> dat) <- M.lookup dat_name ctx.decls.allDataDecls 
                                 ^? (PMErr $ UnknownDataName dat_name)
            con <- lookupCon con_name dat                   
                   ^? (PMErr $ UnknownConNameOfData con_name dat)
            -- check constructor
            (ord', v, now) <- checkCon ctx ord (con, con_args) (dat, dat_args)
            let now' = now {typeLevelDef = (x' := v) : now.typeLevelDef}
            let ts' = substTelescope' ctx (now'.typeLevelDef ++ now'.extraDef) ts
            (ord'', psv, rest) <- checkP (ctx <: now'.resultCtx) ord' ps ts' 
            pure (ord'', (v, i) : psv, unionRes ctx now' rest)

          _ -> Left . PMErr $ TheGivenTypeIsNotAData t

      PInacc n _ -> error "Deprecated" 
  | otherwise = trace (show ctx ++ show (p:ps) ++ "\n" ++ show sp) $ Left . PMErr $ IcitErr (D.icit p) i' 
checkP ctx ord _ _ = Left . PMErr $ NumOfPatErr

checkClause :: Context -> D.Fun -> D.Clause -> IO (Either Context (Term, Context))
checkClause ctx fun (D.Clause pat rhs) = case rhs of
  D.NoMatchFor x -> do -- Check absurd pattern
    (_,sp,res) <- execCheck $ checkP ctx [] pat fun.funPara -- here we check patterns
    let rhs_ctx = ctx <: res.resultCtx <: res.extraDef
    case splitCase rhs_ctx (x, Expl, fromJust (getType x res.resultCtx)) of
      Just [] -> pure (Left rhs_ctx)
      Just ps -> throwIO . PMErr $ Matchable x (map (\(x,_,_) -> x) ps)
      Nothing -> throwIO . PMErr $ Matchable x [PVar x Expl]

  D.Rhs t -> do
    (_,sp,res) <- execCheck $ checkP ctx [] pat fun.funPara -- here we check patterns
    let rhs_ctx = ctx <: res.resultCtx <: res.freevarsRhs <: res.extraDef
    let expect_type = refresh rhs_ctx $ fun.funRetType sp 
    rhs <- C.check rhs_ctx t expect_type
    pure $ Right (rhs, rhs_ctx)

-- Turn a clause to a function.
mkFunVal :: Context -> [Pattern] -> Term -> (Context -> Spine -> Maybe Value)
mkFunVal ctx ps rhs call_ctx sp = do 
  defs <- match ctx ps sp
  let ctx' = call_ctx <: defs 
  pure $ refresh ctx' $ eval ctx' rhs 

checkClauses :: Context -> Bool -> D.Fun -> [D.Clause] -> IO (Context -> Spine -> Maybe Value)
checkClauses ctx coverChGate fun cls = do 
  rhss <- forM cls $ \c -> do 
    rhs <- checkClause ctx fun c
    pure (c.patterns, rhs)

  let patsWithRes = do 
        (p, t) <- rhss
        case t of 
          Left ctx -> pure (p,ctx)
          Right (_,ctx) -> pure (p,ctx)

  -- Coverage Check
  when coverChGate $ do 
    unmatchables <- readIORef allUnmatchableTypes
    checkCoverage unmatchables fun.funName fun.funPara patsWithRes (genInitSp ctx fun.funPara)

  let rhss' = flip map rhss \case (p, Left _)  -> (p, Nothing) 
                                  (p, Right x) -> (p, Just x)
  let vs = map (\(pat, fst . fromJust -> rhs) -> mkFunVal ctx pat rhs) $ filter (isJust . snd) rhss'
  let go [] = \call_ctx sp -> Nothing 
      go (v:vs) = \call_ctx sp -> case v call_ctx sp of 
        Just r -> Just r
        Nothing -> go vs call_ctx sp 
  pure $ go vs

checkFun :: Context -> D.Fun -> IO Fun 
checkFun ctx fun = do 
  let preFun = Fun 
               { funName = fun.funName 
               , funPara = fun.funPara
               , funRetType = fun.funRetType
               , funVal = \ _ _ -> Nothing -- A fake definition, so that we may check the type of the definning function
               }
  let ctx' =ctx { decls = insertFun preFun ctx.decls }
  val <- checkClauses ctx' True fun fun.clauses 
  -- TODO : HIT.Check Boundary
  pure $ preFun { funVal = val }


checkAxiom :: Context -> D.Fun -> IO Fun 
checkAxiom ctx fun = do 
  let preFun = Fun 
               { funName = fun.funName 
               , funPara = fun.funPara
               , funRetType = fun.funRetType
               , funVal = \ _ _ -> Nothing -- A fake definition, so that we may check the type of the definning function
               }
  let ctx' =ctx { decls = insertFun preFun ctx.decls }
  val <- checkClauses ctx' False fun fun.clauses
  pure $ preFun { funVal = val }

unify1 :: NameOrder -> Context -> [Def] -> Value -> Value -> Either CheckError [Def]
unify1 ord ctx fore v w = case (force v, force w) of 

  (VPatVar n [], VPatVar m []) | (runIO $ readIORef withoutKRef) && m == n -> Left UsedK
  (VPatVar n [], VRig m [])    | (runIO $ readIORef withoutKRef) && m == n -> Left UsedK
  (VRig n []   , VPatVar m []) | (runIO $ readIORef withoutKRef) && m == n -> Left UsedK
  (VRig n []   , VRig m [])    | (runIO $ readIORef withoutKRef) && m == n -> Left UsedK

  (VPatVar n [], VPatVar m [])
    | m == n    -> pure fore
    | otherwise -> if ord m n then pure $ (n := VRig m []) : fore
                              else pure $ (m := VRig n []) : fore 

  (VPatVar n [], VVar n') | n == n' -> pure fore
  (VVar n', VPatVar n []) | n == n' -> pure fore

  (VPatVar n [], r) | n `notElem` freeVarOf ctx r -> pure $ [n := r] ++ fore
  (l, VPatVar n []) | n `notElem` freeVarOf ctx l -> pure $ [n := l] ++ fore
  
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

-- | Is the pattern availd in the context
availdPattern :: Context -> (Name, Icit, VType) -> Pattern -> Maybe ((Value, Icit), CheckResult)
availdPattern ctx t p = case checkP ctx [] [p] [t] of 
  Right (_, s, r) -> pure (head s, r) 
  _ -> Nothing 
  
-- | Generate pattern of given constructor, return used names (in pattern)
mkConPat :: Context -> Data -> Constructor -> Icit -> Pattern
mkConPat ctx dat con i = (PCon con.conName pargs i) where 
  ixls xs = go 0 xs where 
    go _ [] = [] 
    go n (x:xs) = (x,n) : go (n+1) xs
  names = map (\(x, n) -> freshName ctx (x ++ show (n :: Int))) (ixls (map (\(x,_,_) -> x) con.conPara))
  pargs = map (\(n, (_,i,_)) -> PVar n i) $ zip names con.conPara

-- | Give the expected type, generate all the possible patterns.
splitCase :: Context -> (Name, Icit, VType) -> Maybe [(Pattern, (Value, Icit), CheckResult)]
splitCase ctx (x, icit, force -> t) = case t of 
  t@(VCon data_name data_args) ->
    case M.lookup data_name ctx.decls.allDataDecls of 
      Nothing  -> Nothing
      Just (basePart -> dat) -> Just do -- List do  

        con <- dat.dataCons
        let conP = mkConPat ctx dat con icit
        case availdPattern ctx (x, icit, t) conP of
          Nothing -> [] 
          Just (v, res) -> pure (conP, v, res)
  
  _ -> Nothing -- only_var
  -- where 
  --   pat_name = freshName ctx "~pat'"
  --   only_var = let (b, c) = fromJust $ availdPattern ctx (x, Impl, t) (PVar pat_name icit) in 
  --     [(PVar pat_name icit, b, c)]

----------------------------------

isInacc :: Context -> Name -> Bool 
isInacc rhs_ctx name = case M.lookup name rhs_ctx.env of 
  Just (VVar x      ) | x == name -> False -- free 
  Just (VPatVar x []) | x == name -> False 
  _ -> True

data MatchResult
  = Done [Def]
  | Failed 
  | Stucked [Spine]
  deriving Show 

-- | ctx |- rhs, extraDef in ctx.
splitMatch1 :: Context -> [Name] -> (Name, Icit, VType) -> Pattern -> (Value, Icit) -> MatchResult
splitMatch1 ctx unmatchables (_, _, VCon ty_name []) p (v, i) 
  | D.icit p == i && ty_name `elem` unmatchables
  = case (p, v) of 
      (PVar x _, VPatVar v []) 
        | isInacc ctx x  -> Done [x := VPatVar v []] -- Mark as flexibile
        | otherwise      -> Done [x := VVar v]
      (PVar x _, VVar v)  
        | isInacc ctx x  -> Done [x := VPatVar v []]
        | otherwise      -> Done [x := VVar v]
      (PVar x _, v)      -> Done [x := v]
      _                  -> error "Trying match an unmatchable"

splitMatch1 ctx unmatchables t p (v, i) | D.icit p == i = case (p, v) of 
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
            teles = (substTelescope' 
                      ctx
                      (map (\((x,_,_), v) -> x := fst v) 
                        (zip pre_tys vs)) 
                      arg_tys) 
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
  (t:ts, p:ps, v:vs) -> 
    case splitMatch1 ctx unmatchables t p v of 
      Failed -> Failed 
      -- 
      Done defs -> case splitMatch (ctx <: defs) unmatchables ts ps vs of 
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
  (freshName ctx . ('*':) -> x,i,t):ts -> (VVar x, i) : genInitSp (ctx <: freeVar x) ts

-- HIT (Implementation is shitty)
--------------------------------------------------------------------------
{-
higher inductive BoolX (A : U) : (_ : Bool) -> U where 
| btrue : (b : Bool) -> ... b
| bfalse : (b : Bool) -> ... b 
| bcon : (a b : Bool) -> ... b when b 
  | true = btrue a          
  | false = bfalse a        
-}
checkHData :: Context -> (Data, [D.HConstructor]) -> IO HData
checkHData ctx (dat, hcons) = do
  let ctx' = ctx { decls = insertData dat ctx.decls }
  hcons' <- forM hcons $ \hcon -> do 
    let patss = D.patterns <$> D.hconClauses hcon
    -- let dataParaDefs = map (\(x,i,t) -> (x,t) :=! VVar x) dat.dataPara
    -- let dataParaSp = map (\(x,i,t) -> (VVar x, i)) dat.dataPara
    -- let dataParaSpImpl = map (\(x,i,t) -> (VVar x, Impl)) dat.dataPara
    let con = fromJust $ lookupCon hcon.hconName dat
    let fakeFun = D.Fun
                  { D.funName = hcon.hconName
                  , D.funPara = allImpl dat.dataPara ++ con.conPara 
                  , D.funRetType = \data_con_para -> 
                      let data_para = take (length dat.dataPara) data_con_para in 
                        VCon dat.dataName $ data_para ++ con.retIx data_con_para
                  , D.clauses = hcon.hconClauses
                  }
    fv <- checkClauses ctx' False fakeFun hcon.hconClauses
    pure HConstructor
      { hconName = hcon.hconName
      , hconPatterns = patss 
      , hconClauses = \ctx sp -> case fv ctx sp of 
          Nothing -> Just $ VCon hcon.hconName sp
          Just v -> Just v
      }
  pure HData 
    { basePart = dat
    , higherCons = hcons'
    } 

-- asValue :: [Def] -> Int -> Pattern -> ((Value, Icit), [Def])
-- asValue fvs nameCount = \case 
--   PVar x i -> ((VVar x, i), freeVar (freshName (emptyCtx <: fvs) $ '*':show nameCount ++ x) : fvs)
--   PCon con sp i -> 
--     let (spv, fvs', cnt) = foldr 
--                       (\p (rest, c, cnt) -> let (v, c') = asValue c cnt p in (v : rest, c', cnt + 1)) 
--                       ([], fvs, nameCount + 1)
--                       sp 
--     in ((VCon con spv , i), fvs')
--   PInacc _ _ -> error "Deprecated"

-- {-
-- higher inductive A : U where 
-- | con1 : (x y : T) -> ... 
-- | con2 : (n : N) (x y : T) -> ... when x y
--   | x y -> con1 x y
--   | ...

-- -}

-- -- | equalPair _ intData
-- --   => [(neg zero, pos zero, [])]
-- --   equalPair _ AData
-- --   => [(con2 n x y, con1 n x y, A)]
-- -- Don't forget renaming
-- equalPair :: Context -> HData -> [(Value, Value, VType)]
-- equalPair ctx hdat = do
--   hcon <- hdat.higherCons 
--   let con       = fromJust $ lookupCon hcon.hconName hdat.basePart
--   let mkSp      = (\(x,i,_) -> (VVar x, i))
--   pats <- hcon.hconPatterns
--   let var_defs  = map 
--                     (\(name, pat) -> 
--                       let (v , d) = asValue [] 1 pat in 
--                         (name := fst v, d)) 
--                   $ zip hcon.hconVars pats 
--   let defs      = join $ map snd var_defs
--   let data_para = mkSp <$> hdat.basePart.dataPara
--   let args      = map (\(v,_) -> (v,Impl)) data_para ++ substSp' ctx (map fst var_defs) (mkSp <$> con.conPara)
--   let left      = VCon con.conName args
--   let right     = fromJust $ hcon.hconClauses (ctx <: defs) args
--   pure (left, right, VCon hdat.basePart.dataName (data_para ++ con.retIx args))


-- checkBoundary :: Context -> Fun -> IO () 
-- checkBoundary ctx fun = forM_ (genInitSp ctx (show <$> [1 .. length fun.funPara]) fun.funPara) \ twosp -> do 
--     goBoundary ctx fun (fst <$> twosp, snd <$> twosp)
--   where 
--     genInitSp :: Context -> [Name] -> Telescope -> [[((Value, Icit), (Value, Icit))]]
--     genInitSp ctx names ts = do 
--       (name, (x,i,t)) <- zip names ts 
--       case t of 
--         (VCon data_name data_args) -> case M.lookup data_name ctx.decls.allDataDecls of 
--           Nothing -> do 
--             let x = freshName ctx ('*':name)  
--             pure [((VVar x, i), (VVar x, i))]
--           Just hdat -> do 
--             (v1,v2,ty) <- equalPair ctx hdat
--             pure [((v1, i), (v2,i))]
--         _ -> do 
--           let x = freshName ctx ('*':name)  
--           pure [((VVar x, i), (VVar x, i))]

-- -- check with equalPair, if stuck, split it -- TODO : split
-- -- goBoundary check if each spine apply on fun are equal, if stuck, return new spines 
-- goBoundary :: Context -> Fun -> (Spine, Spine) -> IO (Either [(Spine, Spine)] ())
-- goBoundary ctx fun (sp1, sp2) = 
--   case fun.funVal ctx sp1 of 
--     Just v1 -> case fun.funVal ctx sp2 of 
--       Just v2 -> 
--         do 
--           fmap pure (C.unify ctx v1 v2) 
--         `catch` \ C.UnifyError -> throwIO $ BoundaryMismatch fun.funName [((sp1, v1), (sp2, v2))] 
--       Nothing -> error "TODO" -- TODO : sp2 stucked
--     Nothing -> error "TODO" -- TODO : sp1 stucked
