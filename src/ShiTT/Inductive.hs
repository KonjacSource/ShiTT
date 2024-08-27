{-# HLINT ignore #-}
{-# LANGUAGE NondecreasingIndentation #-}
module ShiTT.Inductive where 

import qualified ShiTT.Decl as R 
import ShiTT.Context 
import qualified ShiTT.Check as C 
import ShiTT.Eval
import qualified Data.Map as M 
import ShiTT.Syntax
import Debug.Trace
import Control.Exception
import Control.Monad (forM, when)
import Data.Maybe (fromJust)

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

unionRes :: CheckResult -> CheckResult -> CheckResult
unionRes a b = CheckResult
  { resultCtx = a.resultCtx ++ b.resultCtx
  , extraDef = updateDef a.extraDef b.extraDef
  , freevarsRhs = a.freevarsRhs ++ b.freevarsRhs
  , typeLevelDef = a.typeLevelDef ++ b.typeLevelDef
  }

refresh :: Context -> Value -> Value 
refresh ctx = eval ctx . quote ctx 

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
      con_para = exe substTelescope sub con.conPara
  in refreshTelescope ctx con_para

updateDef :: [Def] -> [Def] -> [Def]
updateDef a b = exe substDefs a b ++ exe substDefs b a

-- | Check (con ps) agasint type t.
checkCon :: Context -> [Name] -> (Constructor, [R.Pattern]) -> (Data, Spine) -> Either CheckError ([Name], Value, CheckResult)
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
       , res { extraDef = updateDef defs res.extraDef, typeLevelDef = [] } ) -- this is a sub check, so we dont need the type level def
  where allImpl = \case 
          [] -> []
          ((v,_) : rest) -> (v, Impl) : allImpl rest
  

-- | checkP ctx [(succ n), (cons x xs)] [(m : N), (ls : List N)] ==> 
--   [xs, x, n] ,
--   [(succ n), (cons x xs)] ,
--   CheckResult 
--   { resultCtx = [(n : N), (x : N), (xs : List N)]
--   , typeLevelDef = [(m := succ n), (ls := cons xs)] 
--   } 
checkP :: Context -> [Name] -> [R.Pattern] -> Telescope -> Either CheckError ([Name], Spine, CheckResult)
checkP ctx ord [] [] = pure $ (ord, [], CheckResult [] [] [] [])
checkP ctx ord (p:ps) ((x', i', t'):ts) 
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
        let ts' = exe substTelescope now.typeLevelDef ts
        (ord', psv, rest) <- checkP (ctx <: x := VPatVar x []) (x : ord) ps ts'
        pure (ord', (VPatVar x [], i) : psv, unionRes now rest)
      
      R.PCon con_name con_args i -> 
        case t of 
          VCon dat_name dat_args -> do
            dat <- M.lookup dat_name ctx.decls.allDataDecls ^? (PMErr $ UnknownDataName dat_name)
            con <- lookupCon con_name dat                   ^? (PMErr $ UnknownConNameOfData con_name dat)
            (ord', v, now) <- checkCon ctx ord (con, con_args) (dat, dat_args)
            let now' = now {typeLevelDef = (x' := v) : now.typeLevelDef}
            let ts' = exe substTelescope (now'.typeLevelDef ++ now'.extraDef) ts
            (ord'', psv, rest) <- checkP (ctx <: now'.resultCtx) ord' ps ts' 
            pure (ord'', (v, i) : psv, unionRes now' rest)

          _ -> Left . PMErr $ TheGivenTypeIsNotAData t

      R.PInacc n _ -> error "Deprecated" 
  | otherwise = Left . PMErr $ IcitErr (R.icit p) i' 
checkP ctx ord _ _ = Left . PMErr $ NumOfPatErr

checkClause :: Context -> R.Fun -> R.Clause -> IO (Maybe Term)
checkClause ctx fun (R.Clause pat rhs) = case rhs of
  R.NoMatchFor x -> undefined >> pure Nothing -- TODO: Check absurd pattern
  R.Rhs t -> do 
    (_,sp,res) <- execCheck $ checkP ctx [] pat fun.funPara 
    let rhs_ctx = ctx  <: res.resultCtx <: res.freevarsRhs <: res.extraDef
    let expect_type = refresh rhs_ctx $ fun.funRetType sp 
    rhs <- C.check rhs_ctx t expect_type
    pure $ Just rhs

-- Turn a clause to a function.
mkFunVal :: Context -> [R.Pattern] -> Term -> (Context -> Spine -> Maybe Value)
mkFunVal ctx ps rhs call_ctx sp = do 
  defs <- match ctx ps sp
  let ctx' = call_ctx <: defs 
  pure $ refresh ctx' $ eval ctx' rhs 

checkClauses :: Context -> R.Fun -> [R.Clause] -> IO (Context -> Spine -> Maybe Value)
checkClauses ctx fun cls = do 
  -- TODO : Coverage Check
  rhss <- forM cls $ \c -> do 
    rhs <- checkClause ctx fun c
    pure (c.patterns, rhs)
  let vs = map (\(pat, fromJust -> rhs) -> mkFunVal ctx pat rhs) $ filter ((/= Nothing) . snd) rhss
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
               , funVal = \ _ _ -> Nothing -- so that we may check the type of the definning function
               }
  let ctx' =ctx { decls = insertFun preFun ctx.decls }
  val <- checkClauses ctx' fun fun.clauses 
  pure $ preFun { funVal = val }

unify1 :: NameOrder -> Context -> [Def] -> Value -> Value -> Either CheckError [Def]
unify1 ord ctx fore v w = case (force v, force w) of 
  (VPatVar n [], VPatVar m [])
    | m == n    -> pure fore
    | ord m n   -> pure $ (n := VPatVar m []) : fore
    | otherwise -> pure $ (m := VPatVar n []) : fore

  (VPatVar n [], r) -> do 
    pure $ [n := r] ++ fore
  (l, VPatVar n []) -> do 
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
    let vs' = exe substSp s vs 
    let ws' = exe substSp s ws
    unifySp ord ctx s vs' ws'
  _ -> error "impossible"
