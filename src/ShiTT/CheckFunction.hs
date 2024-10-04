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
import Data.Maybe (fromJust, isJust, isNothing)
import ShiTT.Meta
import Data.IORef (readIORef)
import Data.Foldable (forM_)
import Debug.Trace (trace)
import Control.Applicative (Alternative(empty))

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

type UnifyContext =  M.Map Name Value

-- | What we get when we check those patterns.
data CheckPResult = CheckPResult
  { rhsType :: Maybe VType
  , rhsDefs :: [ElabDef]
  , unifyRes :: UnifyContext
  , asValue :: Spine
  }

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
            let rhs_defs        = [(x, t) :=! VVar x]
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
checkCon :: Context
         -> (Data, Spine) -- ^ expected type
         -> (Constructor, [Pattern], Icit)
         -> UnifyContext
         -> Either CheckError CheckPResult
checkCon ctx a@(dat, dat_args) b@(con, ps, i) pvars = do
  trace ("\nI'm checking constructor: " ++ show b ++ " under the type: " ++ show a) $ do 
  let (dat_para, dat_ix) = splitAt (length dat.dataPara) dat_args
                      -- ^ Split the arguments on data
  let para_def           = [ x := v | ((x,_,_), (v,_)) <- zip dat.dataPara dat_para ]
                      -- ^ Get the definitions of coresponding data parameters
  let ps_tele            = [ (x,i, quote ctx (eval (ctx <: para_def) t)) | (x,i,t) <- con.conPara ] -- TODO : to be optimized
                      -- ^ Telescope of constructor arguments
  trace ("\nChecking arguments: " ++ show ctx) do
  arg_res               <- checkP ctx ps_tele ps Nothing pvars
                      -- ^ Check constructor arguments
  let con_arg_def        = [ x := v | ((x,_,_), (v,_)) <- zip con.conPara arg_res.asValue ]
                      -- ^ Get the definitions of coresponding constructor arguments
  let ret_ix             = [ (eval (ctx <: para_def <: con_arg_def) t, i) | (t, i) <- con.retIx ]
                      -- ^ Get the returning indexes
  trace ("  - Unifying " ++ show ret_ix ++ " with " ++ show dat_ix) do 
  unify_res             <- unifySp (ctx <: arg_res.rhsDefs) arg_res.unifyRes ret_ix dat_ix
                      -- ^ Unification!
  let ret_val            = VCon con.conName $ allImplSp dat_para ++ arg_res.asValue
  trace ("Done checking constructor: \n- "++ show unify_res ++ "\n- " ++ show arg_res.rhsDefs ++ "\nend.\n") do
  pure arg_res
    { unifyRes = unify_res
    , asValue   = [(ret_val, i)]
    }

checkClause :: Context -> D.Fun -> D.Clause -> IO (Either Context (Term, Context))
checkClause ctx fun (D.Clause pat rhs) = case rhs of
  D.NoMatchFor x -> error "TODO" -- Return (Left rhs_ctx)
  D.Rhs t -> do 
    res <- lift $ checkP ctx fun.funPara pat (Just fun.funRetType) M.empty
    let rhs_ctx1 = ctx <: res.rhsDefs 
                       <: res.unifyRes
    let rhs_ctx = rhs_ctx1 {  bds = fetchBD rhs_ctx1 res.rhsDefs  }
    trace
      ("I'm checking clause for funcion: " ++ fun.funName 
      ++ "\n  - with context: " ++ show rhs_ctx
      ++ "\n  - with bds: " ++ show rhs_ctx.bds
      ) do 
    rhs <- C.check rhs_ctx t (fromJust res.rhsType)
    pure $ Right (rhs, rhs_ctx)
  where 
    fetchBD :: Context -> [ElabDef] -> BDs
    fetchBD ctx defs = 
      let names = [ name | (name, _) :=! _ <- defs ] 
      in foldr (\n bds -> M.insert n (if isFree ctx n then Bound else Defined) bds) M.empty names

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
  -- TODO : Coverage Check
  pure Fun 
    { funName = fun.funName
    , funPara = fun.funPara
    , funRetType = fun.funRetType
    , funClauses = if null rhss then Nothing else Just do
        (ps, Right (rhs, rhs_ctx)) <- rhss 
        pure Clause 
          { patterns = ps 
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
    | m < n     -> pure $ M.insert n (VPatVar m []) fore
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






