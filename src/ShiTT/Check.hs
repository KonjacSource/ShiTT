{-# HLINT ignore #-}
module ShiTT.Check where 
import ShiTT.Context
import ShiTT.Syntax
import ShiTT.Meta

import Control.Exception
import Data.IORef
import ShiTT.Eval

import qualified Data.IntMap as I
import qualified Data.Map as M 
import Text.Megaparsec (sourcePosPretty)
import Debug.Trace (trace)

freshMeta :: Context -> IO Term 
freshMeta ctx = do
  m <- readIORef nextMeta
  writeIORef nextMeta (m + 1)
  modifyIORef' mctx $ I.insert m Unsolved
  pure $ InsertedMeta m ctx.bds

-- Unification
------------------------------------------
data UnifyError = UnifyError
  deriving (Show, Exception)

lamNameGen :: Int -> Name 
lamNameGen = ("$_" ++) . show

lams :: [Icit] -> Term -> Term 
lams = go 0 where
  go x [] t = t 
  go x (i:is) t = Lam (lamNameGen x) i $ go (x + 1) is t 

-- | [m1, m2, m3] |-> [m1 := $_0, m2 := $_1, m3 := $_2]
invert :: Context -> Spine -> IO [Def]
invert ctx sp = go [] sp 0 where 
  go used [] n = pure [] 
  go used ((v,_):vs) n = case force ctx v of 
    VVar x | x `notElem` used -> do -- distinct check and var check
      rest <- go (x : used) vs (n + 1) 
      pure $ (x := VVar (lamNameGen n)) : rest
    VPatVar x [] | x `notElem` used -> do -- distinct check and var check
      rest <- go (x : used) vs (n + 1) 
      pure $ (x := VVar (lamNameGen n)) : rest
    _ -> throwIO UnifyError

allMeta :: Term -> [MetaId]
allMeta = flip foldTerm [] $ \t acc -> case t of  
  Meta i -> i  : acc 
  InsertedMeta i _ -> i : acc 
  _ -> acc

--       Gamma      m         sp       rhs
solve :: Context -> MetaId -> Spine -> Value -> IO () 
solve ctx m sp rhs = do
  name_map <- invert ctx sp 
  let rhs_term = quote ctx rhs
  if m `notElem` allMeta rhs_term then do -- ocurrence check
    let solution = 
          eval (ctx {env = M.empty} <: name_map) $ 
            lams (map snd sp) $ 
              quote ctx $ eval (ctx {env = M.empty} <: name_map) rhs_term
    modifyIORef' mctx $ I.insert m (Solved solution)
  else 
    throwIO UnifyError

unifySp :: Context -> Spine -> Spine -> IO () 
unifySp ctx sp sp' = case (sp, sp') of 
  ([],       []        ) -> pure () 
  ((v,_):sp, (v',_):sp') -> unify ctx v v' >> unifySp ctx sp sp'
  _                      -> throwIO UnifyError

unify :: Context -> Value -> Value -> IO () 
unify ctx (refresh ctx -> t) (refresh ctx -> u) = -- trace ("UNIFYING: " ++ show t ++ " WITH " ++ show u) $ 
  case (t, u) of 
  ---
  (VU, VU) -> pure ()
  ---
  (VLam x i t, VLam y i' t') | i == i' -> let x' = freshName ctx x in 
    unify (ctx <: freeVar x') (t @ x := VVar x') (t' @ y := (VVar x'))
  ---
  (t', VLam x i  t ) -> let x' = freshName ctx x in 
    unify (ctx <: freeVar x') (vApp ctx t' (VVar x') i) (t @ x := VVar x')
  ---
  (VLam x i t, t') -> let x' = freshName ctx x in 
    unify (ctx <: freeVar x') (t @ x := VVar x') (vApp ctx t' (VVar x') i)
  ---
  (VPi x i a b, VPi x' i' a' b') | i == i' -> do 
    let fre = freshName ctx x 
    unify ctx a a'
    unify (ctx <: freeVar fre) (b @ x := VVar fre) (b' @ x' := VVar fre)
  ---
  (VCon con sp, VCon con' sp') | con == con' -> unifySp ctx sp sp' 
  ---
  (VFunc fun sp, VFunc fun' sp') | fun.funName == fun'.funName -> unifySp ctx sp sp' 
  ---
  (VRig x sp, VRig x' sp') | x == x' -> unifySp ctx sp sp' 
  --- 
  (VPatVar x sp, VRig x' sp') | x == x' -> unifySp ctx sp sp'
  ---
  (VRig x sp, VPatVar x' sp') | x == x' -> unifySp ctx sp sp'
  ---
  (VPatVar x sp, VPatVar x' sp') | x == x' -> unifySp ctx sp sp'
  ---
  (VFlex m sp, VFlex m' sp') | m == m' -> unifySp ctx sp sp' 
  --- solve
  (VFlex m sp, t') -> solve ctx m sp t'
  --- solve
  (t', VFlex m sp) -> solve ctx m sp t'
  --- error
  _ -> throwIO UnifyError
  
-- Type Check 
------------------------------------------

data ElabError
  = NameNotInScope Name
  | Can'tUnify Value Value 
  | InferNamedLam
  | NoNamedImplicitArg Name
  | IcitMismatch Icit Icit
  deriving (Exception)

instance Show ElabError where 
  show = \case 
    NameNotInScope name ->  "Unknow name: " ++ name 
    Can'tUnify v w -> "(Elaborator) Can't unify " ++ show v ++ " with " ++ show w ++ ""
    InferNamedLam -> "Can't infer the giving lambda"
    NoNamedImplicitArg name -> "There is no such implict name: " ++ name 
    IcitMismatch i i' -> "Expecting " ++ show i' ++ ", got " ++ show i

data Error = Error Context ElabError
  deriving Exception

instance Show Error where 
  show (Error ctx e) = "Error (" ++ show (sourcePosPretty <$> ctx.pos) ++ "): " ++ show e

type Anno = (Term, VType)

unifyGuard :: Context -> Value -> Value -> IO ()
unifyGuard ctx (force ctx -> v) (force ctx -> w) = 
  do
    unify ctx v w 
  `catch` \UnifyError -> 
    throwIO . Error ctx $ Can'tUnify (refresh ctx v) (refresh ctx w)

insert' :: Context -> IO Anno -> IO Anno
insert' ctx = (>>= go) where 
  go (t, t_ty) = case t_ty of 
    VPi x Impl a b -> do 
      m <- freshMeta ctx 
      go (App t m Impl, b @ x := eval ctx m)
    _ -> pure (t, t_ty)

insert :: Context -> IO Anno -> IO Anno 
insert ctx = (>>= \case
  (t@(Lam _ Impl _), v) -> pure (t, v)
  p                     -> insert' ctx (pure p) )

insertUntilName :: Context -> Name -> IO Anno -> IO Anno 
insertUntilName ctx name = (>>= go) where 
  go (t, v) = case force ctx v of 
    v@(VPi x Impl a b) -> do 
      if x == name then 
        pure (t, v)
      else do 
        m <- freshMeta ctx 
        go (App t m Impl, b @ x := eval ctx m)
    _ -> throwIO . Error ctx $ NoNamedImplicitArg name 

check :: Context -> Raw -> VType -> IO Term 
check ctx t v = {- trace ("checking: " ++ show t ++ " under " ++ show (refresh ctx v)) $ -} case (t, refresh ctx v) of 
  ---
  (SrcPos pos t, a) -> 
    check (ctx {pos = Just pos}) t a
  ---
  (RPrintCtx t, a) -> do 
    trace ("\n" ++ printContext ctx ++ "\n--------------------") $ trace (show (refresh ctx v) ++ "\n") $ do 
    t' <- check ctx t a
    pure $ PrintCtx t'
  ---
  (RLam x i t, VPi x' i' a b) 
    | caseBindKind i 
      (\case (Just name) -> i' == Impl && name == x'
             Nothing     -> i' == Impl)
      (i' == Expl)  
    -> Lam x i' <$> check (ctx <: x :! (a, Source)) t (b @ x := VVar x)
  ---
  (t, VPi x Impl a b) -> do 
    let x' = freshName ctx x 
    Lam x' Impl <$> check (ctx <: x :! (a, Inserted)) t (b @ x := VVar x)
  ---
  (RLet x a t u, u') -> do 
    a <- check ctx a VU 
    let va = eval ctx a 
    t <- check ctx t va 
    let vt = eval ctx t 
    u <- check (ctx <: (x, va) :=! vt) u u' 
    pure (Let x a t u)
  ---
  (Hole,  a) -> do 
    freshMeta ctx 
  ---
  (t, expected) -> do 
    (t, inferred) <- insert ctx $ infer ctx t 
    unifyGuard ctx expected inferred 
    pure t

infer :: Context -> Raw -> IO Anno 
infer ctx = \case 
  ---
  SrcPos pos t -> 
    infer ctx {pos = Just pos} 
          t
  ---
  RPrintCtx t -> do 
    trace (show ctx) $ do 
    (t', ty) <- infer ctx t 
    pure $ (PrintCtx t', ty)
  ---
  RRef ref ->  
    case M.lookup ref ctx.decls.allDataDecls of 
      Just dat -> pure (Func ref, getDataType ctx dat) 

      _ -> case M.lookup ref ctx.decls.allFunDecls of 
        Just fun -> pure (Func ref, getFunType ctx fun)
      
        Nothing -> case M.lookup ref ctx.types of 
          Just t -> pure (Var ref, fst t)
          Nothing -> throwIO . Error ctx $ NameNotInScope ref
  ---
  RPVar ref -> case M.lookup ref ctx.types of 
    Just t -> pure (PatVar ref, fst t)
    Nothing -> throwIO . Error ctx $ NameNotInScope ref
  ---
  RLam x (Unnamed i) t -> do 
    a <- eval ctx <$> freshMeta ctx 
    let ctx' = ctx <: x :! (a, Source) 
    (t, b) <- insert ctx' $ infer ctx' t 
    let empEnv = ctx {env = M.empty}
    pure (Lam x i t, VPi x i a $ closeVal ctx $ quote empEnv b)
  ---
  RLam x (Named _) t -> throwIO $ Error ctx InferNamedLam
  ---
  RApp t u i -> do 
    
    (i, t, t_ty) <- case i of 
      Named name -> do 
        (t, t_ty) <- insertUntilName ctx name $ infer ctx t 
        pure (Impl, t, t_ty)
      Unnamed Impl -> do 
        (t, t_ty) <- infer ctx t 
        pure (Impl, t, t_ty)
      Unnamed Expl -> do 
        (t, t_ty) <- insert' ctx $ infer ctx t
        pure (Expl, t, t_ty)
    -- trace (show $ force t_ty) $ do 
    (a, b, x) <- case force ctx t_ty of 
      VPi x i' a b ->  
        if i == i' then 
          pure (a, b, x)
        else 
          throwIO . Error ctx $ IcitMismatch i i' 
      t_ty -> do 
        a <- eval ctx <$> freshMeta ctx 
        let name = freshName ctx "x"
        b' <- freshMeta (ctx <: name :! (a, Source))
        let b = Closure ctx b' 
        unifyGuard ctx t_ty (VPi name i a b)
        pure (a, b, "_")

    u <- check ctx u a
    pure (App t u i, b @ x := eval ctx u)
  ---
  RU -> pure (U, VU)
  ---
  RPi x i a b -> do 
    a <- check ctx a VU 
    b <- check (ctx <: x :! (eval ctx a, Source)) b VU 
    pure (Pi x i a b, VU)
  ---
  RLet x a t u -> do 
    a <- check ctx a VU 
    let va = eval ctx a 
    t <- check ctx t va 
    let vt = eval ctx t 
    (u, b) <- infer (ctx <: (x, va) :=! vt) u
    pure (Let x a t u, b)
  ---
  Hole -> do 
    a <- eval ctx <$> freshMeta ctx 
    t <- freshMeta ctx 
    pure (t, a)
