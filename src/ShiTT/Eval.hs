{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module ShiTT.Eval where 

import ShiTT.Syntax
import ShiTT.Context
import qualified Data.Map as M
import Data.Maybe (fromJust)
import ShiTT.Meta
import Common
import Debug.Trace (trace)
import Control.Monad (join)
import Data.List (nub)

eval :: Context -> Term -> Value 
eval ctx@(env -> env) = \case
  ---
  Var x               -> case M.lookup x env of 
    Just v -> v 
    Nothing -> VVar x
  ---
  App t u i           -> vApp (eval ctx t) (eval ctx u) i
  ---
  Lam x i t           -> VLam x i (\ v -> eval (ctx <: x := v) t)
  ---
  Pi x i t b          -> VPi x i (eval ctx t) (\ v -> eval (ctx <: x := v) b)
  ---
  Let x _ t u         -> eval (ctx <: x := eval ctx t) u
  ---
  Func name           -> case M.lookup name ctx.decls.allFunDecls of 
    Nothing -> error $ "Unknow identifier: " ++ name ++ "\n" ++ show ctx.decls.allFunDecls
    Just f  -> vCall ctx f f.funPara
  ---
  U                   -> VU 
  ---
  PrintCtx t          -> trace (show ctx) $ eval ctx t
  ---
  Meta m              -> vMeta m
  --
  PatVar x            -> case M.lookup x env of 
    Just v -> v 
    Nothing -> VPatVar x [] -- they are free-able
  ---
  InsertedMeta m bds  ->
    let avail_vars = M.filterWithKey (\ name _ -> fromJust (M.lookup name bds) == Bound) env in 
    vAppSp (vMeta m) (map (,Expl) (snd <$> M.toList avail_vars)) 
    -- I don't care the order, since I'm using HOAS

quoteSp :: Context -> Term -> Spine -> Term
quoteSp ctx t = \case 
  []            -> t 
  ((u, i) : xs) -> quoteSp ctx (App t (quote ctx u) i) xs 

quote :: Context -> Value -> Term 
quote ctx (force -> t) =
  case t of
    VRig  x sp  -> quoteSp ctx (Var x)  sp
    VCon  x sp  -> quoteSp ctx (Func x) sp 
    VFlex m sp  -> quoteSp ctx (Meta m) sp 
    VPatVar x sp -> quoteSp ctx (PatVar x) sp
    VFunc x sp  -> quoteSp ctx (Func x) sp 
    VU          -> U 
    VLam x i b  -> binder (\x' b' -> Lam x' i b') (freshName ctx x) b
    VPi x i t b -> binder (\x' b' -> Pi x' i (quote ctx t) b') (freshName ctx x) b
  where 
    binder :: (Name -> Term -> Term) -> Name -> (Value -> Value) ->  Term 
    binder con x b = con x (quote (ctx <: x := VVar x) (b (VVar x))) 

normalize :: Context -> Term ->  Term 
normalize ctx term = quote ctx (eval ctx term) 

-- preQuote :: (Ctx -> Name -> String) -> Ctx -> Value -> Term
-- preQuote fresh ctx = \case
--   VVar x -> Var x
--   VApp f t -> App (preQuote fresh ctx f) (preQuote fresh ctx t)
--   VLam x t b -> binder Lam (fresh ctx x) t b
--   VPi x t b -> binder Pi (fresh ctx x) t b
--   VFunc name (fmap (preQuote fresh ctx) -> spine) -> Call name spine
--   VU -> U
--   where 
--    binder con x t b = 
--      con x (preQuote fresh ctx t) 
--            (preQuote fresh (define ctx x (VVar x) 
--                (b (VVar x)))

freshName :: Context -> Name -> Name
freshName ctx@(env -> env) = \case
  "_" -> "_"
  x -> case M.lookup x env of
    Nothing | x `notElem` ctx.decls.definedNames -> x
            | otherwise -> go x (0 :: Int)
    Just _ -> go x (0 :: Int)
  where
    go x n = let x' = x ++ show n in
      case M.lookup x' env of
        Nothing | x `notElem` ctx.decls.definedNames -> x'
                | otherwise -> go x (n + 1)
        Just _ -> go x (n + 1)

freshName' :: [Name] -> Name -> Name
freshName' ls = \case
  "_" -> "_"
  x -> if x `elem` ls then 
      go x 0 
    else
      x  
  where
    go x n = let x' = x ++ show n in
      case x' `elem` ls of
        False -> x'
        True -> go x (n + 1)

vApp :: Value -> Value -> Icit -> Value
vApp t u i = case t of 
  VLam _ _ f -> f u 
  VFlex m sp -> VFlex m (sp >>> (u, i))
  VRig  x sp -> VRig  x (sp >>> (u, i))
  VPatVar x sp -> VPatVar x (sp >>> (u, i))
  _ -> error "Impossible"

vAppSp :: Value -> Spine -> Value 
vAppSp t sp = revCase sp 
 {- sp == []   -> -} t 
 (\fore (u, i) ->    vApp (vAppSp t fore) u i)

force :: Value -> Value
force t@(VFlex m sp) = 
  case lookupMeta m of 
    Unsolved -> t
    Solved v -> force (vAppSp v sp)
force t = t 

vMeta :: MetaId ->  Value 
vMeta m = 
  case lookupMeta m of 
    Unsolved -> VMeta m
    Solved v -> v

vCall :: Context -> Fun -> Telescope ->  Value
vCall ctx f ls = helper ctx [] ls 
  where 
    helper ctx' arg [] = pushDone f ctx' arg
    helper ctx' arg ((freshName ctx' -> x,i,t):xs) = VLam x i (\ v -> helper (ctx' <: x := v) (arg >>> (v, i)) xs)

-- vCall f ls = helper [] ls
--   where helper arg [] = f arg
--         helper arg ((x,i,t):xs) = VLam x i (\ v -> helper (arg >>> (v, i)) xs)

pushFun :: Context -> Value ->  Value 
pushFun ctx v@(VFunc name sp) = do 
  let fun = fromJust $ M.lookup name ctx.decls.allFunDecls
  case fun.funVal ctx sp of 
    Nothing -> v
    Just next -> pushFun ctx next 
pushFun ctx v = v 

-- This might be unnecessary
pushDone :: Fun -> Context -> Spine ->  Value 
pushDone fun@(funVal -> f) ctx sp = do 
  case f ctx sp of 
    Nothing -> VFunc fun.funName sp 
    Just res' -> res'

pushCall :: Context -> Name -> Spine -> Value
pushCall ctx name sp = pushFun ctx (VFunc name sp)


refresh :: Context -> Value -> Value 
refresh ctx = eval ctx . quote ctx 

--------------------------------------------------------------------------------------------

-- stackoverflow : subst ("A" := VPatVar "-A" [])  (VPi "_" Expl (VVar "A") (\_ -> VU))
-- TODO : Value ---quote--> Term ---subst--> Term ---eval---> Value
subst :: Def -> Value -> Value 
subst d@(x := v) t = case t of 
  VRig n sp | n == x -> vAppSp v $ substSp d sp 
            | otherwise -> VRig n $ substSp d sp 
  VPatVar n sp | n == x -> vAppSp v $ substSp d sp 
               | otherwise -> VPatVar n $ substSp d sp 
  
  VLam x' i f -> VLam x' i $ \v -> subst d (f v)
  VCon n sp -> VCon n $ substSp d sp 
  VFlex m sp -> VFlex m $ substSp d sp
  VFunc m sp -> VFunc m $ substSp d sp 
  VPi x' i a b -> VPi x' i (subst d t) (\v -> subst d (b v)) -- This is so wrong
  VU -> VU

substSp :: Def -> Spine -> Spine
substSp d = \case 
  [] -> []
  (v, i):rest -> (subst d v, i) : substSp d rest 

substTelescope :: Def -> Telescope -> Telescope
substTelescope d@(x':=_) = \case 
  [] -> []
  (x,i,t):rest | x /= x' -> (x,i,subst d t) : substTelescope d rest
               | otherwise -> (x, i, subst d t) : rest 
substDefs :: Def -> [Def] -> [Def]
substDefs d = \case 
  [] -> [] 
  (x := v):rest -> (x := subst d v) : substDefs d rest

exe :: (Def -> a -> a) -> [Def] -> a -> a 
exe sub [] a = a 
exe sub (b:bs) a = sub b (exe sub bs a)

getFunType :: Context -> Fun -> VType 
getFunType ctx fun = go ctx [] fun.funPara where 
  go ctx args [] = fun.funRetType args  
  go ctx args ((x,i,t):xs) = 
    VPi x i (refresh ctx t) (\v -> go (ctx <: (x := v)) (args >>> (v,i)) xs)

getDataType :: Context -> Data -> VType 
getDataType ctx dat = go ctx (dat.dataPara ++ dat.dataIx) where 
  go ctx [] = VU
  go ctx ((x,i,t):xs) = VPi x i (refresh ctx t) (\v -> go (ctx <: (x := v)) xs)


-- The ctx must have the new values
subst' :: Context -> [Def] -> Value -> Value 
subst' ctx defs v = refresh (ctx <: defs) v

substSp' :: Context -> [Def] -> Spine -> Spine
substSp' ctx d = \case 
  [] -> []
  (v, i):rest -> (subst' ctx d v, i) : substSp' ctx d rest 

-- TODO : BUG, to fix this, may need to rewrite a lot. Or add a prefix on telescope variables
--  substTelescope' (testContext <: "x" := VVar "x") [("A" := VVar "x")] idData.dataIx
--  ==> [("x",Expl,x),("y",Expl,x)]
substTelescope' :: Context -> [Def] -> Telescope -> Telescope
substTelescope' ctx ds = \case 
  [] -> []
  (x,i,t):rest -> (x,i,subst' ctx ds t) : substTelescope' (ctx <: x :! (t, Source)) (rm x ds) rest
  where rm x [] = []
        rm x (d@(x':=_):xs) 
          | x == x' = rm x xs 
          | otherwise = d : rm x xs

substDefs' :: Context -> [Def] -> [Def] -> [Def]
substDefs' ctx ds = \case 
  [] -> [] 
  (x := v):rest -> (x := subst' ctx ds v) : substDefs' ctx ds rest

freeVarOf :: Context -> Value -> [Name]
freeVarOf ctx = nub . go ctx [] where 
  goSp ctx bound sp = join (go ctx bound <$> map fst sp)
  go ctx bound = \case
    VRig n sp | n `elem` bound -> goSp ctx bound sp
              | otherwise      -> [n] ++ goSp ctx bound sp
    VPatVar n sp | n `elem` bound -> goSp ctx bound sp
              | otherwise      -> [n] ++ goSp ctx bound sp
    VCon _ sp -> goSp ctx bound sp 
    VFunc _ sp -> goSp ctx bound sp 
    VFlex _ sp -> trace ("error: unsolved meta") $ goSp ctx bound sp
    VLam x _ b -> let x' = freshName ctx x in go (ctx <: freeVar x') (x':bound) (b (VVar x'))
    VPi x _ t b -> let x' = freshName ctx x 
                       tf = go ctx bound t 
                   in  tf ++ go (ctx <: freeVar x') (x':bound) (b (VVar x'))
    VU -> []
                        
