{-# OPTIONS_GHC -Wno-orphans #-}
module ShiTT.Termination.Call where

import ShiTT.Eval
import ShiTT.Context
import Data.Matrix hiding (trace)
import qualified Data.Set as S
import ShiTT.Termination.Ord
import qualified Data.Vector as V
import Data.Maybe (fromJust)
-- import Debug.Trace (trace)
import qualified Data.Map as M

instance Ord e => Ord (Matrix e) where
  compare a b = compare (toList a) (toList b)

data CallMat = CallMat
  { fromFun :: Fun
  , callFun :: Fun
  , callMat :: Matrix Order
  } deriving (Eq, Ord)

trace a b = b

instance Show CallMat where
  show (CallMat f g a) = "\n-- from " ++ show f ++ " call " ++ show g ++ "\n" ++ show a ++ "\n"

-- Call matrix of call
------------------------

-- | The cm function from paper.
getCallMat :: Context -> (Fun, [Pattern]) -> (Fun, Spine) -> CallMat
getCallMat ctx clause@(f, ps) (g, es) = trace ("getting " ++ show clause ++ " " ++ show (g, es)) CallMat
  { fromFun = f
  , callFun = g
  , callMat = matrix (arity f) (arity g) \(i,j) ->
      if j <= length es then 
        compareTP ctx (fst $ es !! (j - 1)) (ps !! (i - 1))
      else
        Unsure
  }

type MutualSet = S.Set Fun
type CallSet = S.Set CallMat

-- Extraction of call matrices from expression
------------------------------------------------

-- | Initial call set
initCallSet :: Context -> MutualSet -> CallSet
initCallSet ctx mut = trace ("init call set: " ++ show mut) $ S.unions . flip map (S.toList mut) $ \fun ->
  S.unions $ [ extractClause mut ctx (fun, c) | c <- fromJust fun.funClauses ]

-- | ctx |- mut
extractCall :: MutualSet -> Context -> Fun -> [Pattern] -> Value -> CallSet
extractCall mut ctx fun ps t = trace ("extracting " ++ show mut ++ " " ++ show fun ++ show ps ++ " " ++ show t) case t of
  VFunc g sp
    | S.member g mut -> 
        S.insert (getCallMat ctx (fun, ps) (g, sp))
                 (S.unions $ self . fst <$> sp)
    | otherwise -> S.unions $ self . fst <$> sp
  VCon    g sp
    | g `elem` map funName (S.toList mut) -> 
        S.insert (getCallMat ctx (fun, ps) (fromJust (M.lookup g ctx.decls.allFunDecls), sp))
                 (S.unions $ self . fst <$> sp)
    | otherwise -> S.unions $ self . fst <$> sp
  VRig    _ sp -> S.unions $ self . fst <$> sp
  VPatVar _ sp -> S.unions $ self . fst <$> sp

  VLam x _ (Closure ctx' e) -> self (eval (ctx' <: freeVar x) e)
  VPi x _ a (Closure ctx' e) -> S.union (self a) (self $ eval (ctx' <: freeVar x) e)
  _ -> S.empty
  where
    self = extractCall mut ctx fun ps

extractClause :: MutualSet -> Context -> (Fun, Clause) -> CallSet
extractClause mut ctx (fun, Clause ps rhs_ctx rhs) = 
  trace ("extracting clause" ++ show mut ++ " " ++ show fun ++ show ps ++ " " ++ show rhs) extractCall mut ctx fun ps (eval rhs_ctx rhs)

-- Call Matrix composition
----------------------------

infixl 4 *#
(*#) :: CallMat -> CallMat -> CallMat
CallMat f g a *# CallMat g' h b
  | g == g'   = CallMat f h (a * b)
  | otherwise = error "Impossible"

-- Call set completion
-----------------------

-- TO BE OPTIMIZED
complete :: CallSet -> CallSet
complete cs
  | cs == cs' = cs
  | otherwise = complete cs'
  where
    cs' = S.union cs
        $ S.unions [ S.singleton (CallMat f h (a * b)) | CallMat f g a <- S.toList cs, CallMat g' h b <- S.toList cs, g == g'  ]

-- | Idempotent call matrix
idempotent :: CallMat -> Bool
idempotent (CallMat f g a) = f == g && a * a == a

class Decrease t where
  decreasing :: t -> Bool

instance Decrease Order where
  decreasing = \case
    Less -> True
    _ -> False

instance Decrease CallMat where
  decreasing (CallMat _ _ a) = any decreasing (V.toList (getDiag a))

instance Decrease CallSet where
  decreasing cs = all decreasing (S.filter idempotent cs)


