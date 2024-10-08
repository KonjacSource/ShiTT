module ShiTT.Termination.Ord where

import ShiTT.Context
import ShiTT.Syntax

data Order = Unsure | LessEq | Less
  deriving (Eq, Ord)

instance Show Order where
  show = \case
    Unsure -> "?"
    Less   -> "<"
    LessEq -> "<="

-- | Unsure as zero, LessEq as one, Less as infinity
instance Num Order where
  fromInteger 0 = Unsure
  fromInteger _ = LessEq

  x + y = max x y
    -- case (x, y) of 
    --   (Unsure, x) -> x -- Unsure as zero 
    --   (x, Unsure) -> x 
    --   (Less, x) -> Less -- Less as inf 
    --   (x, Less) -> Less 
    --   (LessEq, LessEq) -> LessEq

  x * y = case (x, y) of
    (Unsure, _) -> Unsure -- Unsure as zero
    (_, Unsure) -> Unsure
    (LessEq, x) -> x      -- LessEq as one
    (x, LessEq) -> x
    (Less, Less) -> Less

  abs = error "I hate Num"
  signum = error "I hate Num"
  negate = error "I hate Num"

maxOf :: Foldable f => f Order -> Order
maxOf = foldr (+) Unsure

minOf :: Foldable f => f Order -> Order
minOf = foldr min Less

-- | We would simply ignore the inaccessible patterns, so no need for context. 
--   It would not be a big problem, since we (usually) could show the decreasing by other accessible pattern .
compareTP :: Context -> Value -> Pattern -> Order
compareTP ctx e p = case (e, p) of
  (VVar x, p) -> compareNP ctx x p     -- This case might be useless
  (VPatVar x [], p) -> compareNP ctx x p
  (VCon con' [], PCon con ps _)
    | con' == con -> LessEq
  (VCon con' con_arg, PCon con pcon_arg _)
    | con' == con ->
        case lookupCon' con ctx of
          Just (dat, con) ->
            let data_para_leng = length dat.dataPara 
                con_arg' = map fst $ drop data_para_leng con_arg in
              if (length con_arg - data_para_leng) == length pcon_arg then
                minOf $ zipWith (compareTP ctx) con_arg' pcon_arg
              else
                Unsure
          _ -> Unsure
  _ -> Unsure

compareNP :: Context -> Name -> Pattern -> Order
compareNP ctx x = \case 
  PVar x' _ | x == x' -> LessEq
  PCon con ps _       -> Less * maxOf (map (compareNP ctx x) ps)
  _                   -> Unsure