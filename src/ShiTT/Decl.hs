module ShiTT.Decl where 

import ShiTT.Syntax
import Control.Monad (join)

type TelescopeTerm = [(Name, Icit, Type)]

-- data Data = Data 
--   { dataName :: Name 
--   , dataPara :: TelescopeTerm
--   , dataIx   :: TelescopeTerm
--   , dataCons :: [Constructor]
--   }

-- data Constructor = Constructor 
--   { conName :: Name 
--   , belongsTo :: Name 
--   , conPara :: TelescopeTerm
--   , retIx   :: [Term]
--   }

type InaccId = Int 

data Pattern 
  = PVar Name Icit 
  | PCon Name [Pattern] Icit -- TODO: Change to `PCon Constructor [Pattern] Icit`
  | PInacc InaccId Icit -- Deprecated  

icit :: Pattern -> Icit
icit = \case 
  PVar _ i -> i 
  PCon _ _ i -> i 
  PInacc _ i -> i

setIcit :: Icit -> Pattern -> Pattern 
setIcit i = \case 
  PVar x _ -> PVar x i 
  PCon x ps _ -> PCon x ps i 
  PInacc x _ -> PInacc x i

instance Show Pattern where 
  show = pp True where 
    paren _ Impl s = '{' : s ++ "}"
    paren False Expl s = '(' : s ++ ")"
    paren _ _ s = s 
    pp top = \case 
      PVar n i -> paren True i n
      PCon n ps i 
        | null ps -> paren True i n
        | otherwise -> paren top i (n ++ join (map ((' ' :) . pp False) ps))
      PInacc n i -> paren True i ('~':show n) 


data Fun = Fun 
  { funName :: Name 
  , funPara :: Telescope
  , funRetType :: Spine -> VType 
  , clauses :: [Clause]
  }

data Clause = Clause
  { patterns :: [Pattern]
  , clauseRhs :: Rhs   
  } deriving Show

data Rhs = Rhs Raw | NoMatchFor Name 
  deriving Show