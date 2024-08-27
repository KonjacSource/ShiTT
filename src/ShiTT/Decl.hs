module ShiTT.Decl where 

import qualified Data.Map as M 

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
  | PCon Name [Pattern] Icit 
  | PInacc InaccId Icit

icit :: Pattern -> Icit
icit = \case 
  PVar _ i -> i 
  PCon _ _ i -> i 
  PInacc _ i -> i

instance Show Pattern where 
  show = pp True where 
    paren _ Impl s = '{' : s ++ "}"
    paren False Expl s = '(' : s ++ ")"
    paren _ _ s = s 
    pp top = \case 
      PVar n i -> paren True i n
      PCon n ps i -> paren top i (n ++ join (map ((' ' :) . show) ps))
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
  }

data Rhs = Rhs Raw | NoMatchFor Name 