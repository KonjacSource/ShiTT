module ShiTT.Decl where 

import ShiTT.Syntax
import ShiTT.Context (Pattern, Telescope)
import qualified ShiTT.Context as C
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


data Fun = Fun 
  { funName :: Name 
  , funPara :: Telescope
  , funRetType :: Term
  , clauses :: [Clause]
  }

data Clause = Clause
  { patterns :: [Pattern]
  , clauseRhs :: Rhs   
  } deriving Show

data Rhs = Rhs Raw | NoMatchFor Name 
  deriving Show


data HConstructor = HConstructor
  { hconName :: Name 
  , hconClauses :: [Clause]
  }

asPrim :: Fun -> C.Fun
asPrim fun = C.Fun 
  { C.funName = fun.funName
  , C.funPara = fun.funPara
  , C.funRetType = fun.funRetType
  , C.funClauses = Nothing
  }