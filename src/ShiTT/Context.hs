{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore #-}
{-# LANGUAGE FlexibleInstances #-}
module ShiTT.Context where

import ShiTT.Syntax
import qualified Data.Map as M
import Text.Megaparsec (SourcePos)

data NameOrigin = Inserted | Source 
  deriving (Eq, Show)
  
type Types = M.Map String (VType, NameOrigin)

data Context = Context
  { decls :: Decls
  , env   :: Env
  , types :: Types
  , bds   :: BDs
  , pos   :: Maybe SourcePos
  } 

instance Show Context where 
  show decl = "\n- env:" ++ show decl.env ++ "\n- typ:" ++ show decl.types ++ "\n"

emptyCtx :: Context
emptyCtx = Context
  { decls = emptyDecls
  , env = M.empty
  , types = M.empty
  , bds = M.empty
  , pos = Nothing
  }


infixl 4 <: 
infix 5 :=, :~, :!, :=!

-- | Use this when you don't need check type, only for evaluate.
data Def = Name := Value
data Bind = Name :~ (VType, NameOrigin) 

getType :: Name -> [Bind] -> Maybe VType 
getType x = \case 
  [] -> Nothing 
  ((x':~(v,_)):rs) 
    | x == x' -> Just v
    | otherwise -> getType x rs

instance Show Def where 
  show (x := v) = x ++ " := " ++ show v

instance Show Bind where 
  show (x :~ (t, Source)) = x ++ " : " ++ show t  
  show (x :~ (t, Inserted)) = x ++ " : " ++ show t ++ " (Inserted) "

-- | Use this when you need to check type.
data ElabBind = Name :! (VType, NameOrigin)
data ElabDef  = (Name, VType) :=! Value

class Insertable t f where
  (<:) :: t -> f -> t

instance Insertable Context Def where
  ctx@(env -> env) <: x := v = ctx { env = M.insert x v env , bds = M.insert x Defined ctx.bds }

instance Insertable Context Bind where 
  ctx@(types -> types) <: x :~ b = ctx { types = M.insert x b types, bds = M.insert x Bound ctx.bds }

instance Insertable Context ElabBind where 
  ctx <: x :! b = ctx 
    { types = M.insert x b ctx.types
    , bds = M.insert x Bound ctx.bds
    , env = M.insert x (VVar x) ctx.env }
  
instance Insertable Context ElabDef where 
  ctx <: (x, t) :=! v = ctx 
    { types = M.insert x (t, Source) ctx.types
    , bds = M.insert x Defined ctx.bds 
    , env = M.insert x v ctx.env
    }

instance Insertable t f => Insertable t [f] where 
  ctx <: [] = ctx 
  ctx <: (x:xs) = (ctx <: x ) <: xs



freeVar :: Name -> Def
freeVar x = x := VVar x

-- Declarations
--------

data Fun = Fun 
 { funName :: Name
 , funPara :: Telescope
 , funRetType :: Spine -> VType -- funPara |- type
 , funVal  :: Context -> Spine -> Maybe Value
 }

instance Show Fun where 
  show = funName

argNum  :: Fun -> Int
argNum = length . funPara

data Data = Data 
  { dataName :: Name 
  , dataPara :: Telescope
  , dataIx   :: Telescope
  , dataCons :: [Constructor] 
  }

lookupCon :: Name -> Data -> Maybe Constructor
lookupCon n d = go d.dataCons where 
  go [] = Nothing 
  go (c:cs) = if c.conName == n then Just c else go cs

lookupCon' :: Name -> Context -> Maybe (Data, Constructor)
lookupCon' con_name (allDataDecls . decls -> datas) = 
  let dat_ls = M.toList $ M.filter (\dat -> con_name `elem` map conName dat.dataCons) datas in 
  case dat_ls of 
    [] -> Nothing 
    ((_, dat):_) -> do 
      con <- lookupCon con_name dat
      pure (dat, con)
  
instance Show Data where 
  show = dataName

data Constructor = Constructor
  { conName :: Name 
  , belongsTo :: Name 
  , conPara :: Telescope -- dataPara |- telescope
  , retIx   :: Spine -> Spine -- (dataPara ++ conPara) |- spine
  }

instance Show Constructor where 
  show = conName

data Decls = Decls 
  { definedNames :: [Name]
  , allDataDecls :: M.Map Name Data
  , allFunDecls  :: M.Map Name Fun
  } deriving Show


hasName :: Decls -> Name -> Bool 
(definedNames -> names) `hasName` name = name `elem` names 

appData :: Data -> [Value] -> Value 
appData dat sp = VCon dat.dataName (map (\((_,i,_), v) -> (v,i)) (zip (dat.dataPara ++ dat.dataIx) sp))


insertData :: Data -> Decls -> Decls 
insertData dat decls = Decls 
  { definedNames = [con.conName | con <- dat.dataCons] ++ dat.dataName : decls.definedNames 
  , allDataDecls = M.insert dat.dataName dat decls.allDataDecls
  , allFunDecls = foldr 
      (\con ->
        M.insert
          con.conName 
          Fun 
            { funName = con.conName
            , funPara = allImpl dat.dataPara ++ con.conPara
            , funRetType = \ sp -> 
                let (para, _) = splitAt (length dat.dataPara) sp in 
                appData dat (map fst $ para ++ con.retIx sp)
            , funVal = \_ sp -> Just $ VCon con.conName sp 
            }
          )
      (M.insert 
        dat.dataName 
        Fun 
          { funName = dat.dataName
          , funPara = dat.dataPara ++ dat.dataIx
          , funRetType = \ _ -> VU 
          , funVal = \_ sp -> Just $ VCon dat.dataName sp
          } 
        decls.allFunDecls)
      dat.dataCons
  }
  where allImpl [] = [] 
        allImpl ((x,_,t):xs) = (x, Impl, t) : allImpl xs
        
insertFun :: Fun -> Decls -> Decls
insertFun fun@(funName -> name) decls = decls 
  { definedNames = name : decls.definedNames
  , allFunDecls = M.insert name fun decls.allFunDecls
  }

emptyDecls :: Decls
emptyDecls = Decls 
  { definedNames = []
  , allFunDecls = M.empty
  , allDataDecls = M.empty
  }

