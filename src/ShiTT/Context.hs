{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore #-}
{-# LANGUAGE InstanceSigs #-}
module ShiTT.Context where

import ShiTT.Syntax
import qualified Data.Map as M
import Text.Megaparsec (SourcePos)
import Control.Monad (join)
import Data.List (nub)

-- Value
----------------------------------
type Spine = [(Value, Icit)]
type Telescope = [(Name, Icit, Term)]

-- for evaluation 
-- NOTE: this may cause some issue, 
-- since the Map dosn't store the message of dependency of vars.
-- And we will apply a meta to the context vars.
-- The generated lambda term may not be well-typed, 
-- but this is OK if don't check the type of it.
-- If it needs to be changed, remember to change @eval ctx (InsertedMeta m bds)@ also.
type Env = M.Map Name Value

data Closure = Closure
  { cloctx  :: Context
  , cloterm :: Term
  } -- deriving Show


data Value
  = VLam Name Icit Closure
  | VRig Name Spine
  | VCon Name Spine
  | VFlex MetaId Spine
  | VPatVar Name Spine
  | VFunc Fun Spine
  | VPi Name Icit VType Closure
  | VU
  -- deriving Show

foldTerm :: (Term -> b -> b) -> b -> Term -> b
foldTerm f acc t = case t of
  App a b _   -> deal [a,b]
  Lam _ _ b   -> deal [b]
  Pi _ _ a b  -> deal [a,b]
  Let _ a b c -> deal [a,b,c]
  _           -> deal []
  where
    deal xs = f t $ ffold xs
    ffold [] = acc
    ffold (x:xs) = foldTerm f (ffold xs) x

type VType = Value

pattern VVar :: Name -> Value
pattern VVar x = VRig x []

pattern VMeta :: MetaId -> Value
pattern VMeta m = VFlex m []


freeVarOfTm :: Term -> [Name]
freeVarOfTm = \case 
  Var x -> [x]
  App a b _ -> nub $ freeVarOfTm a ++ freeVarOfTm b
  Lam x _ t -> filter (/= x) $ freeVarOfTm t 
  Pi x _ a b -> nub $ freeVarOfTm a ++ filter (/= x) (freeVarOfTm b)
  Let x a b c -> nub $ freeVarOfTm a ++ freeVarOfTm b ++ filter (/= x) (freeVarOfTm c)
  PrintCtx t -> freeVarOfTm t 
  _ -> []

freeVarOf :: Value -> [Name]
freeVarOf = \case 
  VRig x sp -> x : freeVarOfSp sp
  VCon _ sp -> freeVarOfSp sp 
  VFlex _ sp -> freeVarOfSp sp 
  VPatVar x sp -> x : freeVarOfSp sp 
  VFunc _ sp -> freeVarOfSp sp 
  VLam x _ (Closure _ term) -> filter (/= x) $ freeVarOfTm term 
  VPi x _ a (Closure _ term) -> nub $ freeVarOf a ++ filter (/= x) (freeVarOfTm term)
  VU -> []

freeVarOfSp :: Spine -> [Name] 
freeVarOfSp = \case 
  [] -> []
  (x,_):sp -> nub (freeVarOf x ++ freeVarOfSp sp)

-- Ctx
-----------------------------------
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

-- instance Show Context where 
--   show decl = "\n- env:" ++ show decl.env ++ "\n- typ:" ++ show decl.types ++ "\n"

infixl 4 <: 
infix 8 :=, :~, :!, :=!

-- | Use this when you don't need check type, only for evaluate.
data Def = Name := Value
data Bind = Name :~ (VType, NameOrigin) 

getType :: Name -> [Bind] -> Maybe VType 
getType x = \case 
  [] -> Nothing 
  ((x':~(v,_)):rs) 
    | x == x' -> Just v
    | otherwise -> getType x rs

getName :: Value -> Maybe Name 
getName = \case 
  VRig x _ -> Just x 
  VPatVar x _ -> Just x 
  _ -> Nothing 


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

instance Insertable Context (M.Map Name Value) where 
  ctx <: m = (ctx <: map (uncurry (:=)) (M.toList m))

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

isFree :: Context -> Name -> Bool 
isFree ctx name = case M.lookup name ctx.env of 
  Just (getName -> Just n) | n == name -> True 
  _ 
    | head name == '*' -> True
    | otherwise -> False

-- Declarations
----------------

data Pattern 
  = PVar Name Icit 
  | PCon Name [Pattern] Icit -- TODO: Change to `PCon Constructor [Pattern] Icit`

icit :: Pattern -> Icit
icit = \case 
  PVar _ i -> i 
  PCon _ _ i -> i 

setIcit :: Icit -> Pattern -> Pattern 
setIcit i = \case 
  PVar x _ -> PVar x i 
  PCon x ps _ -> PCon x ps i 

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


data Clause = Clause 
  { patterns  :: [Pattern] 
  , rhsContext :: Context 
  , clauseRhs :: Term
  }

data Fun = Fun 
 { funName :: Name
 , funPara :: Telescope
 , funRetType :: Type -- funPara |- funRetType
 , funClauses :: Maybe [Clause]
 }

instance Eq Fun where 
  f == g = f.funName == g.funName

instance Ord Fun where 
  compare f g = compare f.funName g.funName

instance Show Fun where 
  show = funName

arity  :: Fun -> Int
arity = length . funPara

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
  { conName   :: Name 
  , belongsTo :: Name 
  , conPara   :: Telescope -- dataPara |- conPara
  , retIx     :: TmSpine   -- (dataPara ++ conPara) |- retIx
  }

instance Show Constructor where 
  show = conName

-- Signatures
data Decls = Decls 
  { definedNames :: [Name]
  , allDataDecls :: M.Map Name Data
  , allFunDecls  :: M.Map Name Fun
  } deriving Show


hasName :: Decls -> Name -> Bool 
(definedNames -> names) `hasName` name = name `elem` names 

-- App spine on the data, i.e. Vec A n
appData :: Data -> [Value] -> Value 
appData dat sp = VCon dat.dataName (map (\((_,i,_), v) -> (v,i)) (zip (dat.dataPara ++ dat.dataIx) sp))

insertData :: Data -> Decls -> Decls 
insertData dat decls = Decls 
  { definedNames = [con.conName | con <- dat.dataCons] ++ dat.dataName : decls.definedNames 
  , allDataDecls = M.insert dat.dataName dat decls.allDataDecls
  , allFunDecls = foldr 
      -- add Constructor definitions
      ( \con ->
          M.insert
            con.conName 
            Fun 
              { funName = con.conName
              , funPara = allImpl dat.dataPara ++ con.conPara
              , funRetType = tmAppSp (Func dat.dataName) $ teleSpine dat.dataPara ++ con.retIx
              -- \ sp -> let (para, _) = splitAt (length dat.dataPara) sp in appData dat (map fst $ para ++ con.retIx sp)
              , funClauses = Nothing  -- \_ sp -> Just $ VCon con.conName sp 
              }
      )
      -- add Data definition
      ( M.insert 
          dat.dataName 
          Fun 
            { funName = dat.dataName
            , funPara = dat.dataPara ++ dat.dataIx
            , funRetType = U 
            , funClauses = Nothing
            }
          decls.allFunDecls
      )
      dat.dataCons
  }
  where 
    teleSpine :: Telescope -> TmSpine
    teleSpine = \case 
      [] -> [] 
      (x,i,_) : ts -> (Var x, i) : teleSpine ts

mkPatterns :: Telescope -> ([Name], [Pattern])
mkPatterns [] = ([], [])
mkPatterns ((x,i,t):ts) = 
  let x' = x ++ show (length ts) 
      (names,ps) = mkPatterns ts
  in (x':names, PVar x' i : ps)

allImpl :: Telescope -> Telescope
allImpl [] = [] 
allImpl ((x,_,t):xs) = (x, Impl, t) : allImpl xs

allImplSp :: Spine -> Spine 
allImplSp [] = [] 
allImplSp ((x,_):xs) = (x,Impl) : allImplSp xs

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

emptyCtx :: Context
emptyCtx = Context
  { decls = emptyDecls
  , env = M.empty
  , types = M.empty
  , bds = M.empty
  , pos = Nothing
  }

closeVal :: Context -> Term -> Closure 
closeVal ctx tm = Closure (ctx {env = M.empty}) tm