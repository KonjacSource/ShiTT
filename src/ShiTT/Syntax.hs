module ShiTT.Syntax where
import qualified Data.Map as M
import Text.Megaparsec (SourcePos)

data Icit = Impl | Expl deriving (Eq, Show)
data BD = Bound | Defined deriving (Eq, Show)
type BDs = M.Map Name BD

type MetaId = Int

type Name = String

data BindKind = Named Name | Unnamed Icit
  deriving (Show, Eq)

caseBindKind :: BindKind -> (Maybe Name -> c) -> c -> c
caseBindKind (Named n) f _ = f (Just n)
caseBindKind (Unnamed Impl) f _ = f Nothing
caseBindKind (Unnamed Expl) _ c = c

data Raw
  = RRef Name
  | RPVar Name
  | RLam Name BindKind Raw -- \x. t | \{x}. t | \{x = y}. t
  | RApp Raw Raw BindKind   -- t u  | t {u} | t {x = u}
  | RPi Name Icit Raw Raw
  | RLet Name Raw Raw Raw
  | RPrintCtx Raw
  | RU
  | SrcPos SourcePos Raw
  | Hole
  -- deriving Show
  
instance Show Raw where 
  show = \case 
    RRef n -> n 
    RPVar n -> n 
    RLam n b r -> "\\ " ++ n ++ ". " ++ show r
    RApp a b _ -> show a ++ " " ++ show b 
    RPi n _ t b -> "Pi " ++ n ++ ":" ++ show t ++ "." ++ show b 
    SrcPos _ r -> show r 
    _ -> "..."

data Term
  = Var Name
  | App Term Term Icit
  | Lam Name Icit Term
  | Pi Name Icit Type Term
  | Let Name Type Term Term
  | PrintCtx Term
  | Func Name -- Func or Con
  | Meta MetaId
  | PatVar Name
  | InsertedMeta MetaId BDs
  | Undefiend
  | U
  deriving (Show, Eq)

infixl 9 `eApp`
eApp :: Term -> Term -> Term
eApp f u = App f u Expl

tmAppSp :: Term -> TmSpine -> Term 
tmAppSp f sp = case sp of 
  [] -> f 
  (t,i):ts -> tmAppSp (App f t i) ts

type Type = Term
type TmSpine = [(Term, Icit)]
