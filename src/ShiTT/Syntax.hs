module ShiTT.Syntax where
import qualified Data.Map as M
import Text.Megaparsec (SourcePos)

data Icit = Impl | Expl deriving (Eq, Show)
data BD = Bound | Defined deriving (Eq, Show)
type BDs = M.Map Name BD

type Spine = [(Value, Icit)]
type Telescope = [(Name, Icit, VType)]

-- for evaluation 
-- NOTE: this may cause some issue, 
-- since the Map dosn't store the message of dependency of vars.
-- And we will apply a meta to the context vars.
-- The generated lambda term may not be well-typed, 
-- but this is OK if don't check the type of it.
-- If it needs to be changed, remember to change @eval ctx (InsertedMeta m bds)@ also.
type Env = M.Map Name Value

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
  
  

instance Show Raw where 
  show = show . toV where 
    toIcit = \case 
      Unnamed i ->  i
      Named _ -> Impl
    toV = \case 
      RRef x -> VVar x 
      RPVar x -> VVar x 
      RLam x i t -> VLam x (toIcit i) $ const (toV t)
      RApp a b i -> VRig (show a) [(toV b, toIcit i)]
      RU -> VU
      SrcPos _ r -> toV r
      _ -> error "undefined"

data Term
  = Var Name
  | App Term Term Icit
  | Lam Name Icit Term
  | Pi Name Icit Type Term
  | Let Name Type Term Term
  | PrintCtx Term
  | Func Name
  | Meta MetaId
  | PatVar Name
  | InsertedMeta MetaId BDs
  | U
  deriving (Show, Eq)

infixl 9 `eApp`
eApp :: Term -> Term -> Term
eApp f u = App f u Expl

data Value
  = VLam Name Icit (Value -> Value)
  | VRig Name Spine
  | VCon Name Spine
  | VFlex MetaId Spine
  | VPatVar Name Spine
  | VFunc Name Spine
  | VPi Name Icit VType (Value -> Value)
  | VU

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

type Type = Term

type VType = Value

pattern VVar :: Name -> Value
pattern VVar x = VRig x []

pattern VMeta :: MetaId -> Value
pattern VMeta m = VFlex m []

instance Show Value where
  show = pp True -- . force
    where
      ppSp [] = ""
      ppSp ((v, Expl):rest) = ' ' : pp False v ++ ppSp rest
      ppSp ((v, Impl):rest) = " {" ++ pp True v ++ '}' : ppSp rest
      remove_infix = \case
        -- ('-':n) -> n
        n -> n
      pp is_top = \case
        VLam x Expl b -> inParen $ "lambda " ++ x ++ ". " ++ pp True (b (VVar x))
        VLam x Impl b -> inParen $ "lambda {" ++ x ++ "}. " ++ pp True (b (VVar x))
        VRig x sp -> if null sp then remove_infix x else inParen $ x ++ ppSp sp
        VCon x sp -> {-"!con!" ++-} pp is_top (VRig x sp)
        VFlex m sp -> pp is_top (VRig ('?':show m) sp)
        VFunc x sp -> {-"!fun!" ++-} pp is_top (VRig x sp)
        VPatVar x sp -> "!pat!" ++ pp is_top (VRig x sp)
        VPi x Expl t b -> inParen $ "Pi (" ++ x ++ ":" ++ pp True t ++ "). " ++ pp True (b (VVar x))
        VPi x Impl t b -> inParen $ "Pi {" ++ x ++ ":" ++ pp True t ++ "}. " ++ pp True (b (VVar x))
        VU -> "U"
        where paren x = '(' : x ++ ")"
              inParen x = if is_top then x else paren x