# Implementation Note on ShiTT

Up to now, ShiTT is almost a proof assistant. It follows the style of Agda, a neat dependently typed language without native support for tactic. There are benefits of lackness of tactics. It is easy to implement and it can show the idea of Curry and Howard much more clear. And it is more readable than tactic based proof (at least on paper).

ShiTT supports Indexed Data Type and the Pattern Matching on it. Those features are important to the expressive power of ShiTT. It took me a lot of time to write.

So, I decide to take some notes before I forget those details.

## Elaborator

### Idea and Notice

The core part of ShiTT is an elaborator based on pattern-unification, which is an algorithm that solves meta variables during type checking. I learnt this from András Kovács' [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo). However, there are some differences because of evaluator. In elaboration-zoo, the environment of evaluator is `[Value]`, and indexed by De Bruijn indexes. While in ShiTT, I use `Map String Value` as environment, because I'm lazy to count the indexes. This could cause a little tiny problem. Before we show the problem, let us review the basic idea of pattern-unification.

The algorithm is pretty simple. First we introduce a new kind of variables called meta variable. And it could be inserted manually (by "_") or automentally. They are flexible variables, which means they can be unified by other terms during type checking. We store those flexibles globally, while the solution of metas may depend on some local variables. And this will become a problem when a meta refers to another meta in another context. So we need count the context of a meta in the solution. How do we do that. The most easy way is to use lambda-abstraction. We bind all the variables in context of the solving meta in a long lambda. And we apply the solution to all the variables. Like this,

```haskell
\(a : U) (x : a) . id {?1 a x} x
```

And we can solve `?1` by.

```haskell
?1 = \a x . a
```

This won't be a problem in ShiTT, until...
Consider the following term.

```haskell
\(X : U) (A : X -> U) (x : X) (a : A x). id {_} a
```

Here `a` is a variable, and its type depend on an other variable `x`.
And there is a hole in `body`, How do we insert the meta on to that hole? Obviously, it should be `?1 X A x a`. BUT, in ShiTT, I used `Map`, I have no way to know the dependency of `x` and `a`. I can only insert them by lexicographic order, which `?1 a A x X`. And the solution is then `?1 = \a A x X. A x`. It not well-typed! Fortunately, it is safy if we do not check the type of the solution of `?1`, and we do NOT need to.

There are still some thing to notice when we try to solve the meta variables under pattern match. We will get to this later.

### Implementaion

There are three syntax trees for different usage.

- `ShiTT.Syntax.Raw` unchecked input format.
- `ShiTT.Syntax.Term` checked, elaborated but not normalized.
- `ShiTT.Context.Value` checked, elaborated and normalized.

Two mutual type check functions (standard bidirectional type check).

- `ShiTT.Check.check :: Context -> Raw -> VType -> IO Term`
- `ShiTT.Check.infer :: Context -> Raw -> IO (Term, VType)`

`check` will check a `Raw` under the given `Context`, and return the `Term` after elaborate, if succeed.

`infer` will try to inference the type of given `Raw`, return the elaborated `Term` and its type.

If you are writting a implementation of MLTT without meta variable solving. You will need a function to check if two terms are judgementally equal. But now we need to replace the equal with unify, because we have metas.

- `ShiTT.Check.unify :: Context -> Value -> Value -> IO ()`

`unify` take two `Value` as input, and try to equalify them. If a value is an unsolved meta, it will be solved by the other value. The solution will be write done as a global variable.

## Inductive Type

For the record, ShiTT did not support positive check yet (It is not hard, but I am lazy😢).

ShiTT stores all the definitions in the following type.

```haskell
-- ShiTT.Context
data Decls = Decls 
  { definedNames :: [Name]
  , allDataDecls :: M.Map Name Data
  , allFunDecls  :: M.Map Name Fun
  } deriving Show
```

And for a data type, `Context.Data` is used,

```haskell
data Data = Data 
  { dataName :: Name 
  , dataPara :: Telescope
  , dataIx   :: Telescope
  , dataCons :: [Constructor] 
  }
-- where
data Constructor = Constructor
  { conName   :: Name 
  , belongsTo :: Name      -- Name of the data type
  , conPara   :: Telescope -- dataPara              |- conPara
  , retIx     :: TmSpine   -- (dataPara ++ conPara) |- retIx
  }
```

Those fields can be explaind below,

```haskell

data "dataName" "dataPara" : "dataIx" -> U where
| "conName1" : "conPara1" -> ... "retIx1"
| "conName2" : "conPara2" -> ... "retIx2"
blabla

-- belongsTo1 = belongsTo2 = ... = dataName
```

The syntax follows Agda. Split arguments of data types into two parts. (1) The parameters, which can not various between different constructors. (2) The indexes, which can.


