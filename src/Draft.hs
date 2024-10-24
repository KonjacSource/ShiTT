{-# HLINT ignore #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
-- {-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Draft where 
-- import ShiTT.Syntax
-- import ShiTT.Eval
-- import ShiTT.Context

-- import qualified ShiTT.Decl as R 
-- -- import qualified ShiTT.Inductive as I
-- -- import ShiTT.Decl (Pattern(PVar, PCon))
-- import ShiTT.Meta
-- import Control.Monad (forM_)
-- -- import ShiTT.Inductive (splitCase)
-- import ShiTT.TermParser as TP
-- import ShiTT.TermParser (readTerm)
-- import ShiTT.Check (infer)

-- natData :: Data
-- natData = Data 
--   { dataName = "N"
--   , dataPara = []
--   , dataIx   = [] 
--   , dataCons = [zeroCon, succCon]
--   }

-- zeroCon :: Constructor
-- zeroCon = Constructor
--   { conName   = "zero"
--   , belongsTo = "N"
--   , conPara   = []
--   , retIx     = []
--   }

-- zero :: Value 
-- zero = VCon "zero" []

-- suc :: Value -> Value 
-- suc pre = VCon "succ" [(pre, Expl)]

-- succCon :: Constructor
-- succCon = Constructor
--   { conName   = "succ"
--   , belongsTo = "N"
--   , conPara   = [("pre", Expl, Func "N")]
--   , retIx     = []
--   }

-- addFun :: Fun 
-- addFun = Fun 
--   { funName = "add"
--   , funPara = [("m", Expl, Func "N"), ("n", Expl, Func "N")]
--   , funRetType = Func "N"
--   , funClauses = Just 
--       [ Clause 
--         { patterns = [PCon "zero" [] Expl, PVar "n" Expl]
--         , clauseRhs = Var "n" 
--         }
--       , Clause 
--         { patterns = [PCon "succ" [PVar "m" Expl] Expl, PVar "n" Expl]
--         , clauseRhs = Func "succ" `eApp` (Func "add" `eApp` Var "m" `eApp` Var "n")
--         }
--       ]
--   }

-- testDecls 
--   = insertFun addFun 
--   $ insertData natData
--   $ emptyDecls

-- testContext = emptyCtx
--   { decls = testDecls
--   }

-- mkNum :: Int -> Term 
-- mkNum 0 = Func "zero"
-- mkNum n = Func "succ" `eApp` mkNum (n-1)

-- callAdd :: Term -> Term -> Term 
-- callAdd m n = Func "add" `eApp` m `eApp` n

-- evalTest :: IO ()
-- evalTest = do 
--   let tests = 
--         [ Let "x" (Func "N") (mkNum 3) $
--             callAdd (Var "x") (Var "x")
--         , Lam "x" Expl $ Lam "y" Expl $ 
--             callAdd (Func "succ" `eApp` Var "x") (Var "y")
--         , Func "add" 
--         , Func "add" `eApp` mkNum 3
--         , Func "add" `eApp` Func "add"
--         , (Lam "x" Expl $ Lam "y" Expl $ 
--             callAdd (Func "succ" `eApp` Var "x") (Var "y")) `eApp` mkNum 2
--         , Pi "m" Expl (Func "N") (Pi "n" Expl (Func "N") (Func "N"))
--         ]
--   forM_ tests $ \test -> do 
--     print $ eval testContext test

-- testRead :: String -> Raw 
-- testRead = readTerm testContext

-- checkTest :: IO ()
-- checkTest = do 
--   let tests = map testRead
--         [ "add"
--         , "N"
--         , "let x = succ zero ; add x x"
--         , "add zero"
--         , "\\ x . add x x"
--         ]
--   forM_ tests $ \test -> do 
--     (v,t) <- infer testContext test
--     print (eval testContext v, refresh testContext t)
--------------------------------------------------------------------------------------------
{-

addFun :: Fun 
addFun = Fun 
  { funName = "add"
  , funPara = [("m", Expl, natType), ("n", Expl, natType)]
  , funRetType = \ _ -> natType
  , funVal = \ctx -> \case 
      [(VCon "zero" [], Expl), (n, Expl)] -> Just n 
      [(VCon "succ" [(m, Expl)], Expl), (n, Expl)] ->
        Just $ eval (ctx <: "m" := m <: "n" := n) $ 
          Func "succ" `eApp` 
            (Func "add" `eApp` Var "m" 
                        `eApp` Var "n") 
      _ -> Nothing 
  }

vecData :: Data 
vecData = Data 
  { dataName = "Vec"
  , dataPara = [("A", Expl, VU)]
  , dataIx = [("n*", Expl, natType)]
  , dataCons = [nilCon, consCon]
  }

vecType :: Value -> Value -> VType
vecType a n = VFunc "Vec" [(a, Expl), (n, Expl)]

nilCon :: Constructor
nilCon = Constructor
  { conName = "nil"
  , belongsTo = "Vec"
  , conPara = []
  , retIx = \case [(a, Impl)] -> [(zero, Expl)]; p -> error (show p)
  }

consCon :: Constructor 
consCon = Constructor 
  { conName = "cons"
  , belongsTo = "Vec"
  , conPara = [("n*", Impl, natType), ("x", Expl, VVar "A"), ("xs", Expl, VCon "Vec" [(VVar "A", Expl), (VVar "n*", Expl)])]
  , retIx = \sp -> [(VCon "succ" [(fst (sp !! 1), Expl)], Expl)]
  }

imAdd :: Data 
imAdd = Data 
  { dataName = "Im+3"
  , dataPara = []
  , dataIx   = [("n", Expl, natType)]
  , dataCons = [imCon]
  }

mkNumV 0 = VFunc "zero" []
mkNumV n = VFunc "succ" [(mkNumV (n-1), Expl)]

imCon :: Constructor
imCon = Constructor
  { conName = "im+3"
  , belongsTo = "Im+3"
  , conPara = [("x", Expl, natType)]
  , retIx = \[x] -> [(VFunc "add" [x, (mkNumV 3, Expl)], Expl)]
  }

{-
data Id {A : U} : (x y : A) -> U where 
  refl : (x : A) -> ... x x
-}

idData :: Data 
idData = Data 
  { dataName = "Id"
  , dataPara = [("A", Impl, VU)]
  , dataIx = [("x", Expl, VVar "A"), ("y", Expl, VVar "A")] 
  , dataCons = [reflCon]
  }

reflCon :: Constructor
reflCon = Constructor 
  { conName = "refl"
  , belongsTo = "Id"
  , conPara = [("x", Expl, VVar "A")]
  , retIx = \ [a, (x, Expl)] -> [(x, Expl), (x, Expl)] 
  }

testDecls 
  = insertFun addFun 
  $ insertHData intData
  $ insertData natData 
  $ insertData boolData
  $ insertData vecData 
  $ insertData idData 
  $ insertData imAdd
  $ emptyDecls

testContext = emptyCtx
  { decls = testDecls
  }

testNormal :: Term -> Term 
testNormal t = normalize testContext t

-- infixl 9 #
-- infixl 9 #@
-- v = Var 
-- (#) f x = App f x Expl
-- (#@) f x = App f x Impl
-- elam x b = Lam x Expl b 
-- ilam x b = Lam x Impl b 

-- test1 :: Term 
-- test1 = elam "x" $ elam "y" $ 
--   Func "add" # (Func "succ" # (Func "succ" # v "x")) 
--              # v "y"

-- test2 :: Term 
-- test2 = test1 # Func "zero" 
--               # (Func "succ" # (Func "add" # (Func "succ" # Func "zero")
--                                            # Func "zero"))

-- -- allMeta test3 ==> [3]
-- test3 :: Term 
-- test3 = test1 # Func "zero" 
--               # (Func "succ" # (Meta 3 # (Func "succ" # Func "zero")
--                                            # Func "zero"))

{-

Lam "x" Expl $ Lam "y" Expl $
  
    (Func "add") 
      (Var "y")  
      ((Func "succ") (Var "x"))
-}

-- Elab test 
--------------

infixl 9 #
infixl 9 #@
v = RRef 
pv = RPVar
(#) f x = RApp f x (Unnamed Expl)
(#@) f x = RApp f x (Unnamed Impl)
elam x b = RLam x (Unnamed Expl) b 
ilam x b = RLam x (Unnamed Impl) b 
f #! (x, u) = RApp f u (Named x)
nlam (x, y) b = RLam y (Named x) b 


etest1 :: Raw 
etest1 = 
  RLet "id" (RPi "A" Impl RU $ RPi "x" Expl (v "A") (v "A")) 
    (elam "x" (v "x"))
    (v "id" # RU)

etest2 :: Raw 
etest2 = 
  RLet "_" (RRef "Vec" # RU # RRef "zero")
    (RRef "nil")
    RU

mkNum :: Int -> Raw 
mkNum 0 = RRef "zero"
mkNum n = RRef "succ" # mkNum (n-1)

etest3 :: Raw 
etest3 = 
  RLet "refl3" (v "Id" #@ (v "N") # (v "add" # mkNum 1 # mkNum 2) 
                       # mkNum 3)
       (v "refl" # Hole)
  (v "refl3")

etest4 :: Raw 
etest4 = 
  RLet "t" RU
       (RPi "A" Impl RU $ RPi "x" Impl (v"A") $ v "Id" # v"x" # v"x")
  (v "t")

-- pattern match check test 
-------------------------------
-- checkP :: Context -> [Name] -> [R.Pattern] -> Telescope -> Either CheckError ([Name], Spine, CheckResult)

checkPattern :: [R.Pattern] -> Telescope -> Either I.CheckError ([Name], Spine, I.CheckResult)
checkPattern = I.checkP testContext [] 

pmt1 = checkPattern [PVar "x" Impl] [("x^", Impl, natType)]

pmt2 = checkPattern [(PVar "x" Expl), (PCon "succ" [PVar "y" Expl] Expl)] 
                    [("x^", Expl, VU), ("y^", Expl, natType)]

{-
{A: U} {x : A} (p q : Id {A} x x)
{A}    {x}     (refl y) (refl z)
-}
pmt3 = checkPattern 
  [PVar "-A" Impl,   PVar "-x" Impl,            PCon "refl" [PVar "-y" Expl] Expl, PCon "refl" [PVar "-z" Expl] Expl]
  [("A^", Impl, VU), ("x^", Impl, VVar "A^"), ("p^", Expl, id_type),            ("q^", Expl, id_type)] where 
  id_type = VCon "Id" [(VVar "A^", Impl), (VVar "x^", Expl), (VVar "x^", Expl)]

{-
{A : U} {n : N}  (v : Vec A n)
{A}     {succ n} (cons {m} x xs)
{A}     {n}      (cons {m} x xs)
{A}     {n}      nil
-}
pmt4 = checkPattern
  [PVar "-A" Impl, PCon "succ" [PVar "-n" Expl] Impl, PCon "cons" [PVar "-m" Impl, PVar "-x" Expl, PVar "-xs" Expl] Expl]
  [("A", Impl, VU), ("n", Impl, natType), ("v", Expl, VCon "Vec" [(VVar "A", Expl), (VVar "n", Expl)])]

pmt5 = checkPattern
  [PVar "-A" Impl, PVar "-n" Impl, PCon "cons" [PVar "-m" Impl, PVar "-x" Expl, PVar "-xs" Expl] Expl]
  [("A", Impl, VU), ("n", Impl, natType), ("v", Expl, VCon "Vec" [(VVar "A", Expl), (VVar "n", Expl)])]

pmt6 = checkPattern
  [PVar "-A" Impl, PVar "-n" Impl, PCon "nil" [] Expl]
  [("A", Impl, VU), ("n", Impl, natType), ("v", Expl, VCon "Vec" [(VVar "A", Expl), (VVar "n", Expl)])]


{-
minus3 

(y : N) (i : Im+3 y)
y       (im+3 x) 
-- hope y = x + 3     
-}
pmt7 = checkPattern
  [PVar "-y" Expl, PCon "im+3" [PVar "-x" Expl] Expl]
  [("y", Expl, natType), ("i", Expl, VCon "Im+3" [(VVar "y", Expl)])]


{-
{A : U} {n : N} (p : Id {N} n zero) (v : Vec A n)
{A}     {n}     (refl zero)         (cons {m} x xs)
-}
--  succ -m  /=  zero
pmt8 = checkPattern
  [PVar "-A" Impl, PVar "-n" Impl, PCon "refl" [PCon "zero" [] Expl] Expl, PCon "cons" [PVar "-m" Impl, PVar "-x" Expl, PVar "-xs" Expl] Expl]
  [("A", Impl, VU), ("n", Impl, natType), ("p", Expl, VCon "Id" [(natType, Impl), (VVar "n", Expl), (VCon "zero" [], Expl)]), ("v", Expl, VCon "Vec" [(VVar "A", Expl), (VVar "n", Expl)])]

-- checkFun testContext add'Fun
add'Fun :: R.Fun
add'Fun = R.Fun 
  { R.funName = "add'"
  , R.funPara = [("m", Expl, natType), ("n", Expl, natType)]
  , R.funRetType = \ _ -> natType
  , R.clauses = 
      [ R.Clause
        [PCon "zero" [] Expl, PVar "-n" Expl]
        (R.Rhs $ v "-n")
      , R.Clause 
        [PCon "succ" [PVar "-m" Expl] Expl, PVar "-n" Expl]
        (R.Rhs $ v "succ" # (v "add'" # v"-m" # v"-n"))
      ]
  }

{-
append : {A : Set} {m n : ℕ} (v : Vec A m) (w : Vec A n) → Vec A (m + n) 
append {A} {m} {n} nil w = w 
append {A} {m} {n} (cons {l} x xs) w = cons x (append xs w)
-} 
appendFun :: R.Fun 
appendFun = R.Fun
  { R.funName = "append"
  , R.funPara = [ ("A", Impl, VU), ("m", Impl, natType), ("n", Impl, natType)
                , ("v", Expl, VCon "Vec" [(VVar "A", Expl), (VVar "m", Expl)])
                , ("w", Expl, VCon "Vec" [(VVar "A", Expl), (VVar "n", Expl)]) ]
  , R.funRetType = \[(a,_), (m,_), (n,_), _, _] -> VCon "Vec" [(a, Expl), (VFunc "add'" [(m, Expl), (n, Expl)], Expl)]
  , R.clauses = 
    [ R.Clause 
      [ PVar "-A" Impl, PVar "-m" Impl, PVar "-n" Impl
      , PCon "nil" [] Expl, PVar "-w" Expl]
      (R.Rhs $ pv"-w")
    , R.Clause
      [ PVar "-A" Impl, PVar "-m" Impl, PVar "-n" Impl
      , PCon "cons" [PVar "-l" Impl, PVar "-x" Expl, PVar "-xs" Expl] Expl
      , PVar "-w" Expl]
      (R.Rhs $ v"cons" # pv"-x" # (v"append" # pv"-xs" # pv"-w"))
    ]
  }

testContext2 :: Context 
testContext2 = runIO $ do 
  add <- I.checkFun testContext add'Fun
  let ctx' = testContext { decls = insertFun add testContext.decls }
  append <- I.checkFun ctx' appendFun
  pure $ ctx' { decls = insertFun append ctx'.decls }

add'Test1 :: Raw 
add'Test1 = v "add'" # mkNum 3 # mkNum 4

add'Test2 :: Raw 
add'Test2 = RLet "f" (RPi "x" Expl (v"N") (v"N")) (elam "x" $ v "add'" # mkNum 3 # v "x")
  (v"f")

mkVec :: [Raw] -> Raw 
mkVec [] = v"nil"
mkVec (x:xs) = v "cons" # x # mkVec xs

consTest1 :: Raw 
consTest1 = v"cons" #@ v"N" # mkNum 2 # (v"nil" #@ v"N")

appendTest1 :: Raw 
appendTest1 = v "append" # mkVec [] # mkVec (map mkNum [4,5,6])

appendTest2 :: Raw 
appendTest2 = v "append" # mkVec (map mkNum [0]) # mkVec (map mkNum [4])

-- addFun = Fun 
--   { funName = "add"
--   , funPara = [("m", Expl, natType), ("n", Expl, natType)]
--   , funRetType = \ _ -> natType
--   , funVal = \ctx -> \case 
--       [(VCon "zero" [], Expl), (n, Expl)] -> Just n 
--       [(VCon "succ" [(m, Expl)], Expl), (n, Expl)] ->
--         Just $ eval (ctx <: "m" := m <: "n" := n) $ 
--           Func "succ" `eApp` 
--             (Func "add" `eApp` Var "m" 
--                         `eApp` Var "n") 
--       _ -> Nothing 
--   }

-- cons
splitTest1 = splitCase (testContext <: ("m", natType) :=! VVar "m") ("v", Expl, VCon "Vec" [(natType, Expl), (VCon "succ" [(VVar "m", Expl)], Expl)])
-- []
splitTest2 = splitCase (testContext <: ("m", natType) :=! VVar "m") ("v", Expl, VCon "Vec" [(natType, Expl), (VVar "m", Expl)])
-- nil
splitTest3 = splitCase (testContext <: ("m", natType) :=! VVar "m") ("v", Expl, VCon "Vec" [(natType, Expl), (zero, Expl)])

splitTest4 = splitCase (testContext <: ("m", natType) :=! VPatVar "m" []) ("v", Expl, VCon "Vec" [(natType, Expl), (VVar "m", Expl)])

-- test coverage 

--  Context -> (Name, Icit, VType) -> Pattern -> (Value, Icit) -> MatchResult

matchTest1 = I.splitMatch1 testContext2 [] ("_", Expl, natType) (PCon "zero" [] Expl) (VVar "x" ,Expl)

-- matchTest1 = trace (show ps) $ I.match' (testContext2 <: res.typeLevelDef) rhs_ctx ts ps vs
--   where 
--     Right (_,_,res) = I.checkP testContext2 [] ps appendFun.funPara
--     rhs_ctx = testContext2 <: res.resultCtx <: res.freevarsRhs -- <: res.extraDef
--     ts = appendFun.funPara
--     ps = (appendFun.clauses!!0).patterns
--     vs = [(VVar "A%", Impl), (VVar "m%", Impl), (VVar "n%", Impl)
--          ,(VVar "v%", Expl), (VVar "w%", Impl)]
    
    -- appendFun :: R.Fun 
    -- appendFun = R.Fun
    --   { R.funName = "append"
    --   , R.funPara = [ ("A", Impl, VU), ("m", Impl, natType), ("n", Impl, natType)
    --                 , ("v", Expl, VCon "Vec" [(VVar "A", Expl), (VVar "m", Expl)])
    --                 , ("w", Expl, VCon "Vec" [(VVar "A", Expl), (VVar "n", Expl)]) ]
    --   , R.funRetType = \[(a,_), (m,_), (n,_), _, _] -> VCon "Vec" [(a, Expl), (VFunc "add'" [(m, Expl), (n, Expl)], Expl)]
    --   , R.clauses = 
    --     [ R.Clause 
    --       [ PVar "-A" Impl, PVar "-m" Impl, PVar "-n" Impl
    --       , PCon "nil" [] Expl, PVar "-w" Expl]
    --       (R.Rhs $ pv"-w")
    --     , R.Clause
    --       [ PVar "-A" Impl, PVar "-m" Impl, PVar "-n" Impl
    --       , PCon "cons" [PVar "-l" Impl, PVar "-x" Expl, PVar "-xs" Expl] Expl
    --       , PVar "-w" Expl]
    --       (R.Rhs $ v"cons" # pv"-x" # (v"append" # pv"-xs" # pv"-w"))
    --     ]
    --   }

-- HIT
---------------------------------------- 

{-
data Int : U where 
| pos : (n : N) -> ... 
| neg : (n : N) -> ... 
    when n 
    | zero = pos zero
-}
intData :: HData 
intData = HData 
  { basePart = Data 
    { dataName = "Int"
    , dataCons = 
      [ Constructor 
        { conName = "pos"
        , belongsTo = "Int"
        , conPara = [("n", Expl, natType)]
        , retIx = \ _ -> []
        }
      , Constructor 
        { conName = "neg"
        , belongsTo = "Int"
        , conPara = [("n", Expl, natType)]
        , retIx = \ _ -> []
        } 
      ]
    , dataPara = [] 
    , dataIx  = []
    }
  , higherCons = 
    [ HConstructor 
      { hconName = "neg"
      , hconPatterns = [ [PCon "zero" [] Expl] ]
      , hconClauses = \ctx -> \case 
          [(VCon "zero" [], Expl)] -> Just (VCon "pos" [(VCon "zero" [], Expl)])
          sp -> Just $ VCon "neg" sp
      }
    ]
  }

boolData :: Data 
boolData = Data 
  { dataName = "Bool"
  , dataPara = [] 
  , dataIx = []
  , dataCons = 
    [ Constructor
      { conName = "true"
      , belongsTo = "Bool"
      , conPara = []
      , retIx = \_ -> []
      }
    , Constructor
      { conName = "false"
      , belongsTo = "Bool"
      , conPara = []
      , retIx = \_ -> []
      }
    ]
  }

{-
higher inductive BoolX (A : U) : (_ : Bool) -> U where 
| btrue : (b : Bool) -> ... b
| bfalse : (b : Bool) -> ... b 
| bcon : (a b : Bool) -> ... b when 
  | a true = btrue a          
  | a false = bfalse a        
-}
-- boolXData :: HData
-- boolXData = HData
--   { basePart = Data 
--     { dataName = "BoolX"
--     , dataPara = [("A", Expl, VU)]
--     , dataIx = [("_", Expl, VCon "Bool" [])]
--     , dataCons = 
--       [ Constructor
--         { conName = "btrue"
--         , belongsTo = "BoolX"
--         , conPara = [("b", Expl, VCon "Bool" [])]
--         , retIx = \[_,b] -> [b]
--         }
--       , Constructor
--         { conName = "bfalse"
--         , belongsTo = "BoolX"
--         , conPara = [("b", Expl, VCon "Bool" [])]
--         , retIx = \[_,b] -> [b]
--         }
--       , Constructor 
--         { conName = "bcon"
--         , belongsTo = "BoolX"
--         , conPara = [("a", Expl, VCon "Bool" []), ("b", Expl, VCon "Bool" [])]
--         , retIx = \[_,_,b] -> [b]
--         }
--       ]
--     }
--   , higherCons = 
--     [ HConstructor 
--       { hconName = "bcon"
--       , hconPatterns = [ [PCon "true" [] Expl]
--                        , [PCon "false" [] Expl]]
--       , hconClauses = \ctx -> \case 
--           [_, a, (VCon "true" [], Expl)] -> Just $ VCon "btrue" [(VVar "A", Impl)  , a] 
--           [_, a, (VCon "false" [], Expl)] -> Just $ VCon "bfalse" [(VVar "A", Impl), a]
--           sp -> error (show sp) $ Just $ VCon "bcon" sp 
--       }
--     ]
--   }


-- Coverage check will forbid to do pattern match on this, but checkP won't
intervalData :: Data 
intervalData = Data 
  { dataName = "Interval" 
  , dataPara = [] 
  , dataIx   = []
  , dataCons = 
    [ Constructor
      { conName = "i0"
      , belongsTo = "Interval"
      , conPara = []
      , retIx = \ _ -> [] 
      }
    , Constructor 
      { conName = "i1"
      , belongsTo = "Interval"
      , conPara = [] 
      , retIx = \ _ -> [] 
      }
    ]
  }


  -}