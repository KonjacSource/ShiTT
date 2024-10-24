# ShiTT

[English](./README.md) | [中文](./README-zh.md)

ShiTT is a shitty language. TT here is the name of a friend of mine, instead of the abbr of type theory.

There is an [implementation note](./Notes/Implementation_Note.md) that I am still writting.

## Usage

Build from source, or download binary from [Release](https://github.com/KonjacSource/ShiTT/releases).

```shell
> stack build 
> ./shitt Example.shitt
```

or

```shell
> stack repl 
ghci> import ShiTT.Parser 
ghci> run "Eaxmple.shitt"
```

## Features

- [x] Dependent types
- [x] Bidirectional type checking
- [x] Type in Type
- [x] ~~Evaluation by HOAS~~
- [x] Meta variables and implict arugments (pattern unification)
- [x] Pattern matching and data type
- [x] Coverage checking
- [x] Without K
- [x] [Syntax Highlight](https://github.com/KonjacSource/shitt-highlight)
- [x] REPL
- [x] Module system (very naive)
- [x] Mutual recursion
- [x] Termination checking

## TODO

- [ ] OTT
- [ ] Operators
- [ ] Universe polymorphism
- [ ] Positive checking for data types
- [ ] Better pretty printing
- [ ] Better error reporting
- [ ] IO
- [ ] Code generator
- [ ] Type classes
- [ ] Better Module system

## Use REPL

Start REPL with

```shell
> ./shitt repl 
shitt> 
```

or

```shell
> stack repl 
ghci> import ShiTT.Parser
ghci> repl
shitt> 
```

Input any ShiTT code, end with a NEW LINE ";;"

i.e.

```shell
shitt> data Bool : U where 
shitt> | true : ...  
shitt> | false : ...
shitt> ;;
All Done.
shitt> def not (_ : Bool) : Bool 
shitt> | true = false 
shitt> | false = true
shitt> ;;
All Done.
shitt> #eval not false
shitt> ;;
true
All Done.
```

## Load File

You can now import a shitt file with

```haskell
#load "FilePath.shitt"

-- here you can use anything defined in the file.
```

## Syntax

### Data Types

```agda
data Nat : U where 
| zero : ... 
| succ : (_ : Nat) -> ...
```

This equivalent to following code in Agda.

```agda
data Nat : Set where
  zero : Nat 
  succ : Nat -> Nat
```

### Indexed Types

ShiTT also allow Indexed Data Types like

```agda
data Vec (A : U) : (n : Nat) -> U where 
| nil : ... zero
| cons : {n : Nat} (x : A) (xs : Vec x n) -> ... (succ n)
```

In Agda, this is equivalent to

```agda
data Vec (A : U) : (n : Nat) -> U where 
  nil : Vec A zero
  cons : {n : Nat} (x : A) (xs : Vec x n) -> Vec A (succ n)
```

Those dots `...` in code is a place holder for the name and parameters for defining data type.
In this case, `...` is `Vec A` exactly.

We can also define the propositional equality.

```agda
data Id {A : U} : (_ _ : A) -> U where 
| refl : (x : A) -> ... x x
```

### Functions and Pattern Matching

ShiTT allows you to use pattern match to define a function

```haskell
def add (x y : Nat) : Nat where 
| zero y = y 
| (succ x) y = succ (add x y)

def three : Nat where 
| = succ (succ (succ zero))

#eval add three three
```

The `#eval` will evaluate and print the following term to stdout.

Also, `#infer` will infer the type of the following term and print it.

ShiTT allows dependent pattern match, which means some varibles in pattern will be unified by other pattern,

```haskell
data Imf {A B : U} (f : A -> B) : (_ : B) -> U where 
| imf : (x : A) -> ... (f x) 

fun invf {A B : U} (f : A -> B) (y : B) (_ : Imf f y) : A where 
| f _ (imf x) = x  

#eval invf succ (succ zero) (imf zero)
```

Here `y` is restricted by `imf x`.

### Mutual Recursion

Only mutual functions for now. The syntax is pretty Pascal style.

```haskell
mutual
  fun even (_ : N) : Bool
  fun odd  (_ : N) : Bool
begin

  fun even
  | zero = true
  | (succ n) = odd n
  
  fun odd 
  | zero = false
  | (succ n) = even n
  
end
```

### ~~HIT~~

```haskell
higher inductive Int : U where 
| pos : (n : N) -> ... 
| neg : (n : N) -> ... 
    when 
    | zero = pos zero

#infer Int -- : U 
#eval neg zero -- = pos zero
```

### Axiom

Define an axiom like this,

```haskell
axiom def lem {A : U} : Either A (A -> Void)
```

### ~~Unmatchable~~

```haskell
unmatchable data Interval : U where 
| i0 : ... 
| i1 : ...

-- This is ok
def reflTrue (i : Interval) : Bool 
| i = true

-- This is an error, when you try to match on Interval
def trueToFalse (i : Interval) : Bool
| i0 = true 
| i1 = false

-- This is ok, since "when clause" won't do those check.
higher inductive S1 : U where 
| base : ... 
| loop : (i : Interval) -> ... 
    when 
    | i0 = base 
    | i1 = base
```

## Other Syntax

### Let Binding

```haskell
#eval let x : Nat = succ zero ; add x x
```

### Lambda Expression

```haskell
#eval \ x . add (succ zero) x
```

### Apply Implicit Argument by Name

```haskell
#eval Id {A = Nat}
```

### Insert Meta Argument Explicitly

```haskell
#eval let x : Id zero zero = refl _ ; U
-- or
#eval let x : Id zero zero = refl auto ; U
```

### Print Context

```haskell
fun addComm (x y : N) : Id (add x y) (add y x) where 
| zero y = sym (addIdR _)
| (succ x) y = traceContext[  trans (cong succ (addComm x y)) (addSucc y x)  ]
```

This will show

```haskell
x : N
y : N
--------------------
Id {N} (succ (add x y)) (add y (succ x))
```

Here is a useful usage:

```haskell
axiom fun sorry {A : U} : A

fun addComm (x y : N) : Id (add x y) (add y x) where 
| zero y = sym (addIdR _)
| (succ x) y = traceContext[sorry]
```

`traceContext` will print the context definitions and the goal type (if it is not a metavariable) while type checking. Also note that `traceContext[x] = x`

### Termination Check

ShiTT does check termination. You can use `partial` to shut it down.

```haskell
data Bool : U where 
| true : ... 
| false : ...

data N : U where  
| zero : ...  
| succ : (pre : N) -> ...  

mutual
  
  fun even (_ : N) : Bool
  fun odd  (_ : N) : Bool

begin

  fun even
  | zero = true
  | (succ n) = odd n
  
  fun odd 
  | zero = false
  | (succ n) = even n
  
end

fun add (_ _ : N) : N 
| zero n = n 
| (succ m) n = succ (add m n) 

-- Bad
fun add1 (_ _ : N) : N 
| m n = add1 m n

-- Good again
partial fun add1 (_ _ : N) : N 
| m n = add1 m n

-- This is also good!
fun add2 (_ _ : N) : N 
| x zero = x 
| x (succ y) = succ (add2 y x)

data Vec (A : U) : (_ : N) -> U where 
| nil : ... zero 
| cons : {n : N} (_ : A) (_ : Vec A n) -> ... (succ n)



fun append {A : U} {m n : N} (v : Vec A m) (w : Vec A n) : Vec A (add m n)
| nil w = w 
| (cons x xs) w = cons x (append xs w)

-- Bad
fun append1 {A : U} {m n : N} (v : Vec A m) (w : Vec A n) : Vec A (add m n)
| nil w = w 
| (cons x xs) w = (append (cons x xs) w)
```

## Example

The following example shows the basic syntax and how to do some simple theorem proof.

```haskell
data Id {A : U} : (_ _ : A) -> U where 
| refl : (x : A) -> ... x x

def uip {A : U} {x y : A} (p q : Id x y) : Id p q where 
| (refl _) (refl x) = refl (refl _)

data N : U where  
| zero : ...  
| succ : (pre : N) -> ...  

def add (m n : N) : N where  
| zero n = n
| (succ m) n = succ (add m n)

data Vec (A : U) : (_ : N) -> U where 
| nil : ... zero 
| cons : {n : N} (x : A) (xs : Vec A n) -> ... (succ n)

#infer Vec

def append {A : U} {m n : N} (v : Vec A m) (w : Vec A n) : Vec A (add m n) 
| nil w = w
| (cons x xs) w = cons x (append xs w)

#eval append (cons zero (cons (succ zero) nil)) nil

-- Some theorems.

def sym {A : U} {x y : A} (p : Id x y) : Id y x where 
| (refl _) = refl _

def trans {A : U} {x y z : A} (_ : Id x y) (_ : Id y z) : Id x z where 
| (refl _) (refl _) = refl _ 

def cong {A B : U} {x y : A} (f : A -> B) (p : Id x y) : Id (f x) (f y) where 
| f (refl x) = refl _

def addAssoc (x y z : N) : Id (add (add x y) z) (add x (add y z)) where 
| zero y z = refl _
| (succ x) y z = cong succ (addAssoc x y z) 

def addIdR (x : N) : Id (add x zero) x where 
| zero = refl _ 
| (succ x) = cong succ (addIdR x)

def addSucc (x y : N) : Id (add (succ x) y) (add x (succ y)) where 
| zero y = refl _ 
| (succ x) y = cong succ (addSucc x y)

def addComm (x y : N) : Id (add x y) (add y x) where 
| zero y = sym (addIdR _)
| (succ x) y = trans (cong succ (addComm x y)) (addSucc y x)


```

## Reference

Pattern matching and inductive type:

- Ulf Norell. [Towards a practical programming language based on dependent type theory](https://www.cse.chalmers.se/~ulfn/papers/thesis.pdf).

Solving meta variables:

- András Kovács. [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo).

Termination checking:

- Karl Mehltretter. [Termination Checking for a Dependently Typed Language](https://www.cse.chalmers.se/~abela/mehltret-da.pdf).
