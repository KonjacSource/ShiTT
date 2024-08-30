# ShiTT

ShiTT is a shitty language.

## Usage

```
> stack build 
> ./shitt Example.shitt
```

or

```
> stack repl 
ghci> import ShiTT.Parser 
ghci> run "Eaxmple.shitt"
```

## Features

- [x] Dependent types
- [x] Evaluation by HOAS.
- [x] Meta variables and implict arugments
- [x] Pattern match

## TODO

- [ ] Coverage check
- [ ] Operators
- [ ] Termination check
- [ ] Positive check for data types
- [ ] Better pretty printer
- [ ] Module system
- [ ] IO
- [ ] Code generator
- [ ] Type classes

## Example

```haskell
data Id {A : U} : (_ _ : A) -> U where 
| refl : (x : A) -> ... x x

fun uip {A : U} {x y : A} (p q : Id x y) : Id p q where 
| (refl _) (refl x) = refl (refl _)

data N : U where  
| zero : ...  
| succ : (pre : N) -> ...  

fun add (m n : N) : N where  
| zero n = n
| (succ m) n = succ (add m n)

data Vec (A : U) : (_ : N) -> U where 
| nil : ... zero 
| cons : {n : N} (x : A) (xs : Vec A n) -> ... (succ n)

#infer Vec

fun append {A : U} {m n : N} (v : Vec A m) (w : Vec A n) : Vec A (add m n) 
| nil w = w 
| (cons x xs) w = cons x (append xs w)

#eval append (cons zero (cons (succ zero) nil)) nil

-- Some theorems.

fun sym {A : U} {x y : A} (p : Id x y) : Id y x where 
| (refl _) = refl _

fun trans {A : U} {x y z : A} (_ : Id x y) (_ : Id y z) : Id x z where 
| (refl _) (refl _) = refl _ 

fun cong {A B : U} {x y : A} (f : A -> B) (p : Id x y) : Id (f x) (f y) where 
| f (refl x) = refl _

fun addAssoc (x y z : N) : Id (add (add x y) z) (add x (add y z)) where 
| zero y z = refl _
| (succ x) y z = cong succ (addAssoc x y z) 

fun addIdR (x : N) : Id (add x zero) x where 
| zero = refl _ 
| (succ x) = cong succ (addIdR x)

fun addSucc (x y : N) : Id (add (succ x) y) (add x (succ y)) where 
| zero y = refl _ 
| (succ x) y = cong succ (addSucc x y)

fun addComm (x y : N) : Id (add x y) (add y x) where 
| zero y = sym (addIdR _)
| (succ x) y = trans (cong succ (addComm x y)) (addSucc y x)
```
