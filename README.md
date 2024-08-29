# ShiTT

ShiTT is a shitty language.

```haskell
data Id {A : U} : (_ _ : A) -> U where 
| refl : (x : A) -> ... x x

fun uip {A : U} {x y : A} (p q : Id x y) : Id p q where 
| (refl _) (refl x) = refl (refl x)


data N : U where  
| zero : ...  
| succ : (pre : N) -> ...  

fun add (m n : N) : N where  
| zero n = n
| (succ m) n = succ (add m n)

data Vec (A : U) : (_ : N) -> U where 
| nil : ... zero 
| cons : {n : N} (x : A) (xs : Vec A n) -> ... (succ n)

fun append {A : U} {m n : N} (v : Vec A m) (w : Vec A n) : Vec A (add m n) where 
| nil w = w 
| (cons x xs) w = cons x (append xs w)

#eval append (cons zero (cons (succ zero) nil)) nil
#infer Vec
```

## Usage

```
> stack build 
> shitt Example.shitt
```

or

```
> stack repl 
ghci> import ShiTT.Parser 
ghci> run "Eaxmple.shitt"
```

## Feature

- [x] Dependent types
- [x] Evaluation by HOAS.
- [x] Meta variables and implict arugments
- [x] Pattern match

## TODO

- [ ] Coverage check
- [ ] Termination check
- [ ] Positive check for data types
- [ ] Better pretty printer
- [ ] Module system
- [ ] IO
- [ ] Code generator
- [ ] Type classes
