module Sandbox where

data P : {A : Set} -> A -> Set where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

data Vec2 (A : Set) : Nat -> Set where
  nil : Vec2 A zero
  cons : (n : Nat) -> A -> Vec2 A n -> Vec2 A (suc n)

vmap2 : {A B : Set}(n : Nat) -> (A -> B) -> Vec2 A n -> Vec2 B n
vmap2 zero _ nil = nil
vmap2 (suc n) f (cons .n x xs) = cons n (f x) (vmap2 n f xs)

data Image_∋_ {A B : Set}(f : A -> B) : B -> Set where
  im : {x : A} -> Image f ∋ f x

inv : {A B : Set}(f : A -> B)(y : B) -> Image f ∋ y -> A
inv f .(f x) (im {x}) = x

myFun : Nat -> Nat
myFun (suc zero) = zero
myFun _ = suc zero

solveThis : Image myFun ∋ zero
solveThis = im

testInv : P (inv myFun zero im) -> P (suc zero)
testInv x = x

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)
       
infixr 9 _::_

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

_!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
[] ! ()
(x :: _) ! fzero = x
(_ :: xs) ! (fsuc i) = xs ! i

testFin : Fin (suc (suc zero))
testFin = fsuc fzero

test! : P ((zero :: suc zero :: []) ! (fsuc fzero)) -> P (suc zero)
test! x = x