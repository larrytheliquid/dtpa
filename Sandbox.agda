module Sandbox where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

data Vec (A : Set) : Nat -> Set where
  nil : Vec A zero
  cons : (n : Nat) -> A -> Vec A n -> Vec A (suc n)

vmap : {A B : Set}(n : Nat) -> (A -> B) -> Vec A n -> Vec B n
vmap zero _ nil = nil
vmap (suc n) f (cons .n x xs) = cons n (f x) (vmap n f xs)

data Image_∋_ {A B : Set}(f : A -> B) : B -> Set where
  im : (x : A) -> Image f ∋ f x

inv : {A B : Set}(f : A -> B)(y : B) -> Image f ∋ y -> A
inv f .(f x) (im x) = x