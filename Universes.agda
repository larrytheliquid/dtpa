module Universes where
open import Data.Nat

record True : Set where 
data False : Set where 

data Bool : Set where
  true : Bool
  false : Bool

isTrue : Bool → Set
isTrue true = True
isTrue false = False

infix 30 not_ 
not_ : Bool → Bool 
not true = false 
not false = true 

infixr 25 _and_ 
_and_ : Bool → Bool → Bool 
true and x = x 
false and _ = false 

notNotId : (a : Bool) → isTrue (not not a) → isTrue a
notNotId true p = p
notNotId false ()

andIntro : (a b : Bool) → isTrue a → isTrue b → isTrue (a and b)
andIntro true _ _ p = p
andIntro false _ () _

nonZero : ℕ → Bool
nonZero zero = false
nonZero _ = true

postulate _div_ : ℕ → (m : ℕ){p : isTrue (nonZero m)} → ℕ

three = 16 div 5