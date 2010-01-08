module Views where
open import Relation.Binary.Core
open import Data.Nat
open import Data.Function
open import Data.List
open import Data.Bool

data Parity : ℕ → Set where 
  even : (k : ℕ) → Parity (k * 2) 
  odd : (k : ℕ) → Parity (1 + k * 2) 

parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(1 + k * 2)) | odd k = even (suc k)

test-parity : parity 43 ≡ odd 21
test-parity = refl

half : ℕ → ℕ
half n with parity n
half .(k * 2) | even k = k
half .(1 + k * 2) | odd k = k

infixr 30 _:all:_
data All {A : Set}(P : A → Set) : List A → Set where
  all[] : All P []
  _:all:_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

satisfies : {A : Set} → (A → Bool) → A → Set
satisfies p x = T (p x)

data Find {A : Set}(p : A → Bool) : List A → Set where
  found : (xs : List A)(y : A) → satisfies p y → (ys : List A) → Find p (xs ++ y ∷ ys)
  not-found : ∀ {xs} → All (satisfies (not ∘ p)) xs → Find p xs

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : {A : Set}(x : A) → Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} → x ≡ true -> T x
trueIsTrue refl = _

falseIsFalse : {x : Bool} -> x ≡ false -> T (not x)
falseIsFalse refl = _

find₁ : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
find₁ p [] = not-found all[]
find₁ p (x ∷ xs) with inspect (p x)
... | it true p′ = found [] x (trueIsTrue p′) xs
... | it false p′ with find₁ p xs
find₁ p (x ∷ ._) | it false _ | found xs y py ys =
  found (x ∷ xs) y py ys
find₁ p (x ∷ xs) | it false p′ | not-found npxs =
  not-found (falseIsFalse p′ :all: npxs)
