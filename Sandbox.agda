module Sandbox where

data P : {A : Set} -> A -> Set where

data Bool : Set where
  true : Bool
  false : Bool

infixr 40 _::_
data List (A : Set) : Set where 
  [] : List A 
  _::_ : A -> List A -> List A  

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

head : {A : Set}{n : Nat} -> Vec A (suc n) -> A
head (x :: _) = x

tail : {A : Set}{n : Nat} -> Vec A (suc n) -> Vec A n
tail (_ :: xs) = xs

data False : Set where 
record True : Set where

isTrue : Bool -> Set 
isTrue true = True 
isTrue false = False

_<_ : Nat -> Nat -> Bool 
_ < zero = false 
zero < suc _ = true 
suc m < suc n = m < n 

length : {A : Set} -> List A -> Nat 
length [] = zero 
length (_ :: xs) = suc (length xs) 

lookup : {A : Set}(xs : List A)(n : Nat)
         {_ : isTrue (n < length xs)} -> A 
lookup [] _ {()}
lookup (x :: _) zero = x 
lookup (_ :: xs) (suc n) {p} = lookup xs n {p}

testLookup : P (lookup (zero :: suc zero :: []) (suc zero))
             -> P (suc zero)
testLookup x = x

-- meaning of ≤ inductively defined at base case 0
data _≤_ : Nat -> Nat -> Set where
  leq-zero : {n : Nat} -> zero ≤ n
  leq-suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

leq-trans : {l m n : Nat} -> l ≤ m -> m ≤ n -> l ≤ n
leq-trans leq-zero _ = leq-zero
leq-trans (leq-suc p) (leq-suc q) = leq-suc (leq-trans p q)

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data _≠_ : Nat -> Nat -> Set where
  z≠s : {n : Nat} -> zero ≠ suc n
  s≠z : {n : Nat} -> suc n ≠ zero
  s≠s : {m n : Nat} -> m ≠ n -> suc m ≠ suc n

-- This contains the universe codes + conversion function
data Equal? (n m : Nat) : Set where
  eq : n == m -> Equal? n m
  neq : n ≠ m -> Equal? n m

equal? : (n m : Nat) -> Equal? n m
equal? zero zero = eq refl
equal? zero (suc _) = neq z≠s
equal? (suc _) zero = neq s≠z
equal? (suc n) (suc m) with equal? n m
equal? (suc n) (suc .n) | eq refl = eq refl
equal? (suc _) (suc _) | neq p = neq (s≠s p)

infix 20 _⊆_
-- subset means each lhs element can be dropped or
-- kept, but you do not have an element that
-- is kept on lhs and dropped on rhs
data _⊆_ {A : Set} : List A -> List A -> Set where
  stop : [] ⊆ []
  keep : ∀ {x xs ys} -> xs ⊆ ys -> x :: xs ⊆ x :: ys
  drop : ∀ {xs y ys} -> xs ⊆ ys -> xs ⊆ y :: ys

filter : {A : Set} -> (A -> Bool) -> List A -> List A 
filter _ [] = [] 
filter p (x :: xs) with p x 
... | true = x :: filter p xs 
... | false = filter p xs

lem-filter : {A : Set}(p : A -> Bool)(xs : List A) ->
             filter p xs ⊆ xs
lem-filter _ [] = stop
lem-filter p (x :: xs) with p x
... | true = keep (lem-filter p xs)
... | false = drop (lem-filter p xs)

infixl 40 _+_ 
_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)

lem-plus-zero : ∀ n -> n + zero == n
lem-plus-zero zero = refl
lem-plus-zero (suc n) with n + zero | lem-plus-zero n
... | .n | refl = refl

vec : {n : Nat}{A : Set} -> A -> Vec A n
vec {zero} _ = []
vec {suc _} x = x :: vec x

infixl 90 _$_ 
_$_ : {n : Nat}{A B : Set} -> Vec (A -> B) n -> Vec A n -> Vec B n
[] $ [] = []
(f :: fs) $ (x :: xs) = f x :: (fs $ xs)

Matrix : Set -> Nat -> Nat -> Set
Matrix A n m = Vec (Vec A n) m

vmap : {A B : Set}{n : Nat} -> (A -> B) -> Vec A n -> Vec B n
vmap f xss = vec f $ xss

-- transpose : ∀ {A n m} → Matrix A n m → Matrix A m n
-- transpose [] = vec []
-- transpose ([] :: _) = []
-- transpose xss with vec (λ x :: _ → x) $ xss | vec (λ _ :: xs → xs) $ xss
-- ... | column | remainder = column :: transpose remainder

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

infixl 90 _!_
_!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
[] ! ()
(x :: _) ! fzero = x
(_ :: xs) ! (fsuc i) = xs ! i

testFin : Fin (suc (suc (suc zero)))
testFin = fsuc fzero

test! : P ((zero :: suc zero :: []) ! (fsuc fzero)) -> P (suc zero)
test! x = x

_◦_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set} 
      (f : {x : A}(y : B x) -> C x y)(g : (x : A) -> B x) 
      (x : A) -> C x (g x)
(f ◦ g) x = f (g x)

tabulate : {n : Nat}{A : Set} -> (Fin n -> A) -> Vec A n
tabulate {zero} _ = []
tabulate {suc _} f = f fzero :: tabulate (f ◦ fsuc)

lem-!-tab : ∀{n A}(f : Fin n -> A)(i : Fin n) ->
            tabulate f ! i == f i
lem-!-tab f fzero = refl
lem-!-tab f (fsuc i) = lem-!-tab (f ◦ fsuc) i
