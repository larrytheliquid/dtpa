module Views where
open import Relation.Binary.Core
open import Data.Nat

data Parity : ℕ → Set where 
  even : (k : ℕ) → Parity (k * 2) 
  odd : (k : ℕ) → Parity (1 + k * 2) 

parity : (n : ℕ) -> Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(1 + k * 2)) | odd k = even (suc k)

test-parity : parity 43 ≡ odd 21
test-parity = refl