{-# OPTIONS --universe-polymorphism #-}
module Sandbox where
open import Data.Bool hiding ( _≟_ )
open import Data.Nat
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.List hiding ( any )
open import Data.List.Any
open Membership-≡

tester : 2 ∈ 1 ∷ 2 ∷ []
tester = there (here refl)

tester₂ : 2 ∈ 1 ∷ 2 ∷ []
tester₂ = toWitness {Q = any (_≟_ 2) (1 ∷ 2 ∷ [])} _

decTest : true ≡ ⌊ any (_≟_ 2) (1 ∷ 2 ∷ []) ⌋
decTest = refl

decTest₂ : false ≡ ⌊ any (_≟_ 3) (1 ∷ 2 ∷ []) ⌋
decTest₂ = refl

-- Because this can be proven by the empty record,
-- it can be an implicit precondition!
decTruth : True (any (_≟_ 2) (1 ∷ 2 ∷ []))
decTruth = _

decAbsurdity : False (any (_≟_ 3) (1 ∷ 2 ∷ []))
decAbsurdity = _

