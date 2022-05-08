import Relation.Binary.PropositionalEquality as Eq
import exercises.part1.Induction.Ex02_distrib as Tuto

open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open Tuto using (*-distrib-+)

-- Exercise *-assoc (recommended)
-- Show multiplication is associative, that is,
--   (m * n) * p ≡ m * (n * p)
-- for all naturals m, n, and p.
module exercise.part1.Induction.Ex03_assoc where

  *-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
  *-assoc zero n p = refl
  *-assoc (suc m) n p = 
    begin
      (suc m * n) * p -- suc n * m = m + n * m
     ≡⟨ refl ⟩
      (n + m * n) * p
     ≡⟨ *-distrib-+ n (m * n) p ⟩
      (n * p) + ((m * n) * p)
     ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
      (n * p) + m * (n * p) 
     ≡⟨ refl ⟩ -- suc n * m = m + n * m
      suc m * (n * p) 
    ∎