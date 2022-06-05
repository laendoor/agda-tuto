import Relation.Binary.PropositionalEquality as Eq
import plfa.part1.Induction as Tuto
import exercise.part1.Induction.Ex05_zerominus as Ex05

open Eq using (_≡_; _≢_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open Tuto using (+-comm′; +-identity′; +-rearrange; +-assoc′)
open Ex05 using (zz)

-- Exercise ∸-|-assoc (practice)
-- Show that monus associates with addition, that is,
--       m ∸ n ∸ p ≡ m ∸ (n + p)
-- for all naturals m, n, and p.
module exercise.part1.Induction.Ex06_assoc where

∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc m zero p = refl
∸-|-assoc zero (suc n) p = 
  begin
    zero ∸ p
   ≡⟨ zz p ⟩
    zero
  ∎
∸-|-assoc (suc m) (suc n) p = 
  begin
    m ∸ n ∸ p
   ≡⟨ ∸-|-assoc m n p ⟩
    m ∸ (n + p)
  ∎
