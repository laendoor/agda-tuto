import Relation.Binary.PropositionalEquality as Eq
import plfa.part1.Induction as TutoInduction
import exercise.part1.Naturals.Ex05_Bin as Ex05Bin

open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open TutoInduction using (+-comm; +-assoc)
open Ex05Bin

-- Exercise Bin-laws (stretch)
-- Recall that Exercise Bin defines a datatype Bin of bitstrings representing natural numbers, and asks you to define functions
--      inc   : Bin → Bin
--      to    : ℕ → Bin
--      from  : Bin → ℕ
-- Consider the following laws, where n ranges over naturals and b over bitstrings:
--      from (inc b) ≡ suc (from b)
--      to (from b) ≡ b
--      from (to n) ≡ n
-- For each law: if it holds, prove; if not, give a counterexample.
module exercise.part1.Induction.Ex08_Bin-laws where

l1 : ∀ (n : ℕ) → suc n ≡ n + 1
l1 zero = refl
l1 (suc n) = 
  begin
    suc (suc n)
   ≡⟨ cong suc (l1 n) ⟩
    suc (n + 1)
  ∎

law₁ : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
law₁ ⟨⟩ = refl
law₁ (b O) = 
  begin
    from b + (from b + zero) + 1
   ≡⟨ +-comm (from b + (from b + zero)) 1 ⟩
    suc zero + from b + (from b + zero)
   ≡⟨ refl ⟩
    suc (from b + (from b + zero))
  ∎
law₁ (b I) = 
  begin
    from (inc b) + (from (inc b) + zero)
   ≡⟨ cong (_+ (from (inc b) + zero)) (law₁ b) ⟩
    suc (from b) + (from (inc b) + zero)
   ≡⟨ cong (suc (from b) +_) (cong (_+ zero) (law₁ b)) ⟩
    suc (from b) + (suc (from b) + zero)
   ≡⟨ refl ⟩
    suc (from b) + suc (from b + zero)
   ≡⟨ cong ((suc (from b)) +_) (l1 (from b + zero))  ⟩
    suc (from b) + ((from b + zero) + 1)
   ≡⟨ refl ⟩
    suc (from b + ((from b + zero) + 1))
   ≡⟨ cong suc (sym (+-assoc (from b) (from b + zero) 1)) ⟩
    suc (from b + (from b + zero) + 1)
  ∎

law₂ : ∀ (b : Bin) → to (from b) ≡ b
law₂ ⟨⟩ = 
  begin
    (⟨⟩ O)
   ≡⟨ {!   !} ⟩ -- para mi no se puede
    ⟨⟩
  ∎
law₂ (b O) = {!   !}
law₂ (b I) = {!   !}

law₃ : ∀ (n : ℕ) →  from (to n) ≡ n
law₃ zero = refl
law₃ (suc n) = 
  begin
    from (inc (to n))
   ≡⟨ law₁ (to n) ⟩
    suc (from (to n))
   ≡⟨ cong suc (law₃ n) ⟩
    suc n
  ∎