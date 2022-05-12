import Relation.Binary.PropositionalEquality as Eq
import plfa.part1.Induction as Tuto
import exercise.part1.Induction.Ex02_distrib as TutoEx

open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open Tuto using (+-comm′; +-identity′; +-rearrange; +-assoc′)
open TutoEx using (*-neutral′; *-identity′; *-distrib-+)

-- Exercise *-comm (practice)
-- Show multiplication is commutative, that is,
--   m * n ≡ n * m
-- for all naturals m and n.
-- As with commutativity of addition, you will need to formulate and prove suitable lemmas.
module exercise.part1.Induction.Ex04_comm where

*-distrib2 : ∀ (p m n : ℕ) → p * (m + n) ≡ p * m + p * n
*-distrib2 zero m n = refl
*-distrib2 (suc p) m n = 
  begin
    m + n + (p * (m + n))
  ≡⟨ cong ((m + n) +_) (*-distrib2 p m n) ⟩
    m + n + (p * m + p * n)
  ≡⟨ +-rearrange m n (p * m) (p * n) ⟩
    m + (n + p * m) + p * n
  ≡⟨ cong (_+ (p * n)) (cong (m +_) (+-comm′ n (p * m))) ⟩
    m + (p * m + n) + p * n
  ≡⟨ sym (+-rearrange m (p * m) n (p * n))  ⟩
    (m + p * m) + (n + p * n)
  ≡⟨ refl ⟩
    m + p * m + (n + p * n)
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n =
  begin
    zero
  ≡⟨ sym (*-neutral′ n) ⟩
    n * zero
  ∎
*-comm (suc m) n = 
  begin
    (suc m) * n
   ≡⟨ refl ⟩
    n + m * n
   ≡⟨ cong (_+ (m * n)) (sym (*-identity′ n)) ⟩
    n * 1 + m * n
   ≡⟨ cong ((n * 1) +_) (*-comm m n) ⟩
    n * 1 + n * m
   ≡⟨ sym (*-distrib2 n 1 m) ⟩
    n * (1 + m)
   ≡⟨ refl ⟩
    n * suc m
  ∎
