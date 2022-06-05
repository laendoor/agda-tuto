import Relation.Binary.PropositionalEquality as Eq
import plfa.part1.Induction as Tuto
import exercise.part1.Induction.Ex02_distrib as TutoEx

open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open Tuto using (+-comm′; +-identity′; +-rearrange; +-assoc′)
open TutoEx using (*-neutral′; *-identity′; *-distrib-+)

-- Exercise 0∸n≡0 (practice)
-- Show
--      zero ∸ n ≡ zero
-- for all naturals n. Did your proof require induction?
module exercise.part1.Induction.Ex05_zerominus where

zz : ∀ (n : ℕ) → zero ∸ n ≡ zero
zz zero = refl
zz (suc n) = refl
