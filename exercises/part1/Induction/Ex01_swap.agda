import Relation.Binary.PropositionalEquality as Eq
import plfa.part1.Induction as Tuto

open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open Tuto using (+-assoc′; +-identity′; +-suc′; +-comm′)

-- Exercise +-swap (recommended)
module exercises.part1.Induction.Ex01_swap where
  +-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
  +-swap m n p =
    begin
      m + (n + p)
    ≡⟨ sym (+-assoc′ m n p) ⟩
      m + n + p
    ≡⟨ cong (_+ p) (+-comm′ m n) ⟩
      (n + m) + p
    ≡⟨ +-assoc′ n m p ⟩
      n + (m + p)
    ∎

