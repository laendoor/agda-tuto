import Relation.Binary.PropositionalEquality as Eq
import plfa.part1.Induction as Tuto

open Tuto using (+-assoc′)
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- Exercise *-distrib-+ (recommended)
module exercises.part1.Induction.Ex02_distrib where
  *-neutral′ : ∀ (n : ℕ) → n * zero ≡ zero
  *-neutral′ zero = refl
  *-neutral′ (suc n) =
    begin
      n * zero
    ≡⟨ *-neutral′ n ⟩
      zero
    ∎

  *-identity′ : ∀ (n : ℕ) → n * (suc zero) ≡ n
  *-identity′ zero = refl
  *-identity′ (suc n) =
    begin
      suc n * (suc zero)
     ≡⟨ refl ⟩
      suc (n * (suc zero))
     ≡⟨ cong suc (*-identity′ n) ⟩
      suc n
    ∎

  *-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
  *-distrib-+ zero n p = refl
  *-distrib-+ (suc m) n p =
    begin
      (suc m + n) * p
    ≡⟨ refl ⟩
      suc (m + n) * p
    ≡⟨ refl ⟩ -- suc n * m = m + n * m
      p + (m + n) * p
    ≡⟨ cong (_+_ p) (*-distrib-+ m n p) ⟩
      p + (m * p + n * p)
    ≡⟨ sym (+-assoc′ _ (m * p) (n * p)) ⟩
      p + m * p + n * p
    ∎
