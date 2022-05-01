import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import plfa.part1.Naturals

{-# BUILTIN NATURAL ℕ #-}

module exercises.part1.Naturals.Ex03_exponent where

  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  (suc m) + n = suc (m + n)

  _*_ : ℕ → ℕ → ℕ
  zero    * n  =  zero
  (suc m) * n  =  n + (m * n)

  _^_ : ℕ → ℕ → ℕ
  n ^ zero    = suc zero
  n ^ (suc m) = n * (n ^ m)

  _ = refl
  _ = 3 ^ 4 ≡ 81
  _ =
    begin
      3 ^ 4
    ≡⟨⟩
      3 ^ (suc 3)
    ≡⟨⟩
      3 * (3 ^ 3)
    ≡⟨⟩
      3 * 27
    ≡⟨⟩
      81
    ∎