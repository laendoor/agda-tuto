import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import plfa.part1.Naturals

{-# BUILTIN NATURAL ℕ #-}

module exercises.part1.Naturals.Ex02_example where

  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  (suc m) + n = suc (m + n)

  _*_ : ℕ → ℕ → ℕ
  zero    * n  =  zero
  (suc m) * n  =  n + (m * n)

  _ = refl
  _ = 3 * 4 ≡ 12
  _ =
    begin
      3 * 4
    ≡⟨⟩
      (suc 2) * 4
    ≡⟨⟩
      4 + (2 * 4)
    ≡⟨⟩
      4 + 8
    ≡⟨⟩
      12
    ∎