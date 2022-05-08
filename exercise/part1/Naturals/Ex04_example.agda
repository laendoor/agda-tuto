import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import plfa.part1.Naturals

{-# BUILTIN NATURAL ℕ #-}

module exercise.part1.Naturals.Ex04_example where

  _∸_ : ℕ → ℕ → ℕ
  m     ∸ zero  = m
  zero  ∸ suc n = zero
  suc m ∸ suc n = m ∸ n

  _ = 5 ∸ 3 ≡ 2
  _ = 3 ∸ 5 ≡ 0
  _ = 
    begin
      5 ∸ 3
    ≡⟨⟩
      4 ∸ 2
    ≡⟨⟩
      3 ∸ 1
    ≡⟨⟩
      2 ∸ 0
    ≡⟨⟩
      2
    ∎

  _ = 
    begin
      3 ∸ 5
    ≡⟨⟩
      2 ∸ 4
    ≡⟨⟩
      1 ∸ 3
    ≡⟨⟩
      0 ∸ 2
    ≡⟨⟩
      0
    ∎