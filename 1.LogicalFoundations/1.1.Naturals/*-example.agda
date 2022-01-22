import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

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