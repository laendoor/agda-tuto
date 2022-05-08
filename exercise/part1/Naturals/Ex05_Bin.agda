import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

module exercise.part1.Naturals.Ex05_Bin where

  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

  inc : Bin → Bin
  inc    ⟨⟩ = ⟨⟩ I
  inc (b O) = b I
  inc (b I) = (inc b) O

  -- inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
  _ = begin
      inc (⟨⟩ I O I I)
    ≡⟨⟩
      ⟨⟩ I I O O
    ∎

  --  inc (⟨⟩ I I I I) ≡ ⟨⟩ I O O O O
  _ = begin
      inc (⟨⟩ I I I I)
    ≡⟨⟩
      ⟨⟩ I O O O O
    ∎

  to   : ℕ → Bin
  to zero    = ⟨⟩ O
  to (suc n) = inc (to n)

  from : Bin → ℕ
  from ⟨⟩ = 0
  from (b O) = 2 * (from b)
  from (b I) = 2 * (from b) + 1

  -- 2 ≡ ⟨⟩ I O
  _ =
    begin
      to 2
    ≡⟨⟩
      ⟨⟩ I O
    ∎

  -- 5 ≡ ⟨⟩ I O I
  _ =
    begin
      to 5
    ≡⟨⟩
      ⟨⟩ I O I
    ∎

  -- 10 ≡ ⟨⟩ I O I O
  _ =
    begin
      to 10
    ≡⟨⟩
      ⟨⟩ I O I O
    ∎


  -- ⟨⟩ I O ≡ 2
  _ =
    begin
      from (⟨⟩ I O)
    ≡⟨⟩
      2
    ∎

  -- ⟨⟩ I O I ≡ 5
  _ =
    begin
      from (⟨⟩ I O I)
    ≡⟨⟩
      5
    ∎

  -- ⟨⟩ I O I O ≡ 10
  _ =
    begin
      from (⟨⟩ I O I O)
    ≡⟨⟩
      10
    ∎
