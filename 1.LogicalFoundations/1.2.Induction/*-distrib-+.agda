import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

*-neutral′ : ∀ (n : ℕ) → n * zero ≡ zero
*-neutral′ zero = refl
*-neutral′ (suc n) rewrite *-neutral′ n = refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

*-identity′ : ∀ (n : ℕ) → n * (suc zero) ≡ n
*-identity′ zero = refl
*-identity′ (suc n) rewrite *-identity′ n = refl

*-suc′ : ∀ (m n : ℕ) → m * (suc n) ≡ m + (m * n)
*-suc′ m zero = 
  begin
    m * (suc zero)
  ≡⟨ *-identity′ m ⟩
    m
  ≡⟨ sym (+-identity′ m) ⟩
    m + zero
  ≡⟨ cong (m +_) (sym (*-neutral′ m)) ⟩
    m + (m * zero) 
  ∎
*-suc′ m (suc n) = 
  begin
    m * (suc (suc n))
  ≡⟨ {!   !} ⟩
  m + (m * (suc n))
  ∎

*-comm′ : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm′ m zero rewrite *-identity′ m | *-neutral′ m = refl
*-comm′ m (suc n) =
  begin
    m * (suc n)
  ≡⟨ {!   !} ⟩
    (suc n) * m
  ∎

-- p + m * p ≡ (m + 1) * p
-- +bla : ∀ (m p : ℕ) → (m + 1) * p ≡ m * p + p
-- +bla zero p =
--   begin
--     (zero + 1) * p
--   ≡⟨ refl ⟩
--     1 * p
--   ≡⟨ {!  refl !} ⟩
--    p
--   ≡⟨ {!   !} ⟩
--    zero + p
--   ≡⟨ {!   !} ⟩
--     (zero * p) + p
--   ∎
-- +bla (suc m) p = {!   !}

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