import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p  
  rewrite sym (+-assoc′ m n p)
    | cong (_+ p) (+-comm′ m n)
    | +-assoc′ n m p
    = refl

+-swap1 : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap1 m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc′ m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm′ m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc′ n m p ⟩
    n + (m + p)
  ∎

