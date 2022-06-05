import Relation.Binary.PropositionalEquality as Eq
import plfa.part1.Induction as TutoInduction
import exercise.part1.Induction.Ex03_assoc as Ex03Induction
import exercise.part1.Induction.Ex04_comm as Ex04Induction

open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open TutoInduction using (+-comm)
open Ex03Induction using (*-assoc)
open Ex04Induction using (*-comm)

-- Exercise +*^ (stretch)
-- Show the following three laws
--        m ^ (n + p) ≡ (m ^ n) * (m ^ p)  (^-distribˡ-|-*)
--        (m * n) ^ p ≡ (m ^ p) * (n ^ p)  (^-distribʳ-*)
--        (m ^ n) ^ p ≡ m ^ (n * p)        (^-*-assoc)
-- for all m, n, and p.
module exercise.part1.Induction.Ex07_stretch1 where

^-distribˡ-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-|-* m zero p = 
  begin
    (m ^ p)
   ≡⟨ refl ⟩
    zero + (m ^ p)
   ≡⟨ +-comm zero (m ^ p) ⟩
    (m ^ p) + zero
  ∎
^-distribˡ-|-* m (suc n) p = 
  begin
    m * (m ^ (n + p))
   ≡⟨ cong (m *_) (^-distribˡ-|-* m n p) ⟩
    m * ((m ^ n) * (m ^ p))
   ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    m * (m ^ n) * (m ^ p)
  ∎

lemma₁ : ∀ (m n p q : ℕ) → m * n * (p * q) ≡ m * p * (n * q)
lemma₁ m n p q = 
  begin
    m * n * (p * q)
   ≡⟨ sym (*-assoc (m * n) p q) ⟩
    m * n * p * q
   ≡⟨ cong (_* q) (*-assoc m n p) ⟩
    m * (n * p) * q
   ≡⟨ cong (_* q) (cong (m *_) (*-comm n p)) ⟩
    m * (p * n) * q
   ≡⟨ cong (_* q) (sym (*-assoc m p n)) ⟩
    m * p * n * q
   ≡⟨ *-assoc (m * p) n q ⟩
    m * p * (n * q)
  ∎


^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) = 
  begin
    m * n * ((m * n) ^ p)
   ≡⟨ cong ((m * n) *_) (^-distribʳ-* m n p) ⟩
    m * n * ((m ^ p) * (n ^ p))
   ≡⟨ lemma₁ m n (m ^ p) (n ^ p) ⟩
    m * (m ^ p) * (n * (n ^ p))
  ∎

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero = 
  begin
    1
   ≡⟨ refl ⟩
    m ^ zero
   ≡⟨ refl ⟩
    m ^ (zero * n)
   ≡⟨ cong (m ^_) (*-comm zero n) ⟩
    m ^ (n * zero)
  ∎
^-*-assoc m n (suc p) = 
  begin
    (m ^ n) * ((m ^ n) ^ p)
   ≡⟨ cong ((m ^ n) *_) (^-*-assoc m n p) ⟩
    (m ^ n) * (m ^ (n * p))
   ≡⟨ sym (^-distribˡ-|-* m n (n * p)) ⟩
    (m ^ (n + n * p))
   ≡⟨ cong (m ^_) (cong (n +_) (*-comm n p)) ⟩
    (m ^ (n + p * n))
   ≡⟨ refl ⟩
    (m ^ (suc p * n))
   ≡⟨ cong (m ^_) (*-comm (suc p) n) ⟩
    (m ^ (n * suc p))
  ∎