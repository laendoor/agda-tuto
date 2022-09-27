import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

-- Standard library
-- import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)

module plfa.part1.Induction where

-- # Associativity
-- // One property of addition is that it is associative, that is,
-- // that the location of the parentheses does not matter:
--    (m + n) + p ≡ m + (n + p)
-- // Here `m`, `n`, and `p` are variables that range over all natural numbers.

-- // We can test the proposition by choosing specific numbers for the three variables:
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

-- # Our first proof: associativity
-- To prove associativity, we take `P m` to be the property:
-- (m + n) + p ≡ m + (n + p)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- # Induction as recursion
-- As a concrete example of how induction corresponds to recursion,
-- here is the computation that occurs when instantiating m to 2 in the proof of associativity.
+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    2 + (n + p)
  ∎
  where
  +-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
  +-assoc-1 n p =
    begin
      (1 + n) + p
    ≡⟨⟩
      suc (0 + n) + p
    ≡⟨⟩
      suc ((0 + n) + p)
    ≡⟨ cong suc (+-assoc-0 n p) ⟩
      suc (0 + (n + p))
    ≡⟨⟩
      1 + (n + p)
    ∎
    where
    +-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
    +-assoc-0 n p =
      begin
        (0 + n) + p
      ≡⟨⟩
        n + p
      ≡⟨⟩
        0 + (n + p)
      ∎

-- # Our second proof: commutativity
-- Another important property of addition is that it is commutative, that is,
-- that the order of the operands does not matter:
--   m + n ≡ n + m

-- The first lemma
-- The base case of the definition of addition states that zero is a left-identity:
--   zero + n ≡ n
-- Our first lemma states that zero is also a right-identity:
--   m + zero ≡ m

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

-- # The second lemma
-- The inductive case of the definition of addition pushes suc on the first argument to the outside:
--   suc m + n ≡ suc (m + n)
-- Our second lemma does the same for suc on the second argument:
--   m + suc n ≡ suc (m + n)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

-- # The proposition

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- # Our first corollary: rearranging

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ≡⟨⟩
    m + (n + p) + q
  ∎

-- # Exercise `finite-+-assoc` (stretch)
-- Write out what is known about associativity of addition on each of the first four days
-- using a finite story of creation, as earlier.

-- In the beginning, we know nothing.
-- On the first day
{-
(0 + n) + p = (n) + p
            = n + p
            = (n + p)
            = 0 + (n + p)
-}

-- On the second day
{-
(0 + n) + p = 0 + (n + p)
(1 + n) + p = (1 + 0 + n) + p
            = 1 + (0 + n) + p
            = 1 + (n + p)
 -}

-- On the third day
{-
(0 + n) + p = 0 + (n + p)
(1 + n) + p = 1 + (n + p)
(2 + n) + p = (1 + 1 + n) + p
            = 1 + (1 + n) + p
            = 1 + 1 + (n + p)
            = 2 + (n + p)
 -}

-- On the fourth day
{-
(0 + n) + p = 0 + (n + p)
(1 + n) + p = 1 + (n + p)
(2 + n) + p = 2 + (n + p)
(3 + n) + p = (1 + 2 + n) + p
            = 1 + (2 + n) + p
            = 1 + 2 + (n + p)
            = 3 + (n + p)
 -}

-- # Associativity with rewrite
-- Here is a second proof of associativity of addition in Agda,
-- using rewrite rather than chains of equations:

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

-- # Commutativity with rewrite
-- Here is a second proof of commutativity of addition,
-- using rewrite rather than chains of equations:

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- # Exercise `+-swap` (recommended)
-- Show: m + (n + p) ≡ n + (m + p)
-- for all naturals m, n, and p.
-- No induction is needed, just apply the previous results which show addition is associative and commutative.

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


-- # Exercise `*-distrib-+` (recommended)
-- Show multiplication distributes over addition
-- i.e. (m + n) * p ≡ m * p + n * p

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
  ≡⟨ sym (+-assoc _ (m * p) (n * p)) ⟩
    p + m * p + n * p
  ∎

-- # Exercise *-assoc (recommended)
-- Show multiplication is associative
--   (m * n) * p ≡ m * (n * p)
-- for all naturals m, n, and p.

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p = 
  begin
    (suc m * n) * p -- suc n * m = m + n * m
    ≡⟨ refl ⟩
    (n + m * n) * p
    ≡⟨ *-distrib-+ n (m * n) p ⟩
    (n * p) + ((m * n) * p)
    ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    (n * p) + m * (n * p) 
    ≡⟨ refl ⟩ -- suc n * m = m + n * m
    suc m * (n * p) 
  ∎

-- # Exercise `*-comm` (practice)
-- Show multiplication is commutative
-- i.e. m * n ≡ n * m
-- You will need to formulate and prove suitable lemmas.

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

*-distrib-+ˡ : ∀ (p m n : ℕ) → p * (m + n) ≡ p * m + p * n
*-distrib-+ˡ zero m n = refl
*-distrib-+ˡ (suc p) m n = 
  begin
    m + n + (p * (m + n))
  ≡⟨ cong ((m + n) +_) (*-distrib-+ˡ p m n) ⟩
    m + n + (p * m + p * n)
  ≡⟨ +-rearrange m n (p * m) (p * n) ⟩
    m + (n + p * m) + p * n
  ≡⟨ cong (_+ (p * n)) (cong (m +_) (+-comm′ n (p * m))) ⟩
    m + (p * m + n) + p * n
  ≡⟨ sym (+-rearrange m (p * m) n (p * n))  ⟩
    (m + p * m) + (n + p * n)
  ≡⟨ refl ⟩
    m + p * m + (n + p * n)
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n =
  begin
    zero
  ≡⟨ sym (*-neutral′ n) ⟩
    n * zero
  ∎
*-comm (suc m) n = 
  begin
    (suc m) * n
   ≡⟨ refl ⟩
    n + m * n
   ≡⟨ cong (_+ (m * n)) (sym (*-identity′ n)) ⟩
    n * 1 + m * n
   ≡⟨ cong ((n * 1) +_) (*-comm m n) ⟩
    n * 1 + n * m
   ≡⟨ sym (*-distrib-+ˡ n 1 m) ⟩
    n * (1 + m)
   ≡⟨ refl ⟩
    n * suc m
  ∎

-- # Exercise `0∸n≡0` (practice)
-- Show: zero ∸ n ≡ zero
-- for all naturals n. Did your proof require induction?

zz : ∀ (n : ℕ) → zero ∸ n ≡ zero
zz zero = refl
zz (suc n) = refl

-- # Exercise `∸-+-assoc` (practice)
-- Show that monus associates with addition, that is,
--   m ∸ n ∸ p ≡ m ∸ (n + p)
-- for all naturals m, n, and p.

∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc m zero p = refl
∸-|-assoc zero (suc n) p = 
  begin
    zero ∸ p
   ≡⟨ zz p ⟩
    zero
  ∎
∸-|-assoc (suc m) (suc n) p = 
  begin
    m ∸ n ∸ p
   ≡⟨ ∸-|-assoc m n p ⟩
    m ∸ (n + p)
  ∎

-- # Exercise +*^ (stretch)
-- Show the following three laws
--   m ^ (n + p) ≡ (m ^ n) * (m ^ p)   (^-distribˡ-+-*)
--   (m * n) ^ p ≡ (m ^ p) * (n ^ p)   (^-distribʳ-*)
--   (m ^ n) ^ p ≡ m ^ (n * p)         (^-*-assoc)
-- for all m, n, and p.

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

-- # Exercise Bin-laws (stretch)
-- Recall that Exercise Bin defines a datatype Bin of bitstrings
-- representing natural numbers, and asks you to define functions

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc    ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to   : ℕ → Bin
to zero    = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = 2 * (from b)
from (b I) = 2 * (from b) + 1

-- Consider the following laws, where n ranges over naturals and b over bitstrings:
--   from (inc b) ≡ suc (from b)
--   to (from b) ≡ b
--   from (to n) ≡ n
-- For each law: if it holds, prove; if not, give a counterexample.

l1 : ∀ (n : ℕ) → suc n ≡ n + 1
l1 zero = refl
l1 (suc n) = 
  begin
    suc (suc n)
   ≡⟨ cong suc (l1 n) ⟩
    suc (n + 1)
  ∎

law₁ : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
law₁ ⟨⟩ = refl
law₁ (b O) = 
  begin
    from b + (from b + zero) + 1
   ≡⟨ +-comm (from b + (from b + zero)) 1 ⟩
    suc zero + from b + (from b + zero)
   ≡⟨ refl ⟩
    suc (from b + (from b + zero))
  ∎
law₁ (b I) = 
  begin
    from (inc b) + (from (inc b) + zero)
   ≡⟨ cong (_+ (from (inc b) + zero)) (law₁ b) ⟩
    suc (from b) + (from (inc b) + zero)
   ≡⟨ cong (suc (from b) +_) (cong (_+ zero) (law₁ b)) ⟩
    suc (from b) + (suc (from b) + zero)
   ≡⟨ refl ⟩
    suc (from b) + suc (from b + zero)
   ≡⟨ cong ((suc (from b)) +_) (l1 (from b + zero))  ⟩
    suc (from b) + ((from b + zero) + 1)
   ≡⟨ refl ⟩
    suc (from b + ((from b + zero) + 1))
   ≡⟨ cong suc (sym (+-assoc (from b) (from b + zero) 1)) ⟩
    suc (from b + (from b + zero) + 1)
  ∎

-- !! invalid postulate
postulate law₂ : ∀ (b : Bin) → to (from b) ≡ b
{- law₂ ⟨⟩ = 
  begin
    (⟨⟩ O)
   ≡⟨ {!   !} ⟩ -- ! no se puede
    ⟨⟩
  ∎
law₂ (b O) = {!   !}
law₂ (b I) = {!   !} -}

law₃ : ∀ (n : ℕ) →  from (to n) ≡ n
law₃ zero = refl
law₃ (suc n) = 
  begin
    from (inc (to n))
   ≡⟨ law₁ (to n) ⟩
    suc (from (to n))
   ≡⟨ cong suc (law₃ n) ⟩
    suc n
  ∎