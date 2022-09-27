import Relation.Binary.PropositionalEquality as Eq
import plfa.part1.Induction as Induction
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_) 
open import Data.Nat.Properties using (+-comm; +-identityʳ)
open Induction using (Bin; ⟨⟩; _O; _I; from; inc; to; law₁)

module plfa.part1.Relations where

infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  -- z≤n ----------
  --      zero ≤ n
  z≤n : ∀ {n : ℕ} → zero ≤ n

  --          m ≤ n
  -- s≤s ---------------
  --      suc m ≤ suc n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
  -- This is our first use of an indexed datatype, where the type m ≤ n is indexed by two naturals, m and n.

-- the proof that 2 ≤ 4
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

-- here is the Agda proof that 2 ≤ 4 repeated, with the implicit arguments made explicit:
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

-- One may also identify implicit arguments by name:
_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

-- In the latter format, you can choose to only supply some implicit arguments:
_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)

-- ^ It is not permitted to swap implicit arguments, even when named.

-- We can ask Agda to use the same inference to try and infer an explicit term, by writing _.
-- For instance, we can define a variant of the proposition +-identityʳ with implicit arguments:
+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _
-- We use _ to ask Agda to infer the value of the explicit argument from context. 

-- Inversion

-- There is only one way to prove that suc m ≤ suc n, for any m and n. This lets us invert our previous rule.
inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

-- ^ Not every rule is invertible; indeed, the rule for z≤n has no non-implicit hypotheses.

-- Another example of inversion is showing that there is only one way a number can be less than or equal to zero.
inv-z≤n : ∀ {m : ℕ} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl


-- ^ Reflexive: For all `n`, `n ≤ n`
-- ^ Transitive: For all `m`, `n`, and `p`, if `m ≤ n` and `n ≤ p` then `m ≤ p`
-- ^ Anti-symmetric: For all `m` and `n`, if both `m ≤ n` and `n ≤ m`, then `m ≡ n`
-- ^ Total: For all `m` and `n`, either `m ≤ n` or `n ≤ m` holds.
-- The relation _≤_ satisfies all four of these properties.

-- ^ Preorder: Any relation that is `reflexive` and `transitive`
-- ^ Partial order: Any `preorder` that is also `anti-symmetric`
-- ^ Total order: Any `partial order` that is also `total`.

-- # Ex00_orderings.agda (practice)
-- Give an example of a preorder that is not a partial order.
-- TODO

-- Give an example of a partial order that is not a total order.
-- TODO

-- # Reflexivity
≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl
-- * ≤-refl {suc n} = s≤s (≤-refl {n})
-- ^ The proof is a straightforward induction on the implicit argument `n`

-- # Transitivity
≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)
-- The case `≤-trans (s≤s m≤n) z≤n` cannot arise,
-- 1 <= 1 -> 0 <= 1 -> 2 <= 2
-- since the first inequality implies the middle value is `suc n`
-- while the second inequality implies that it is `zero`.

-- Alternatively, we could make the implicit parameters explicit:
≤-trans′ : ∀ (m n p : ℕ) → m ≤ n → n ≤ p → m ≤ p
≤-trans′ zero    _       _       z≤n       _          =  z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans′ m n p m≤n n≤p)

-- # Anti-symmetry
≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n       z≤n       = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)
--                 `s≤s m≤n`       & `s≤s n≤m`
-- so we are given `suc m ≤ suc n` & `suc n ≤ suc m`
-- and must show   `suc m ≡ suc n`

-- # Exercise `≤-antisym-cases` (practice)
-- The above proof omits cases where one argument is `z≤n` and one argument is `s≤s`.
-- Why is it ok to omit them?
≤-antisym-case : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym-case z≤n z≤n = refl
-- * ≤-antisym-case z≤n (s≤s n≤m) = {!   !}
-- The case for the constructor `s≤s` is impossible
-- because unification ended with a conflicting equation
--   `suc n ≟ zero`
-- * ≤-antisym-case (s≤s m≤n) z≤n = {!   !}
-- The case for the constructor `z≤n` is impossible
-- because unification ended with a conflicting equation
--   zero ≟ suc n
≤-antisym-case (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym-case m≤n n≤m)

-- # Total
data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n
-- ^ This is our first use of a datatype with parameters, in this case `m` and `n`.

-- It is equivalent to the following indexed datatype:
data Total′ : ℕ → ℕ → Set where
  forward′ : ∀ {m n : ℕ} → m ≤ n → Total′ m n
  flipped′ : ∀ {m n : ℕ} → n ≤ m → Total′ m n

-- we specify and prove totality
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)
-- The keyword with is followed by an expression and one or more subsequent lines.
-- Each line begins with an ellipsis (...) and a vertical bar (|),
-- followed by a pattern to be matched against the expression and the right-hand side of the equation.

-- Every use of with is equivalent to defining a helper function
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)

-- If both arguments are equal, then both cases hold and we could return evidence of either.
-- In the code above we return the `forward` case,
-- but there is a variant that returns the `flipped` case:
≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                         | forward m≤n  =  forward (s≤s m≤n)
...                         | flipped n≤m  =  flipped (s≤s n≤m)

-- # Monotonicity
-- ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q
-- The proof is straightforward using the techniques we have learned, and is best broken into three parts:

-- ^ 1st: show addition is monotonic on the right
+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

-- ^ 2nd: show addition is monotonic on the left
+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

-- * v1
≤+-monotˡ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
≤+-monotˡ m n p m≤n
  with  m + p  | +-comm m p |   n + p  | +-comm n p
... | .(p + m) | refl       | .(p + n) | refl       = +-monoʳ-≤ p m n m≤n

-- ^ 3rd: combine the two previous results
+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)
--                         ≤-trans (m + p ≤ n + p) (n + p ≤ n + q)
--                         m + p ≤ n + q

-- # Exercise `*-mono-≤` (stretch)
-- Show that multiplication is monotonic with regard to inequality.
-- i.e. ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m * p ≤ n * q

-- ? show addition is monotonic on the right
*-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero    p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)
-- goal: p + n * p ≤ q + n * q

-- ^ Solution
*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ zero    _       p q m≤n p≤q = z≤n
*-mono-≤ (suc m) (suc n) p q m≤n p≤q = +-mono-≤ p q (m * p) (n * q) p≤q (*-mono-≤ m n p q (inv-s≤s m≤n) p≤q)

-- todo *-mono-≤ con pttern matching sobre m≤n

-- # Strict inequality
-- We can define strict inequality similarly to inequality:

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

-- // strict inequality is transitive, is not reflexive, is not total
-- // but satisfies the closely related property of trichotomy: for any `m` and `n`,
-- // exactly one of `m < n`, `m ≡ n`, or `m > n` holds
-- // It is also monotonic with regards to addition and multiplication.

-- # Exercise `<-trans` (recommended)
-- Show that strict inequality is transitive

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s       (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- # Exercise trichotomy (practice)

-- Define `m > n` to be the same as `n < m`.
_>_ : ℕ → ℕ → Set
_>_ m n = n < m

-- Show that strict inequality satisfies a weak version of trichotomy,
-- in the sense that for any `m` and `n` that one of the following holds: * `m < n`, * `m ≡ n`, or * `m > n`.
-- You will need a suitable data declaration, similar to that used for totality.
-- (We will show that the three cases are exclusive after we introduce negation)

data Trichotomy (m n : ℕ) : Set where
  equal   : m ≡ n → Trichotomy m n
  lesser  : m < n → Trichotomy m n
  greater : m > n → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero    zero    = equal refl
<-trichotomy zero    (suc n) = lesser z<s
<-trichotomy (suc m) zero    = greater z<s
<-trichotomy (suc m) (suc n)
  with <-trichotomy m n 
...       | equal   m≡n = equal (cong suc m≡n)
...       | lesser  m<n = lesser (s<s m<n)
...       | greater n<m = greater (s<s n<m)


-- # Exercise +-mono-< (practice)
-- Show that addition is monotonic with respect to strict inequality.
-- As with inequality, some additional definitions may be required.

-- ∀ {m n p q : ℕ} → m < n → p < q → m + p < n + q

-- ^ 1st: show addition is monotonic on the right
+-monoʳ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero    p q p<q  = p<q
+-monoʳ-< (suc n) p q p<q  = s<s (+-monoʳ-< n p q p<q)

-- ^ 2nd: show addition is monotonic on the left
+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

-- ^ 3rd: combine the two previous results
+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

-- # Exercise ≤-iff-< (recommended)
-- Show that `suc m ≤ n` implies `m < n`, and conversely.

-- ^ 1st: show `suc m ≤ n → m < n`
≤-iff-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤-iff-< {zero}  {suc n} 1≤n₁ = z<s
≤-iff-< {suc m} {suc n} (s≤s m₁≤n) = s<s (≤-iff-< m₁≤n)

-- ^ 2nd: show `m < n → suc m ≤ n`
<-iff-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-iff-≤ {zero}  {suc n} 0<n₁      = s≤s z≤n
<-iff-≤ {suc m} {suc n} (s<s m<n) = s≤s (<-iff-≤ m<n)

-- # Exercise <-trans-revisited (practice)
-- Give an alternative proof that strict inequality is transitive,
-- using the relation between strict inequality and inequality
-- and the fact that inequality is transitive.

-- ^ mental notes
-- m < n → suc m ≤ n
-- n ≤ suc n
-- n < p → suc n ≤ p
-- suc m ≤ p → m < p
-- ≤-iff-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
-- <-iff-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
-- ≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p

n≤N : ∀ {n : ℕ} → n ≤ suc n
n≤N {zero}  = z≤n
n≤N {suc n} = s≤s n≤N

<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited m<n n<p = ≤-iff-< (≤-trans (<-iff-≤ m<n) (≤-trans n≤N (<-iff-≤ n<p)))

<-trans-revisitedʷ : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisitedʷ m<n n<p
  with <-iff-≤ m<n | <-iff-≤ n<p
...   | m₁≤n       | n₁≤p       = ≤-iff-< (≤-trans m₁≤n (≤-trans n≤N n₁≤p))

-- # Even and odd
-- As a further example, let's specify even and odd numbers.
-- Inequality and strict inequality are binary relations,
-- while even and odd are unary relations, sometimes called predicates:

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc  : ∀ {n : ℕ} → even n → odd (suc n)

-- This is our first use of overloaded constructors.
-- Here `suc` means one of three constructors:
-- suc : ℕ → ℕ
-- suc : ∀ {n : ℕ} → odd  n → even (suc n)
-- suc : ∀ {n : ℕ} → even n → odd  (suc n)

-- Due to how it does type inference,
-- ! Agda does NOT allow overloading of defined names (function names),
-- ! but allows to overload constructors

-- We show that the sum of two even numbers is even:
e+e≡e : ∀ {m n : ℕ} → even m → even n → even (m + n)
o+e≡o : ∀ {m n : ℕ} → odd  m → even n → odd  (m + n)

e+e≡e zero     en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)

-- This is our first use of mutually recursive functions.
-- Since each identifier must be defined before it is used,
-- we first give the signatures for both functions and then the equations that define them.

-- # Exercise `o+o≡e` (stretch)
-- Show that the sum of two odd numbers is even.

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (suc zero)    on = suc on
o+o≡e (suc (suc x)) on = suc (suc (o+o≡e x on))

-- ? por qué no funcionan?

-- o+o≡e′ : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
-- o+o≡e′ (suc x) (suc y) = suc (suc (e+e≡e x y))

-- o+o≡e′′ : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
-- o+o≡e′′ om (suc y) = suc (o+e≡o om y)

-- ? suc _n_310 != n + suc n₁ of type ℕ
-- ? when checking that the inferred type of an application
-- ?   odd (suc _n_310)
-- ? matches the expected type
-- ?   odd (n + suc n₁)

-- # Exercise `Bin-predicates` (stretch)

-- Recall that Exercise Bin defines a datatype Bin of bitstrings representing natural numbers.
-- Representations are not unique due to leading zeros.
-- Define a predicate over all bitstrings that holds if the bitstring is canonical
--   Can : Bin → Set
--   One : Bin → Set (auxiliar, holds only if the bistring has a leading one)

data One : Bin → Set
data Can : Bin → Set

-- TODO definir One sin usar `inc`ya que es una función y no un constructor.
data One where
  bit  : One (⟨⟩ I)
  sucᵇ : ∀ {b : Bin} → One b → One (inc b)
data Can where
  zero : Can (⟨⟩ O)
  bin  : ∀ {b : Bin} → One b → Can b

-- Show that increment preserves canonical bitstrings:
-- Can b → Can (inc b)

inc¹ : ∀ {b : Bin} → One b → One (inc b)
inc¹ ob = sucᵇ ob

incᶜ : ∀ {b : Bin} → Can b → Can (inc b)
incᶜ zero     = bin bit
incᶜ (bin b₁) = bin (inc¹ b₁)


-- Show that converting a natural to a bitstring always yields a canonical bitstring:
--   Can (to n)

toᶜ : ∀ {n : ℕ} → Can (to n)
toᶜ {zero}  = zero
toᶜ {suc n} = incᶜ (toᶜ {n})


-- Show that converting a canonical bitstring to a natural and back is the identity:
--   Can b → to (from b) ≡ b
-- (Hint: For each of these, you may first need to prove related properties of One.
-- Also, you may need to prove that if One b then 1 is less or equal to the result of from b.)

-- TODO lo pide el ejercicio pero no lo necesité (?)
-- lema : ∀ {b : Bin} → One b → 1 ≤ from b
-- lema bit = s≤s z≤n
-- lema (sucᵇ ob) = {!   !}

_<< : ∀ {b : Bin} → One b → Bin
_<< {b} _ = b

-- !! Estoy seguro que estoy "haciendo trampa"
cast¹ : ∀ {b : Bin} → One b → to (from b) ≡ b 
cast¹ bit = refl                  -- (⟨⟩ I) ≡ (⟨⟩ I)
cast¹ (sucᵇ ob) with ob <<
... | b = 
  begin
    to (from (inc b))
  ≡⟨ cong to (law₁ b) ⟩
    to (suc (from b))
  ≡⟨ refl ⟩
    inc (to (from b))
  ≡⟨ cong inc (cast¹ ob) ⟩
    inc b
  ∎
-- ?0 : to (from (inc b)) ≡ inc b
--          to (from (inc b)) ≡ inc b
--  <law′>≡ to (suc (from b)) ≡ inc b
--    <to>≡ inc (to (from b)) ≡ inc b
-- <cast¹>≡ inc b ≡ inc b

castᶜ : ∀ {b : Bin} → Can b → to (from b) ≡ b 
castᶜ zero    = refl
castᶜ (bin x) = cast¹ x