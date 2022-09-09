import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-distrib-+)
open import plfa.part1.Induction using (*-distrib-+ʳ; *-distrib-+ˡ)

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
-- // Show that strict inequality is transitive

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans z<s       (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- # Exercise trichotomy (practice)
-- // Show that strict inequality satisfies a weak version of trichotomy,
-- // in the sense that for any `m` and `n` that one of the following holds: * `m < n`, * `m ≡ n`, or * `m > n`.
-- // Define `m > n` to be the same as `n < m`.
-- // You will need a suitable data declaration, similar to that used for totality.
-- // (We will show that the three cases are exclusive after we introduce negation)

infix 4 _>_
data _>_ : ℕ → ℕ → Set where
  s>z : ∀ {n   : ℕ}         → suc n > zero
  s>s : ∀ {n m : ℕ} → n > m → suc n > suc m

-- todo reescribir así
_>1_ : ℕ → ℕ → Set
_>1_ m n = n < m

data Trichotomy (m n : ℕ) : Set where
  equal   : m ≡ n → Trichotomy m n
  lesser  : m < n → Trichotomy m n
  greater : m > n → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero    zero    = equal refl
<-trichotomy zero    (suc n) = lesser z<s
<-trichotomy (suc m) zero    = greater s>z
<-trichotomy (suc m) (suc n)
  with <-trichotomy m n 
...       | equal   m≡n = equal (cong suc m≡n)
...       | lesser  m<n = lesser (s<s m<n)
...       | greater m>n = greater (s>s m>n)


-- # Exercise +-mono-< (practice)
-- // Show that addition is monotonic with respect to strict inequality.
-- // As with inequality, some additional definitions may be required.

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
-- // Show that `suc m ≤ n` implies `m < n`, and conversely.

-- ^ 1st: show `suc m ≤ n → m < n`
≤-iff-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤-iff-< {zero}  {suc n} 1≤n₁ = z<s
≤-iff-< {suc m} {suc n} (s≤s m₁≤n) = s<s (≤-iff-< m₁≤n)

-- ^ 2nd: show `m < n → suc m ≤ n`
<-iff-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<-iff-≤ {zero}  {suc n} 0<n₁  = s≤s z≤n
<-iff-≤ {suc m} {suc n} (s<s m<n) = s≤s (<-iff-≤ m<n)

-- # Exercise <-trans-revisited (practice)
-- // Give an alternative proof that strict inequality is transitive,
-- // using the relation between strict inequality and inequality
-- // and the fact that inequality is transitive.

-- ≤-iff-< : ∀ {m n : ℕ} → suc m ≤ n → m < n
-- <-iff-≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n

<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited m<n n<p = ≤-iff-< {!   !}
    -- suc m ≤ p
-- m < n → suc m ≤ n
-- n ≤ suc n
-- n < p → suc n ≤ p
-- suc m ≤ p → m < p


-- <-trans-revisited {m} {n} {p} m<n n<p
--   with <-iff-≤ m<n      | <-iff-≤ n<p
-- ... | s≤s {m} {n₁} m≤n₁ | s≤s {n2} {p2} n₁≤p = ≤-iff-< {!   !}