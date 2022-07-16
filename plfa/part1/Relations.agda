import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

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
-- ? ≤-refl {suc n} = s≤s (≤-refl {n})
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
-- ? ≤-antisym-case z≤n (s≤s n≤m) = {!   !}
-- The case for the constructor `s≤s` is impossible
-- because unification ended with a conflicting equation
--   `suc n ≟ zero`
-- ? ≤-antisym-case (s≤s m≤n) z≤n = {!   !}
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

-- g : Nat -> Nat
-- f : m <= n -> g m <= g n
-- map f (forward p)  = forward (f p)
-- map f (flipped p) = flipped (f p)
-- <=-total (suc m) (suc n) = map s<=s (<=-total m n)

-- If both arguments are equal, then both cases hold and we could return evidence of either.
-- In the code above we return the `forward` case,
-- but there is a variant that returns the `flipped` case:
≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                         | forward m≤n  =  forward (s≤s m≤n)
...                         | flipped n≤m  =  flipped (s≤s n≤m)
 