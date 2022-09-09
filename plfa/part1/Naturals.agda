{-# OPTIONS --exact-split #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- # Naturals: Natural numbers
module plfa.part1.Naturals where

-- # The naturals are an inductive datatype
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- # Exercise `seven` (practice)
-- // Write out 7 in longhand.

one   = suc zero
two   = suc one
three = suc two
four  = suc three
five  = suc four
six   = suc five

seven : ℕ
seven = suc six

-- # Operations on naturals are recursive functions

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

-- // For example, let's add two and three:
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

-- // We can write the same derivation more compactly by only expanding shorthand as needed:
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

-- // In fact, both proofs are longer than need be, and Agda is satisfied with the following:
_ : 2 + 3 ≡ 5
_ = refl

-- # Exercise `+-example` (practice)
-- // Compute 3 + 4
-- // writing out your reasoning as a chain of equations,
-- // using the equations for +.

-- shorter
_ = 3 + 4 ≡ 7

-- reasoning
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc 6
  ≡⟨⟩
    7
  ∎

-- # Multiplication
-- // Once we have defined addition, we can define multiplication as repeated addition:

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

-- // For example, let's multiply two and three:
_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

-- # Exercise `*-example` (practice)
-- // Compute 3 * 4,
-- // writing out your reasoning as a chain of equations,
-- // using the equations for *. (You do not need to step through the evaluation of +.)

-- shorter
_ = 3 * 4 ≡ 12

-- reasoning
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

-- # Exercise _^_ (recommended)
-- // Define exponentiation, which is given by the following equations:
-- m ^ 0        =  1
-- m ^ (1 + n)  =  m * (m ^ n)

_^_ : ℕ → ℕ → ℕ
n ^ zero    = suc zero
n ^ (suc m) = n * (n ^ m)

-- // Check that 3 ^ 4 is 81.

-- // shorter
_ = 3 ^ 4 ≡ 81

-- // reasoning
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 ^ (suc 3)
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * 27
  ≡⟨⟩
    81
  ∎

-- # Monus

-- // Monus is our first use of a definition that uses pattern matching against both arguments:

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

-- // For example, let's subtract two from three:
_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

-- We did not use the second equation at all, but it will be required
-- if we try to subtract a larger number from a smaller one:
_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

-- # Exercise `∸-example₁` and `∸-example₂` (recommended)
-- // Compute `5 ∸ 3` and `3 ∸ 5`,
-- // writing out your reasoning as a chain of equations.

_ = 5 ∸ 3 ≡ 2
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

_ = 3 ∸ 5 ≡ 0
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

-- # Precedence

-- // In Agda the precedence and associativity of infix operators needs to be declared:
infixl 6  _+_  _∸_
infixl 7  _*_

-- # Exercise Bin (stretch)
-- // A more efficient representation of natural numbers uses a binary rather than a unary system.
-- // We represent a number as a bitstring:

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
