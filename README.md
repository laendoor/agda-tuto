# AGDA Tutorial

> [Programming Language Foundations in Agda](https://plfa.github.io)

## Exercises

### Part 1: Logical Foundations

1. [Naturals](exercises/part1/Naturals): Natural numbers
1. [Induction(exercises/part1/Induction)]: Proof by Induction
1. Relations: Inductive definition of relations
1. Equality: Equality and equational reasoning
1. Isomorphism: Isomorphism and Embedding
1. Connectives: Conjunction, disjunction, and implication
1. Negation: Negation, with intuitionistic and classical logic
1. Quantifiers: Universals and existentials
1. Decidable: Booleans and decision procedures
1. Lists: Lists and higher-order functions

### Part 2: Programming Language Foundations

1. Lambda: Introduction to Lambda Calculus
1. Properties: Progress and Preservation
1. DeBruijn: Intrinsically-typed de Bruijn representation
1. More: Additional constructs of simply-typed lambda calculus
1. Bisimulation: Relating reduction systems
1. Inference: Bidirectional type inference
1. Untyped: Untyped lambda calculus with full normalization
1. Confluence: Confluence of untyped lambda calculus
1. BigStep: Big-step semantics of untyped lambda calculus

### Part 3: Denotational Semantics

1. Denotational: Denotational semantics of untyped lambda calculus
1. Compositional: The denotational semantics is compositional
1. Soundness: Soundness of reduction with respect to denotational semantics
1. Adequacy: Adequacy of denotational semantics with respect to operational semantics
1. ContextualEquivalence: Denotational equality implies contextual equivalence

## Key binds

```txt
C-c C-l       Load
C-c C-f       Forward to next hole
C-c C-c       Cases for variable
C-c C-,       Display information about the hole
C-c C-r       Refine the hole
C-c C-space   Remove the hole
```

## Standard Library

```agda
import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
```

## Unicode Snippets

```txt
ℕ  U+2115  DOUBLE-STRUCK CAPITAL N (\N)
→  U+2192  RIGHTWARDS ARROW (\to, \r, \->)
∸  U+2238  DOT MINUS (\.-)
≡  U+2261  IDENTICAL TO (\==)
⟨  U+27E8  MATHEMATICAL LEFT ANGLE BRACKET (\<)
⟩  U+27E9  MATHEMATICAL RIGHT ANGLE BRACKET (\>)
∎  U+220E  END OF PROOF (\qed)
```
