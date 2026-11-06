/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Basic
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Tactic.Ring

/-!
# Steiner triple systems with a strict 3-bicolouring (statement layer)

Faithful statement layer for the Colbourn–Dinitz–Rosa bicolouring problem
(Electron. J. Combin. 6 (1999) R25), as reiterated by Dinitz–Stinson (Conjecture 1.4).

* `STS V` : a family of 3-subsets of a finite type such that every pair of distinct
  points lies in exactly one block.
* `IsStrictBicolouring` : a map to three colours under which EVERY block sees exactly
  two colours (no monochromatic and no rainbow block).
* `AdmissibleProfile a b c` : the arithmetic hypotheses of the target theorem, with the
  published exception written literally as "no two classes of size 2".
* `CDRConjecture` : every admissible profile is realised.

Nothing in this file is proved about existence; it only fixes the statements.
-/

@[expose] public section

namespace CDRBicolour

/-- A Steiner triple system on `V`: 3-element blocks, every pair of distinct points in
exactly one block. -/
structure STS (V : Type*) [DecidableEq V] where
  blocks : Finset (Finset V)
  card_eq_three : ∀ B ∈ blocks, B.card = 3
  existsUnique_block : ∀ x y : V, x ≠ y → ∃! B, B ∈ blocks ∧ x ∈ B ∧ y ∈ B

variable {V : Type*} [DecidableEq V]

/-- Every block meets exactly two colour classes. -/
def IsStrictBicolouring (S : STS V) (col : V → Fin 3) : Prop :=
  ∀ B ∈ S.blocks, (B.image col).card = 2

/-- Size of the colour class `i`. -/
def classSize [Fintype V] (col : V → Fin 3) (i : Fin 3) : ℕ :=
  (Finset.univ.filter fun v => col v = i).card

/-- The arithmetic hypotheses on a prescribed profile `(a,b,c)`:
positivity, `n ≡ 1,3 (mod 6)`, the pair-count identity in its quadratic form, and the
published exception (no two classes of size `2`). -/
def AdmissibleProfile (a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧
  ((a + b + c) % 6 = 1 ∨ (a + b + c) % 6 = 3) ∧
  ((a : ℤ) ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c = a + b + c) ∧
  ¬ (a = 2 ∧ b = 2) ∧ ¬ (a = 2 ∧ c = 2) ∧ ¬ (b = 2 ∧ c = 2)

/-- `(a,b,c)` is realised: a strictly bicoloured STS of order `a+b+c` with class sizes
exactly `a`, `b`, `c`. -/
def Realises (a b c : ℕ) : Prop :=
  ∃ (S : STS (Fin (a + b + c))) (col : Fin (a + b + c) → Fin 3),
    IsStrictBicolouring S col ∧
      classSize col 0 = a ∧ classSize col 1 = b ∧ classSize col 2 = c

/-- Target statement (sufficiency direction of the CDR problem). -/
def CDRConjecture : Prop :=
  ∀ a b c : ℕ, AdmissibleProfile a b c → Realises a b c

end CDRBicolour
