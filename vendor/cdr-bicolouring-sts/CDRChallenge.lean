/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Bicolouring Steiner triple systems

* `CDR.bicolourable3_mul`: **Colbourn–Dinitz–Rosa, *Bicoloring Steiner triple systems*,
  Electron. J. Combin. 6 (1999) #R25, Theorem 2.4.** If there is an `(a, b, c)`-bicolourable
  STS(`u`) with `c = max(a, b, c)` and `c ≤ a + b`, and an `(x, y, z)`-bicolourable STS(`v`), then
  there is an `(ax + by + cz, ay + bz + cx, az + bx + cy)`-bicolourable STS(`uv`).
* **Dinitz–Stinson, *A singular direct product for bicolorable Steiner triple systems*,
  Proposition 1.2**: for a bicoloured STS on `v` points with colour classes of sizes `c_k`,
  (1) `3 Σ_k c_k (c_k − 1) = v (v − 1)` (`CDR.IsSTS.three_mul_sum`); (2) no two distinct colour
  classes have size `2` (`CDR.not_two_classes_of_size_two`); (3) with three colour classes, at
  most one class size is odd (`CDR.Bicolourable3.not_two_odd`).

A Steiner triple system on `X` is a family of 3-subsets in which every pair of distinct points
lies in exactly one block; a bicolouring gives every block exactly two colours.
-/

@[expose] public section

namespace CDR

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A Steiner triple system on `X`: blocks of size three, every pair of distinct points in
exactly one block. -/
structure IsSTS (B : Finset (Finset X)) : Prop where
  card_eq : ∀ t ∈ B, #t = 3
  pair : ∀ x y, x ≠ y → ∃! t, t ∈ B ∧ x ∈ t ∧ y ∈ t

/-- `φ` is a bicolouring of the blocks `B`: every block receives exactly two colours. -/
def IsBicolouring {κ : Type*} [DecidableEq κ] (B : Finset (Finset X)) (φ : X → κ) : Prop :=
  ∀ t ∈ B, #(t.image φ) = 2

/-- The colour class of `k`. -/
def colourClass {κ : Type*} [DecidableEq κ] (φ : X → κ) (k : κ) : Finset X :=
  univ.filter fun x => φ x = k

/-- `Bicolourable3 v a b c`: there is an STS on `v` points with a bicolouring by the colours
`0, 1, 2` whose colour classes have sizes `a`, `b`, `c`. -/
def Bicolourable3 (v a b c : ℕ) : Prop :=
  ∃ (B : Finset (Finset (Fin v))) (φ : Fin v → Fin 3), IsSTS B ∧ IsBicolouring B φ ∧
    #(colourClass φ 0) = a ∧ #(colourClass φ 1) = b ∧ #(colourClass φ 2) = c

/-- **Divisibility (Colbourn–Dinitz–Rosa, Proposition 1.4 for STS; Dinitz–Stinson,
Proposition 1.2 (1)).** -/
theorem IsSTS.three_mul_sum {κ : Type*} [Fintype κ] [DecidableEq κ] {B : Finset (Finset X)}
    (hB : IsSTS B) {φ : X → κ} (hφ : IsBicolouring B φ) :
    3 * ∑ k, #(colourClass φ k) * (#(colourClass φ k) - 1) =
      Fintype.card X * (Fintype.card X - 1) := by
  sorry

/-- **Duplicity (Dinitz–Stinson, Proposition 1.2 (2)).** A bicolouring of an STS has no two
distinct colour classes of size `2`. -/
theorem not_two_classes_of_size_two {κ : Type*} [DecidableEq κ] {B : Finset (Finset X)}
    {φ : X → κ} (hB : IsSTS B) (hφ : IsBicolouring B φ) {k l : κ} (hkl : k ≠ l)
    (hk : #(univ.filter fun x => φ x = k) = 2) (hl : #(univ.filter fun x => φ x = l) = 2) :
    False := by
  sorry

/-- **Oddity (Dinitz–Stinson, Proposition 1.2 (3), three classes).** In a `3`-bicoloured STS,
at most one of the class sizes is odd. -/
theorem Bicolourable3.not_two_odd {v a b c : ℕ} (h : Bicolourable3 v a b c) :
    ¬ (Odd a ∧ Odd b) ∧ ¬ (Odd b ∧ Odd c) ∧ ¬ (Odd c ∧ Odd a) := by
  sorry

/-- **Colbourn–Dinitz–Rosa, Theorem 2.4.** -/
theorem bicolourable3_mul {u v a b c x y z : ℕ} (h₁ : Bicolourable3 u a b c)
    (hac : a ≤ c) (hbc : b ≤ c) (hcab : c ≤ a + b) (h₂ : Bicolourable3 v x y z) :
    Bicolourable3 (u * v) (a * x + b * y + c * z) (a * y + b * z + c * x)
      (a * z + b * x + c * y) := by
  sorry

end CDR
