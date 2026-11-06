/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Arithmetic of admissible profiles

* `pair_count_iff` : with `n = a+b+c`, the pair-count identity
  `3·(a(a-1)+b(b-1)+c(c-1)) = n(n-1)` (monochromatic pairs = number of blocks) is
  equivalent to the quadratic identity `a²+b²+c²-ab-ac-bc = n`.
* `two_two_forces_five` : two classes of size `2` force the third to have size `5`
  (so the literal exception is exactly the permutations of `(2,2,5)`).
-/

@[expose] public section

namespace CDRBicolour

/-- The key polynomial identity behind `pair_count_iff`. -/
theorem pair_count_identity (a b c : ℤ) :
    3 * (a * (a - 1) + b * (b - 1) + c * (c - 1)) - (a + b + c) * (a + b + c - 1) =
      2 * ((a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c) - (a + b + c)) := by
  ring

/-- Pair count ⇔ quadratic identity. -/
theorem pair_count_iff (a b c : ℤ) :
    3 * (a * (a - 1) + b * (b - 1) + c * (c - 1)) = (a + b + c) * (a + b + c - 1) ↔
      a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c = a + b + c := by
  have h := pair_count_identity a b c
  constructor <;> intro h' <;> linarith

/-- Two classes of size two force the third to be `5`. -/
theorem two_two_forces_five {c : ℤ} (hc : 0 < c)
    (h : (2 : ℤ) ^ 2 + 2 ^ 2 + c ^ 2 - 2 * 2 - 2 * c - 2 * c = 2 + 2 + c) : c = 5 := by
  have h' : c * (c - 5) = 0 := by linarith
  rcases mul_eq_zero.1 h' with h0 | h5
  · linarith
  · linarith

end CDRBicolour
