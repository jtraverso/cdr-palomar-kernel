/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexLossBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Arithmetic of the global robustness-radius schedule. These estimates
do not construct the adaptive samples or the schedule itself. -/

open Finset

namespace TypedTriangle.Vortex

/-- Geometrically shrinking earlier radii cost at most twice the current
radius, independently of the number of levels. -/
theorem geometric_radius_sum (β : ℕ → ℝ)
    (hβ : ∀ j, 0 ≤ β j) (hstep : ∀ j, β j ≤ β (j + 1) / 2)
    (L : ℕ) :
    ∑ j ∈ range (L + 1), β j ≤ 2 * β L := by
  induction L with
  | zero => simp; linarith [hβ 0]
  | succ L ih =>
    rw [sum_range_succ]
    linarith [hstep L]

/-- Earlier robustness extractions fit in the preparation window at the
current global index. This is the quantitative implication of (2.1). -/
theorem earlier_radii_within_window (β ε : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (L r : ℕ) (hr : r ≤ L) (hε : 0 ≤ ε r)
    (hcross : ∀ j < r,
      β j ≤ ε r / (16 * b * (L + 1))) :
    2 * b * (∑ j ∈ range r, β j) ≤ ε r / 8 := by
  have hsum : (∑ j ∈ range r, β j) ≤
      ∑ _j ∈ range r, ε r / (16 * b * (L + 1)) := by
    apply sum_le_sum
    intro j hj
    exact hcross j (mem_range.mp hj)
  have hden : 0 < 16 * b * (L + 1 : ℝ) := by positivity
  simp only [sum_const, card_range, nsmul_eq_mul] at hsum
  have hrR : (r : ℝ) ≤ L + 1 := by exact_mod_cast (Nat.le_succ_of_le hr)
  have hratio : (r : ℝ) * (ε r / (16 * b * (L + 1))) ≤
      ε r / (16 * b) := by
    have hfrac : 0 ≤ ε r / (16 * b * (L + 1)) :=
      div_nonneg hε hden.le
    calc
      (r : ℝ) * (ε r / (16 * b * (L + 1)))
          ≤ (L + 1) * (ε r / (16 * b * (L + 1))) :=
            mul_le_mul_of_nonneg_right hrR hfrac
      _ = ε r / (16 * b) := by
        field_simp
  have hbound := hsum.trans hratio
  have hscaled := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 2 * b)
  have heq : 2 * b * (ε r / (16 * b)) = ε r / 8 := by field_simp; ring
  rw [heq] at hscaled
  exact hscaled

#print axioms geometric_radius_sum
#print axioms earlier_radii_within_window

end TypedTriangle.Vortex
