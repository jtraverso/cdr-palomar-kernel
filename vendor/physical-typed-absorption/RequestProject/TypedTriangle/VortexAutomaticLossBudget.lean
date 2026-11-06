/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The automatic fourth-root error is summable on geometrically shrinking
orders. These arithmetic lemmas do not construct paid layers or preserve
the hinge condition under their edge payments. -/

open Finset
noncomputable section

namespace TypedTriangle.Vortex

def automaticRelativeError (n : ℝ) : ℝ := (Real.sqrt (Real.sqrt n))⁻¹

theorem automaticRelativeError_nonneg (n : ℝ) :
    0 ≤ automaticRelativeError n := by
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- A factor-sixteen decrease of order at least doubles the automatic error. -/
theorem automaticRelativeError_contract (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxy : 16 * y ≤ x) :
    automaticRelativeError x ≤ automaticRelativeError y / 2 := by
  have hfirst : 4 * Real.sqrt y ≤ Real.sqrt x := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg x)).mp
    nlinarith [Real.sq_sqrt hy.le, Real.sq_sqrt hx.le]
  have hsecond : 2 * Real.sqrt (Real.sqrt y) ≤ Real.sqrt (Real.sqrt x) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg y),
      Real.sq_sqrt (Real.sqrt_nonneg x)]
  have hyroot : 0 < Real.sqrt (Real.sqrt y) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hy)
  have hInv := one_div_le_one_div_of_le (by positivity :
    0 < 2 * Real.sqrt (Real.sqrt y)) hsecond
  dsimp [automaticRelativeError]
  convert hInv using 1 <;> field_simp

/-- The total automatic sampling error is bounded independently of depth. -/
theorem sum_automaticRelativeError_le_last
    (order : ℕ → ℝ) (k : ℕ)
    (hpos : ∀ i ≤ k, 0 < order i)
    (hstep : ∀ i < k, 16 * order (i + 1) ≤ order i) :
    (∑ i ∈ range (k + 1), automaticRelativeError (order i)) ≤
      2 * automaticRelativeError (order k) := by
  induction k with
  | zero =>
      simpa only [Nat.zero_add, sum_range_one] using
        (show automaticRelativeError (order 0) ≤
          2 * automaticRelativeError (order 0) by
          linarith [automaticRelativeError_nonneg (order 0)])
  | succ k ih =>
      have hprev := ih (by intro i hi; exact hpos i (by omega))
        (by intro i hi; exact hstep i (by omega))
      have hlast := automaticRelativeError_contract (order k) (order (k + 1))
        (hpos k (by omega)) (hpos (k + 1) (by omega)) (hstep k (by omega))
      rw [sum_range_succ]
      linarith

/-- Choosing the last admissible order before the host pays every earlier
sampling loss, even when the number of levels depends on the host order. -/
theorem automatic_geometry_loss_budget
    (order : ℕ → ℝ) (k h : ℕ)
    (hpos : ∀ i ≤ k, 0 < order i)
    (hstep : ∀ i < k, 16 * order (i + 1) ≤ order i)
    (hlast : 4 * ((h : ℝ) + 1) * automaticRelativeError (order k) ≤ 1) :
    (∑ i ∈ range (k + 1),
      ((h : ℝ) + 1) * automaticRelativeError (order i)) ≤ 1 / 2 := by
  rw [← mul_sum]
  have hsum := sum_automaticRelativeError_le_last order k hpos hstep
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ (h : ℝ) + 1)
  nlinarith

theorem automaticRelativeError_le_of_power_bound (B n : ℝ)
    (hB : 0 < B) (hn : B ^ 4 ≤ n) :
    automaticRelativeError n ≤ B⁻¹ := by
  have hn0 : 0 ≤ n := (pow_nonneg hB.le _).trans hn
  have hfirst : B ^ 2 ≤ Real.sqrt n := by
    apply (sq_le_sq₀ (sq_nonneg B) (Real.sqrt_nonneg n)).mp
    nlinarith [Real.sq_sqrt hn0]
  have hsecond : B ≤ Real.sqrt (Real.sqrt n) := by
    apply (sq_le_sq₀ hB.le (Real.sqrt_nonneg _)).mp
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg n)]
  have hInv := one_div_le_one_div_of_le hB hsecond
  simpa only [automaticRelativeError, one_div] using hInv

/-- The explicit last-order threshold depends on the fixed hinge order,
not on the depth or the original host order. -/
theorem automatic_geometry_loss_budget_of_terminal_threshold
    (order : ℕ → ℝ) (k h : ℕ)
    (hpos : ∀ i ≤ k, 0 < order i)
    (hstep : ∀ i < k, 16 * order (i + 1) ≤ order i)
    (hlast : (4 * ((h : ℝ) + 1)) ^ 4 ≤ order k) :
    (∑ i ∈ range (k + 1),
      ((h : ℝ) + 1) * automaticRelativeError (order i)) ≤ 1 / 2 := by
  have hB : 0 < 4 * ((h : ℝ) + 1) := by positivity
  have hErr := automaticRelativeError_le_of_power_bound
    (4 * ((h : ℝ) + 1)) (order k) hB hlast
  apply automatic_geometry_loss_budget order k h hpos hstep
  calc
    4 * ((h : ℝ) + 1) * automaticRelativeError (order k) ≤
        (4 * ((h : ℝ) + 1)) * (4 * ((h : ℝ) + 1))⁻¹ :=
      mul_le_mul_of_nonneg_left hErr hB.le
    _ = 1 := mul_inv_cancel₀ hB.ne'

#print axioms automaticRelativeError_contract
#print axioms sum_automaticRelativeError_le_last
#print axioms automatic_geometry_loss_budget
#print axioms automaticRelativeError_le_of_power_bound
#print axioms automatic_geometry_loss_budget_of_terminal_threshold

end TypedTriangle.Vortex
