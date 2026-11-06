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
noncomputable section
namespace Pseudorandom.Explicit

/-- A specified cutoff for `A ≤ x^c`, including nonpositive A. -/
def powerCut (c A : ℝ) : ℝ := max 1 ((max A 0) ^ c⁻¹)

theorem powerCut_one (c A : ℝ) : 1 ≤ powerCut c A := le_max_left _ _

theorem const_le_rpow {c A x : ℝ} (hc : 0 < c) (hx : powerCut c A ≤ x) :
    A ≤ x ^ c := by
  have hx1 : 1 ≤ x := (powerCut_one c A).trans hx
  have hs : (max A 0) ^ c⁻¹ ≤ x := (le_max_right _ _).trans hx
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ (max A 0) ^ c⁻¹) hs hc.le
  rw [Real.rpow_inv_rpow (le_max_right A 0) hc.ne'] at h
  exact (le_max_left A 0).trans h

def logCut (c A : ℝ) : ℝ := powerCut (c/2) (2 * max A 0 / c)

theorem mul_log_le_rpow {c A x : ℝ} (hc : 0 < c) (hx : logCut c A ≤ x) :
    A * Real.log x ≤ x ^ c := by
  have hx1 : 1 ≤ x := (powerCut_one _ _).trans hx
  have hx0 : 0 < x := by linarith
  have ha : 0 ≤ max A 0 := le_max_right _ _
  have hBound : 2 * max A 0 / c ≤ x ^ (c/2) :=
    const_le_rpow (by positivity) hx
  calc
    A * Real.log x ≤ max A 0 * Real.log x :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg hx1)
    _ ≤ max A 0 * (x ^ (c/2) / (c/2)) :=
      mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx0.le (by positivity)) ha
    _ = (2 * max A 0 / c) * x ^ (c/2) := by ring
    _ ≤ x ^ (c/2) * x ^ (c/2) :=
      mul_le_mul_of_nonneg_right hBound (Real.rpow_nonneg hx0.le _)
    _ = x ^ c := by rw [← Real.rpow_add hx0]; congr 1 <;> ring

theorem mul_rpow_le_rpow {u v A x : ℝ} (huv : u < v)
    (hx : powerCut (v-u) A ≤ x) : A * x ^ u ≤ x ^ v := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one ((powerCut_one _ _).trans hx)
  have h := const_le_rpow (sub_pos.mpr huv) hx
  calc
    A * x ^ u ≤ x ^ (v-u) * x ^ u :=
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hx0.le _)
    _ = x ^ v := by rw [← Real.rpow_add hx0]; congr 1 <;> ring

theorem rpow_le_mul_rpow {u v A x : ℝ} (huv : u < v) (hA : 0 < A)
    (hx : powerCut (v-u) (1/A) ≤ x) : x ^ u ≤ A * x ^ v := by
  have h := mul_rpow_le_rpow huv hx
  have hs := mul_le_mul_of_nonneg_left h hA.le
  calc
    x ^ u = A * ((1/A) * x ^ u) := by field_simp
    _ ≤ A * x ^ v := hs

#print axioms const_le_rpow
#print axioms mul_log_le_rpow
#print axioms mul_rpow_le_rpow
#print axioms rpow_le_mul_rpow
end Pseudorandom.Explicit
