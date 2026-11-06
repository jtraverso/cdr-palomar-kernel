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
namespace TypedTriangle.ExplicitSample

theorem nat_succ_le_two_pow (j : ℕ) : j+1 ≤ 2^j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ]
    omega

theorem nat_mul_succ_le_two_pow (j : ℕ) : j*(j+1) ≤ 2^(j+1) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    by_cases hj : j ≤ 1
    · interval_cases j <;> norm_num
    · have hj2 : 2 ≤ j := by omega
      calc
        (j+1)*(j+1+1) ≤ 2*(j*(j+1)) := by nlinarith
        _ ≤ 2*2^(j+1) := Nat.mul_le_mul_left _ ih
        _ = 2^(j+1+1) := by rw [pow_succ]; omega

theorem dyadic_le_inv (j : ℕ) : ((1:ℝ)/2)^j ≤ 1/((j:ℝ)+1) := by
  have hj : (j:ℝ)+1 ≤ (2:ℝ)^j := by exact_mod_cast nat_succ_le_two_pow j
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) hj

theorem weighted_dyadic_le_inv (j : ℕ) :
    (j:ℝ)*((1:ℝ)/2)^j ≤ 2/((j:ℝ)+1) := by
  have hj : (j:ℝ)*((j:ℝ)+1) ≤ 2*(2:ℝ)^j := by
    have h : j*(j+1) ≤ 2*2^j := by
      simpa only [pow_succ, Nat.mul_comm] using nat_mul_succ_le_two_pow j
    exact_mod_cast h
  rw [one_div_pow,mul_one_div]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr hj

#print axioms dyadic_le_inv
#print axioms weighted_dyadic_le_inv
end TypedTriangle.ExplicitSample
