/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini

-/
module

public import RequestProject.TypedTriangle.VortexHingeRelativeTail
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! The polynomial family of parent-root tests fits the relative sampling
budget at exponent `c * sqrt n` for all sufficiently large parent hosts. -/

open Classical

noncomputable section

namespace TypedTriangle.RawReference

theorem anchored_polynomial_test_budget (c : ℝ) (hc : 0 < c) :
    ∃ N : ℝ, ∀ n : ℕ, N ≤ n →
      ((n : ℝ)^3 + (n : ℝ)^4 + 2) *
        Real.exp (-(c * Real.sqrt n)) < 1 := by
  obtain ⟨N, hN⟩ := polynomial_sqrt_budget 5 c hc
  refine ⟨max N 2, ?_⟩
  intro n hn
  have hnN : N ≤ (n : ℝ) := (le_max_left N 2).trans hn
  have hn2 : (2 : ℝ) ≤ n := (le_max_right N 2).trans hn
  have hx0 : (0 : ℝ) ≤ n := by linarith
  have hx : (0 : ℝ) ≤ (n : ℝ)^2 - n - 1 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hpow : (0 : ℝ) ≤ (n : ℝ)^3 := pow_nonneg hx0 _
  have hmul := mul_nonneg hpow hx
  have hpoly : (n : ℝ)^3 + (n : ℝ)^4 + 2 ≤ (n : ℝ)^5 + 2 := by
    nlinarith [hmul]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hpoly (le_of_lt (Real.exp_pos _)))
    (by simpa only [neg_mul] using hN n hnN)

theorem anchored_root_test_budget (c : ℝ) (hc : 0 < c) :
    ∃ N : ℝ, ∀ (V : Type*) (inst : Fintype V),
      letI : Fintype V := inst
      N ≤ (Fintype.card V : ℝ) →
      (Fintype.card ((V × V × V) ⊕ (V × V × V × V)) + 2 : ℝ) *
        Real.exp (-(c * Real.sqrt (Fintype.card V))) < 1 := by
  obtain ⟨N, hN⟩ := anchored_polynomial_test_budget c hc
  refine ⟨N, ?_⟩
  intro V inst
  letI : Fintype V := inst
  intro hcard
  have hcount :
      (Fintype.card ((V × V × V) ⊕ (V × V × V × V)) : ℝ) =
        (Fintype.card V : ℝ)^3 + (Fintype.card V : ℝ)^4 := by
    simp only [Fintype.card_sum, Fintype.card_prod, Nat.cast_add,
      Nat.cast_mul]
    ring
  rw [hcount]
  exact hN (Fintype.card V) hcard

theorem quarter_tolerance_rate_identity (c x : ℝ) (hx : 0 < x) :
    (c * (Real.sqrt (Real.sqrt x))⁻¹ ^ 2) * x =
      c * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hss : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.2 hs
  have hsq : (Real.sqrt x)^2 = x := Real.sq_sqrt (le_of_lt hx)
  have hssq : (Real.sqrt (Real.sqrt x))^2 = Real.sqrt x :=
    Real.sq_sqrt (le_of_lt hs)
  rw [inv_pow, hssq]
  calc
    c * (Real.sqrt x)⁻¹ * x = c * (Real.sqrt x)⁻¹ * (Real.sqrt x)^2 := by
      rw [hsq]
    _ = c * Real.sqrt x := by
      field_simp [ne_of_gt hs]

#print axioms anchored_polynomial_test_budget
#print axioms anchored_root_test_budget
#print axioms quarter_tolerance_rate_identity

end TypedTriangle.RawReference
