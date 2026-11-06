/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini

-/
module

public import RequestProject.TypedTriangle.VortexAnchoredRelativeTail
public import RequestProject.TypedTriangle.VortexAnchoredBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! The per-layer relative sampling precision has a uniform choice of
constants. The host order is quantified after the rate constant. -/

open Classical

noncomputable section

namespace TypedTriangle.RawReference

theorem exists_anchored_sampling_parameters
    (α q : ℝ) (h : ℕ) (hα : 0 < α) (hq : 0 < q) :
    ∃ c N : ℝ, 0 < c ∧
      ∀ n : ℕ, N ≤ n →
        let η : ℝ := (Real.sqrt (Real.sqrt n))⁻¹
        let θ : ℝ := c * η ^ 2
        0 < η ∧ η ≤ 1 ∧
        θ ≤ η ^ 2 * q ^ 2 / 4 ∧
        θ ≤ η ^ 2 * α ^ 2 * q ^ 2 / 4 ∧
        (∀ i, 6 ≤ i → i ≤ h →
          θ ≤ η ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) /
            (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ))) ∧
        ((n : ℝ)^3 + (n : ℝ)^4 + 2) *
          Real.exp (-(θ * n)) < 1 := by
  obtain ⟨c, hc, hcsize, hcpool, hchinge⟩ :=
    exists_common_relative_rate α q h hα hq
  obtain ⟨N, hN⟩ := anchored_polynomial_test_budget c hc
  refine ⟨c, max N 1, hc, ?_⟩
  intro n hn
  have hnN : N ≤ (n : ℝ) := (le_max_left N 1).trans hn
  have hn1 : (1 : ℝ) ≤ n := (le_max_right N 1).trans hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := by
    simpa using (Real.sqrt_le_sqrt hn1)
  have hss1 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt n) := by
    simpa using (Real.sqrt_le_sqrt hs1)
  dsimp
  have hηpos : 0 < (Real.sqrt (Real.sqrt n))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.2 (Real.sqrt_pos.2 hnpos))
  have hηle : (Real.sqrt (Real.sqrt n))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hss1
  have hηsq : 0 ≤ ((Real.sqrt (Real.sqrt n))⁻¹)^2 := sq_nonneg _
  refine ⟨hηpos, hηle, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hcsize hηsq]
  · nlinarith [mul_le_mul_of_nonneg_right hcpool hηsq]
  · intro i hi6 hih
    calc
      c * (Real.sqrt (Real.sqrt n))⁻¹ ^ 2 ≤
          (α ^ 2 * q ^ (2 * (i - 4)) /
            (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ))) *
            (Real.sqrt (Real.sqrt n))⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right (hchinge i hi6 hih) hηsq
      _ = (Real.sqrt (Real.sqrt n))⁻¹ ^ 2 * α ^ 2 * q ^ (2 * (i - 4)) /
            (4 * ((2 : ℝ) ^ (i.choose 2)) ^ 2 * ((i - 4 : ℕ) : ℝ)) := by ring
  · have hbudget := hN n hnN
    have hid := quarter_tolerance_rate_identity c n hnpos
    simpa only [hid, neg_mul] using hbudget

#print axioms exists_anchored_sampling_parameters

end TypedTriangle.RawReference
