/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexPaidSameSampleExactSeed
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

/-! The variable-radius schedule may be fixed on the sampled core before
the sample is selected. Its inverse budget is stronger than the later ambient
profile budget because the sampled core has at most the ambient order. -/

/-- A finite family of reference tolerances can be fixed before the sample.
The sampled precision is then chosen below every one of them and below the
precision already budgeted by the variable-radius preparation. -/
theorem exists_sample_precision_for_finite_references
    (L : ℕ) (ξSchedule : ℝ) (εRef : Fin (L + 1) → ℝ)
    (hξ : 0 < ξSchedule) (hRef : ∀ j, 0 < εRef j) :
    ∃ ξSample : ℝ, 0 < ξSample ∧ ξSample ≤ ξSchedule ∧
      ∀ j, ξSample ≤ εRef j / 2 := by
  let s : Finset ℝ := (univ : Finset (Fin (L + 1))).image εRef
  have hs : s.Nonempty := by simp [s]
  let εmin := s.min' hs
  have hεmin : 0 < εmin := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.min'_mem s hs)
    have h := hRef j
    rw [hj] at h
    exact h
  let ξSample := min ξSchedule (εmin / 2)
  refine ⟨ξSample, lt_min hξ (by positivity), min_le_left _ _, ?_⟩
  intro j
  exact (min_le_right _ _).trans (div_le_div_of_nonneg_right
    (Finset.min'_le s (εRef j)
      (Finset.mem_image.mpr ⟨j, mem_univ j, rfl⟩))
    (by norm_num))

theorem scheduled_sample_budget_transfers_to_ambient
    (C q K ξSample ξSchedule nWindow nAmbient : ℝ) (a : ℕ)
    (hC : 1 ≤ C) (hq : 0 < q) (hK : 0 ≤ K)
    (hnWindow : 0 < nWindow) (hWindow : nWindow ≤ nAmbient)
    (hξ : ξSample ≤ ξSchedule)
    (hSchedule : K * (ξSchedule + (a : ℝ) * (2 * C) /
      (q * nWindow)) ≤ 1 / (8 * C)) :
    K * (ξSample + (a : ℝ) * C / (q * nAmbient)) ≤
      1 / (8 * C) := by
  have hC0 : 0 ≤ C := by linarith
  have hnAmbient : 0 < nAmbient := lt_of_lt_of_le hnWindow hWindow
  have hAC : 0 ≤ (a : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC0
  have hScale : (a : ℝ) * C * nWindow ≤
      (a : ℝ) * C * (2 * nAmbient) :=
    mul_le_mul_of_nonneg_left (by linarith : nWindow ≤ 2 * nAmbient) hAC
  have hQScale := mul_le_mul_of_nonneg_left hScale hq.le
  have hDen : (a : ℝ) * C / (q * nAmbient) ≤
      (a : ℝ) * (2 * C) / (q * nWindow) := by
    apply (div_le_div_iff₀ (mul_pos hq hnAmbient)
      (mul_pos hq hnWindow)).2
    nlinarith [hQScale]
  have hErr : ξSample + (a : ℝ) * C / (q * nAmbient) ≤
      ξSchedule + (a : ℝ) * (2 * C) / (q * nWindow) :=
    add_le_add hξ hDen
  exact (mul_le_mul_of_nonneg_left hErr hK).trans hSchedule

theorem scheduled_sample_budget_with_paid_holes
    (C q K ξSample ξSchedule nWindow nAmbient η : ℝ)
    (a d : ℕ) (hC : 1 ≤ C) (hq : 0 < q) (hK : 0 ≤ K)
    (hnWindow : 0 < nWindow) (hWindow : nWindow ≤ nAmbient)
    (hξ : ξSample ≤ ξSchedule)
    (hSchedule : K * (ξSchedule + (a : ℝ) * (2 * C) /
      (q * nWindow)) ≤ 1 / (8 * C))
    (hd : (d : ℝ) ≤ η * nAmbient)
    (hHoles : K * (4 * C * η) ≤ 1 / (8 * C)) :
    K * (ξSample + (a : ℝ) * C / (q * nAmbient) +
      4 * C * d / nAmbient) ≤ 1 / (4 * C) := by
  have hnAmbient : 0 < nAmbient := lt_of_lt_of_le hnWindow hWindow
  have hSample := scheduled_sample_budget_transfers_to_ambient
    C q K ξSample ξSchedule nWindow nAmbient a
    hC hq hK hnWindow hWindow hξ hSchedule
  have hHoleTerm : 4 * C * (d : ℝ) / nAmbient ≤ 4 * C * η := by
    apply (div_le_iff₀ hnAmbient).2
    have hC4 : 0 ≤ 4 * C := by linarith
    have hScale := mul_le_mul_of_nonneg_left hd hC4
    nlinarith [hScale]
  have hHoleScaled := mul_le_mul_of_nonneg_left hHoleTerm hK
  calc
    K * (ξSample + (a : ℝ) * C / (q * nAmbient) +
        4 * C * d / nAmbient) =
        K * (ξSample + (a : ℝ) * C / (q * nAmbient)) +
          K * (4 * C * d / nAmbient) := by ring
    _ ≤ 1 / (8 * C) + 1 / (8 * C) :=
      add_le_add hSample (hHoleScaled.trans hHoles)
    _ = 1 / (4 * C) := by ring

#print axioms scheduled_sample_budget_transfers_to_ambient
#print axioms scheduled_sample_budget_with_paid_holes
#print axioms exists_sample_precision_for_finite_references

end TypedTriangle.Vortex
