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
namespace TypedTriangle.Vortex

theorem explicit_child_hole_window (C K ηMax : ℝ)
    (hC : 1 ≤ C) (hK : 0 < K) (hηMax : 0 < ηMax) (hDom : 1 ≤ K * ηMax) :
    0 < 1 / (128 * C * C * K) ∧
    1 / (128 * C * C * K) ≤ ηMax ∧
    K * (8 * C * (1 / (128 * C * C * K))) = 1 / (16 * C) := by
  have hCpos : 0 < C := by linarith
  have hScale : K ≤ 128 * C * C * K := by
    have hc : (1 : ℝ) ≤ 128 * C * C := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hK.le
  have hRecip : 1 / (128 * C * C * K) ≤ 1 / K :=
    one_div_le_one_div_of_le hK hScale
  have hCap : 1 / K ≤ ηMax := (div_le_iff₀ hK).2 (by nlinarith [hDom])
  refine ⟨by positivity, hRecip.trans hCap, ?_⟩
  field_simp
  ring

/-- The first-entry deletion is a strict fraction of the explicit child
hole window; the dense reference can be selected afterward. -/
theorem amplified_schedule_pays_explicit_child_hole
    (C K q ξ w w' a : ℝ) (hC : 1 ≤ C) (hK : 0 < K)
    (hq : 0 < q) (hq1 : q ≤ 1) (hξ : 0 ≤ ξ)
    (hw : 0 < w) (hhalf : w / 2 ≤ w') (ha : 0 ≤ a)
    (hBudget : K * (ξ + a * (32 * C) / (q * w)) ≤ 1 / (128 * C)) :
    a / w' ≤ (1 / (128 * C * C * K)) / 16 ∧
    ∀ ηRef : ℝ, ηRef ≤ (1 / (128 * C * C * K)) / 4 →
      (ηRef * w + a) / w' ≤ 1 / (128 * C * C * K) := by
  have hCpos : 0 < C := by linarith
  have hqW : 0 < q * w := mul_pos hq hw
  have hw' : 0 < w' := lt_of_lt_of_le (by linarith : 0 < w / 2) hhalf
  have hTerm : K * (a * (32 * C) / (q * w)) ≤ 1 / (128 * C) := by
    nlinarith [mul_nonneg hK.le hξ]
  have hClear := (le_div_iff₀ (by positivity : 0 < 128 * C)).mp hTerm
  have hClear' := mul_le_mul_of_nonneg_right hClear hqW.le
  have hId : K * (a * (32 * C) / (q * w)) * (128 * C) * (q * w) =
      4096 * C * C * K * a := by field_simp; ring
  rw [hId] at hClear'
  have hqw : q * w ≤ w := by nlinarith [mul_le_mul_of_nonneg_right hq1 hw.le]
  have hRemoved : 2048 * C * C * K * a ≤ w' := by nlinarith [hClear', hqw, hhalf]
  have hA : a / w' ≤ (1 / (128 * C * C * K)) / 16 := by
    rw [show (1 / (128 * C * C * K)) / 16 = 1 / (2048 * C * C * K) by ring]
    apply (div_le_div_iff₀ hw' (by positivity : 0 < 2048 * C * C * K)).2
    nlinarith [hRemoved]
  refine ⟨hA, ?_⟩
  intro ηRef hRef
  let ηHole := 1 / (128 * C * C * K)
  have hHolePos : 0 < ηHole := by dsimp only [ηHole]; positivity
  have hA' : a ≤ ηHole / 16 * w' := (div_le_iff₀ hw').1 hA
  have hRefW : ηRef * w ≤ ηHole / 4 * w :=
    mul_le_mul_of_nonneg_right hRef hw.le
  have hRefScale : ηHole / 4 * w ≤ ηHole / 2 * w' := by
    have h := mul_le_mul_of_nonneg_left hhalf hHolePos.le
    nlinarith
  apply (div_le_iff₀ hw').2
  have hHoleW : 0 ≤ ηHole * w' := mul_nonneg hHolePos.le hw'.le
  nlinarith [hA', hRefW, hRefScale]

#print axioms explicit_child_hole_window
#print axioms amplified_schedule_pays_explicit_child_hole

end TypedTriangle.Vortex
