/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexGlobalGeometryBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset
noncomputable section
set_option autoImplicit false

namespace TypedTriangle.Vortex

/-- The raw profile is charged for sampling by the current order and for
preparation by the intrinsic quotient index, rather than by chain depth. -/
def globalRawProfileError (A E : ℝ) (β : ℕ → ℝ) (n : ℝ) (r : ℕ) : ℝ :=
  A * automaticRelativeError n + E * ∑ j ∈ range r, β j

theorem globalRawProfileError_sample (A E : ℝ) (β : ℕ → ℝ)
    (hA : 2 ≤ A) (hE : 0 ≤ E) (hβ : ∀ j, 0 ≤ β j)
    (x y : ℝ) (r s : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hxy : 16*y ≤ x) (hrs : r ≤ s) :
    globalRawProfileError A E β x r + 2*automaticRelativeError x ≤
      globalRawProfileError A E β y s := by
  have hErr := automaticRelativeError_contract x y hx hy hxy
  have hNonneg := automaticRelativeError_nonneg x
  have hGrowth : A*automaticRelativeError x + 2*automaticRelativeError x ≤
      A*automaticRelativeError y := by
    have hDiff : automaticRelativeError x ≤
        automaticRelativeError y - automaticRelativeError x := by linarith
    have hScale := mul_le_mul_of_nonneg_left hDiff (by linarith : 0 ≤ A)
    have hTwo := mul_le_mul_of_nonneg_right hA hNonneg
    nlinarith
  have hPrefix : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range s, β j :=
    sum_le_sum_of_subset_of_nonneg (range_mono hrs) (by intro j _ _; exact hβ j)
  have hDebt := mul_le_mul_of_nonneg_left hPrefix hE
  dsimp [globalRawProfileError]
  linarith

theorem globalRawProfileError_prepare (A E b δ : ℝ) (β : ℕ → ℝ)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hb : b ≤ E) (hδ : 0 ≤ δ)
    (x y : ℝ) (r s : ℕ) (hy : 0 < y) (hxy : y ≤ x)
    (hBudget : δ ≤ (∑ j ∈ range s, β j) - ∑ j ∈ range r, β j) :
    globalRawProfileError A E β x r + b*δ ≤
      globalRawProfileError A E β y s := by
  have hErr := automaticRelativeError_antitone x y hy hxy
  have hScale := mul_le_mul_of_nonneg_left hErr hA
  have hPaid := mul_le_mul_of_nonneg_left hBudget hE
  have hCoeff := mul_le_mul_of_nonneg_right hb hδ
  dsimp [globalRawProfileError]
  nlinarith

theorem globalRawProfileError_le_cap (A E cap : ℝ) (β : ℕ → ℝ)
    (n : ℝ) (r : ℕ)
    (hSample : A*automaticRelativeError n ≤ cap/2)
    (hDebt : E*(∑ j ∈ range r, β j) ≤ cap/2) :
    globalRawProfileError A E β n r ≤ cap := by
  dsimp [globalRawProfileError]
  linarith

#print axioms globalRawProfileError_sample
#print axioms globalRawProfileError_prepare
#print axioms globalRawProfileError_le_cap
end TypedTriangle.Vortex
