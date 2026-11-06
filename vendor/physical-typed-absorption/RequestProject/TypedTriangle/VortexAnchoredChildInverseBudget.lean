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

/-- A fixed relative raw window anchored at the original seed is paid by
exactly the same sampling and hole margins as the explicit calendar. -/
theorem anchored_child_inverse_budget (C K ξ η ζ n : ℝ) (d : ℕ)
    (hC : 1 ≤ C) (hK : 0 ≤ K) (hn : 0 < n)
    (hηLower : 1 / 8 ≤ η) (hηUpper : η ≤ 1 / 4)
    (hζ : 0 ≤ ζ) (hd : (d : ℝ) ≤ ζ * n)
    (hSample : K * ξ ≤ 1 / (16 * C))
    (hHoles : K * (8 * C * ζ) ≤ 1 / (16 * C)) :
    K * (ξ + 2 * ((1 + η) * C) * d / n) ≤ η / C := by
  have hCpos : 0 < C := by linarith
  have hη : 0 ≤ η := by linarith
  have hCoeff : 0 ≤ 2 * ((1 + η) * C) := by positivity
  have hCoeffLe : 2 * ((1 + η) * C) ≤ 8 * C := by nlinarith
  have hTerm : 2 * ((1 + η) * C) * (d : ℝ) / n ≤ 8 * C * ζ := by
    apply (div_le_iff₀ hn).2
    calc
      2 * ((1 + η) * C) * (d : ℝ) ≤ 2 * ((1 + η) * C) * (ζ * n) :=
        mul_le_mul_of_nonneg_left hd hCoeff
      _ ≤ 8 * C * (ζ * n) := mul_le_mul_of_nonneg_right hCoeffLe (by positivity)
      _ = (8 * C * ζ) * n := by ring
  have hBound := add_le_add hSample
    ((mul_le_mul_of_nonneg_left hTerm hK).trans hHoles)
  have hScale := div_le_div_of_nonneg_right hηLower hCpos.le
  calc
    K * (ξ + 2 * ((1 + η) * C) * d / n) ≤
        1 / (16 * C) + 1 / (16 * C) := by nlinarith [hBound]
    _ = (1 / 8) / C := by ring
    _ ≤ η / C := hScale

#print axioms anchored_child_inverse_budget
end TypedTriangle.Vortex
