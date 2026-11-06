/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4PositiveMomentBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A common late cap pays the local contribution of the actual stock,
selector and packing. The cap is chosen after the bank's allocation budget. -/

namespace TypedTriangle.StockEntry

theorem exists_small_positive_moment_cap (L η : ℝ) (hL : 0 ≤ L) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ τ ηPack ρ τSel : ℝ,
        τ ≤ δ → ηPack ≤ δ → ρ ≤ δ → τSel ≤ δ →
        τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel) ≤ η := by
  refine ⟨η / (2 + 15 * L), by positivity, ?_⟩
  intro τ ηPack ρ τSel hτ hPack hρ hSel
  have hsum : ηPack + 2 * ρ + 2 * τSel ≤ 5 * (η / (2 + 15 * L)) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 3 * L / 2 by positivity)
  have hden : 0 < 2 + 15 * L := by positivity
  have hscale : (η / (2 + 15 * L)) * (2 + 15 * L) = η := by
    field_simp
  nlinarith only [hmul, hτ, hscale, hη.le]

end TypedTriangle.StockEntry
