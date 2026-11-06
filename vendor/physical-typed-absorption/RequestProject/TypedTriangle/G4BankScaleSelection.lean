/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4FinalBankCapacity
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Choose the positive allocation scale after the native bank density is
known, while keeping the selector's linear capacity and the bank's quadratic
capacity compatible. -/

namespace TypedTriangle.StockEntry

theorem exists_native_bank_scales (κ q ε : ℝ) (B : ℕ)
    (hκ : 0 < κ) (hq : 0 < q) (hε : 0 < ε) :
    ∃ γ η : ℝ, 0 < γ ∧ 0 < η ∧ η ≤ κ * q ^ 2 / 8 ∧
      η * B / γ ≤ 1 ∧
      ∀ n w qSel : ℕ, q * n / 2 ≤ w →
        ε * w / 4 ≤ qSel → γ * n ≤ qSel := by
  let γ := ε * q / 8
  have hγ : 0 < γ := by dsimp [γ]; positivity
  let η := min (κ * q ^ 2 / 8) (γ / ((B : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨γ, η, hγ, hη, min_le_left _ _, ?_, ?_⟩
  · have hη' : η ≤ γ / ((B : ℝ) + 1) := min_le_right _ _
    have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    have hD : (0 : ℝ) < B + 1 := by positivity
    have hprod := mul_le_mul_of_nonneg_right hη' hB
    apply (div_le_iff₀ hγ).2
    have hquot : γ / ((B : ℝ) + 1) * B ≤ γ := by
      calc
        γ / ((B : ℝ) + 1) * B = γ * B / ((B : ℝ) + 1) := by ring
        _ ≤ γ := (div_le_iff₀ hD).2 (by nlinarith only [hγ, hB])
    nlinarith only [hprod, hquot]
  · intro n w qSel hw hsel
    dsimp [γ]
    have hw' := mul_le_mul_of_nonneg_left hw (show 0 ≤ ε / 4 by positivity)
    nlinarith only [hw', hsel]

end TypedTriangle.StockEntry

#print axioms TypedTriangle.StockEntry.exists_native_bank_scales
