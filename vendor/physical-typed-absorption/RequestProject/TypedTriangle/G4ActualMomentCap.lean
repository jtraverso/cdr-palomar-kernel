/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4UniformMonitorCap
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The same cap pays the actual one-layer moment bound at every stratum. -/

namespace TypedTriangle.StockEntry

theorem exists_actual_moment_cap (L η : ℝ) (K : ℕ)
    (hL : 0 ≤ L) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n b τ ηPack ρ τSel load : ℝ,
        0 ≤ n → 0 ≤ b → load ≤ ηPack * n →
        τ ≤ δ → ηPack ≤ δ → ρ ≤ δ → τSel ≤ δ →
        (K : ℝ) *
          (τ * n * b + (3 * L * b) *
            (load + ρ * n + 2 * (τSel * n) + ρ * n) / 2) ≤
          η * n * b := by
  obtain ⟨δ, hδ, hcap⟩ := exists_uniform_monitor_moment_cap L η K hL hη
  refine ⟨δ, hδ, ?_⟩
  intro n b τ ηPack ρ τSel load hn hb hload hτ hPack hρ hSel
  let B := τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel)
  have hmoment := actual_moment_factor_bound L n b τ ηPack ρ τSel load
    hL hb hload
  have hscaled := mul_le_mul_of_nonneg_left hmoment
    (show (0 : ℝ) ≤ K by positivity)
  have hcap' := mul_le_mul_of_nonneg_right
    (hcap τ ηPack ρ τSel hτ hPack hρ hSel)
    (mul_nonneg hn hb)
  calc
    (K : ℝ) *
        (τ * n * b + (3 * L * b) *
          (load + ρ * n + 2 * (τSel * n) + ρ * n) / 2)
      ≤ (K : ℝ) * (B * n * b) := hscaled
    _ = ((K : ℝ) * B) * (n * b) := by ring
    _ ≤ η * (n * b) := hcap'
    _ = η * n * b := by ring

end TypedTriangle.StockEntry

#print axioms TypedTriangle.StockEntry.exists_actual_moment_cap
