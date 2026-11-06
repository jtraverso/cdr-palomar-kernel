/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4BankScaleSelection
public import RequestProject.TypedTriangle.G4UniformMonitorCap
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Pick the bank capacity, monitor tolerance and terminal sample threshold
in the order required by the native one-layer construction. -/

namespace TypedTriangle.StockEntry

theorem exists_native_bank_scale_cap
    (κ q ε Λ : ℝ) (B K : ℕ)
    (hκ : 0 < κ) (hq : 0 < q) (hε : 0 < ε) (hΛ : 0 ≤ Λ) :
    ∃ γ η δ : ℝ, 0 < γ ∧ 0 < η ∧ 0 < δ ∧
      η ≤ κ * q ^ 2 / 8 ∧ η * B / γ ≤ 1 ∧
      (∀ n w qSel : ℕ, q * n / 2 ≤ w →
        ε * w / 4 ≤ qSel → γ * n ≤ qSel) ∧
      (∀ τ ηPack ρ τSel : ℝ,
        τ ≤ δ → ηPack ≤ δ → ρ ≤ δ → τSel ≤ δ →
        (K : ℝ) *
          (τ + (3 * Λ / 2) * (ηPack + 2 * ρ + 2 * τSel)) ≤ η) ∧
      ∃ nBank : ℕ, ∀ n : ℕ, nBank ≤ n →
        8 ≤ κ * q ^ 2 * (n : ℝ) ^ 2 := by
  obtain ⟨γ,η,hγ,hη,hηκ,hcapacity,hqn⟩ :=
    exists_native_bank_scales κ q ε B hκ hq hε
  obtain ⟨δ,hδ,hKB⟩ :=
    exists_uniform_monitor_moment_cap Λ η K hΛ hη
  obtain ⟨nBank,hN⟩ := eventually_large_for_bank κ q hκ hq
  exact ⟨γ,η,δ,hγ,hη,hδ,hηκ,hcapacity,hqn,hKB,nBank,hN⟩

end TypedTriangle.StockEntry

#print axioms TypedTriangle.StockEntry.exists_native_bank_scale_cap
