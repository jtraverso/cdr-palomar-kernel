/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4PositiveCapacityArithmetic
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The number of physical monitor coordinates is fixed by the catalog before
the packing parameters are chosen. One later cap pays all coordinates at once. -/

namespace TypedTriangle.StockEntry

theorem exists_uniform_monitor_moment_cap (L η : ℝ) (K : ℕ)
    (hL : 0 ≤ L) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ τ ηPack ρ τSel : ℝ,
        τ ≤ δ → ηPack ≤ δ → ρ ≤ δ → τSel ≤ δ →
        (K : ℝ) *
          (τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel)) ≤ η := by
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hηK : 0 < η / ((K : ℝ) + 1) := div_pos hη hKpos
  obtain ⟨δ, hδ, hcap⟩ := exists_small_positive_moment_cap L
    (η / ((K : ℝ) + 1)) hL hηK
  refine ⟨δ, hδ, ?_⟩
  intro τ ηPack ρ τSel hτ hPack hρ hSel
  have hbudget := hcap τ ηPack ρ τSel hτ hPack hρ hSel
  have hK : (K : ℝ) ≤ (K : ℝ) + 1 := by linarith
  have hquot : ((K : ℝ) + 1) * (η / ((K : ℝ) + 1)) = η := by field_simp
  by_cases hnonneg : 0 ≤ τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel)
  · calc
      (K : ℝ) * (τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel))
          ≤ ((K : ℝ) + 1) * (τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel)) :=
            mul_le_mul_of_nonneg_right hK hnonneg
      _ ≤ ((K : ℝ) + 1) * (η / ((K : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hbudget hKpos.le
      _ = η := hquot
  · have hneg : τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel) < 0 :=
      lt_of_not_ge hnonneg
    have hk0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    exact (mul_nonpos_of_nonneg_of_nonpos hk0 hneg.le).trans hη.le

/-- Substitute the actual cover-down load into the per-coordinate G34
moment bound. The same identity applies with `b = |Z|` or `b = n`. -/
theorem actual_moment_factor_bound (L n b τ ηPack ρ τSel load : ℝ)
    (hL : 0 ≤ L) (hb : 0 ≤ b)
    (hload : load ≤ ηPack * n) :
    τ * n * b + (3 * L * b) *
      (load + ρ * n + 2 * (τSel * n) + ρ * n) / 2 ≤
      (τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel)) * n * b := by
  have hplus : load + ρ * n + 2 * (τSel * n) + ρ * n ≤
      ηPack * n + ρ * n + 2 * (τSel * n) + ρ * n := by
    linarith only [hload]
  have hfac : 0 ≤ 3 * L * b / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hplus hfac
  calc
    τ * n * b + (3 * L * b) *
        (load + ρ * n + 2 * (τSel * n) + ρ * n) / 2 =
      τ * n * b + (3 * L * b / 2) *
        (load + ρ * n + 2 * (τSel * n) + ρ * n) := by ring
    _ ≤ τ * n * b + (3 * L * b / 2) *
        (ηPack * n + ρ * n + 2 * (τSel * n) + ρ * n) :=
      add_le_add_right hmul _
    _ = (τ + (3 * L / 2) * (ηPack + 2 * ρ + 2 * τSel)) * n * b := by ring

end TypedTriangle.StockEntry
