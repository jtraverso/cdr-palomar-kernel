/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexCleanGeometricStep
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A two-coordinate geometric budget: automatic sampling errors depend on
the current order, while preparation losses depend on the intrinsic global
quotient index. Thus preparation losses are paid once per index, not once
per level. -/

open Finset
noncomputable section
namespace TypedTriangle.Vortex

def globalGeometryFloor (α₀ : ℝ) (h : ℕ) (D : ℝ) (β : ℕ → ℝ)
    (n : ℝ) (r : ℕ) : ℝ := geometryFloor α₀ h n - D * ∑ j ∈ range r, β j

private theorem prefix_mono (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j)
    {r s : ℕ} (hrs : r ≤ s) :
    (∑ j ∈ range r, β j) ≤ ∑ j ∈ range s, β j :=
  sum_le_sum_of_subset_of_nonneg (range_mono hrs) (by intro j _ _; exact hβ j)

private theorem prefix_step (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j)
    {r s : ℕ} (hrs : r < s) :
    (∑ j ∈ range r, β j) + β r ≤ ∑ j ∈ range s, β j := by
  rw [← sum_range_succ]
  exact prefix_mono β hβ hrs

theorem automaticRelativeError_antitone (x y : ℝ) (hy : 0 < y) (hxy : y ≤ x) :
    automaticRelativeError x ≤ automaticRelativeError y := by
  have hm := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hxy)
  have hp : 0 < Real.sqrt (Real.sqrt y) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hy)
  simpa only [automaticRelativeError, one_div] using one_div_le_one_div_of_le hp hm

theorem globalGeometryFloor_sample (α₀ D : ℝ) (h : ℕ) (β : ℕ → ℝ)
    (hα : 0 ≤ α₀) (hD : 0 ≤ D) (hβ : ∀ j, 0 ≤ β j)
    (x y : ℝ) (r s : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hxy : 16 * y ≤ x) (hrs : r ≤ s) :
    globalGeometryFloor α₀ h D β y s ≤
      globalGeometryFloor α₀ h D β x r *
        (1 - ((h : ℝ) + 1) * automaticRelativeError x) := by
  have hGeom := geometryFloor_step α₀ h x y hα hx hy hxy
  have hDebt := mul_le_mul_of_nonneg_left (prefix_mono β hβ hrs) hD
  have hSum : 0 ≤ D * ∑ j ∈ range r, β j :=
    mul_nonneg hD (sum_nonneg (by intro j _; exact hβ j))
  have hErr : 0 ≤ ((h : ℝ) + 1) * automaticRelativeError x :=
    mul_nonneg (by positivity) (automaticRelativeError_nonneg x)
  have hBonus := mul_nonneg hSum hErr
  dsimp [globalGeometryFloor]
  nlinarith

theorem globalGeometryFloor_trim (α₀ D : ℝ) (h : ℕ) (β : ℕ → ℝ)
    (hα : 0 ≤ α₀) (x y : ℝ) (r s : ℕ) (hy : 0 < y) (hxy : y ≤ x) :
    globalGeometryFloor α₀ h D β y s ≤
      globalGeometryFloor α₀ h D β x r -
        D * ((∑ j ∈ range s, β j) - ∑ j ∈ range r, β j) := by
  have hErr := automaticRelativeError_antitone x y hy hxy
  have hScale := mul_le_mul_of_nonneg_left hErr
    (mul_nonneg hα (by positivity : 0 ≤ 2 * ((h : ℝ) + 1)))
  dsimp [globalGeometryFloor, geometryFloor]
  nlinarith

theorem globalGeometryFloor_prepare (α₀ D : ℝ) (h : ℕ) (β : ℕ → ℝ)
    (hα : 0 ≤ α₀) (hD : 0 ≤ D) (hβ : ∀ j, 0 ≤ β j)
    (x y : ℝ) (r s : ℕ) (hy : 0 < y) (hxy : y ≤ x) (hrs : r < s) :
    globalGeometryFloor α₀ h D β y s ≤
      globalGeometryFloor α₀ h D β x r - D * β r := by
  have hErr := automaticRelativeError_antitone x y hy hxy
  have hScale := mul_le_mul_of_nonneg_left hErr
    (mul_nonneg hα (by positivity : 0 ≤ 2 * ((h : ℝ) + 1)))
  have hGeom : geometryFloor α₀ h y ≤ geometryFloor α₀ h x := by
    dsimp [geometryFloor]
    nlinarith
  have hDebt := mul_le_mul_of_nonneg_left (prefix_step β hβ hrs) hD
  dsimp [globalGeometryFloor]
  nlinarith

theorem globalGeometryFloor_half_le (α₀ D : ℝ) (h : ℕ) (β : ℕ → ℝ)
    (n : ℝ) (r : ℕ) (hα : 0 ≤ α₀)
    (hn : (8 * ((h : ℝ) + 1)) ^ 4 ≤ n)
    (hDebt : D * (∑ j ∈ range r, β j) ≤ α₀ / 4) :
    α₀ / 2 ≤ globalGeometryFloor α₀ h D β n r := by
  have hErr := automaticRelativeError_le_of_power_bound
    (8 * ((h : ℝ) + 1)) n (by positivity) hn
  have hScale := mul_le_mul_of_nonneg_left hErr
    (by positivity : 0 ≤ 2 * ((h : ℝ) + 1))
  have heq : 2 * ((h : ℝ) + 1) * (8 * ((h : ℝ) + 1))⁻¹ = (1 / 4 : ℝ) := by
    field_simp
    ring
  rw [heq] at hScale
  have hScaled := mul_le_mul_of_nonneg_left hScale hα
  dsimp [globalGeometryFloor, geometryFloor]
  nlinarith

/-- Disjoint intrinsic-index intervals telescope even when the number of
sampled levels depends on the host. Sampling may skip arbitrarily many
indices; skipped radii are never charged twice. -/
theorem sum_global_preparation_intervals (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (enter leave : ℕ → ℕ) (m : ℕ)
    (hNext : ∀ i < m, leave i ≤ enter (i + 1)) :
    (∑ i ∈ range m, ((∑ j ∈ range (leave i), β j) - ∑ j ∈ range (enter i), β j)) ≤
      (∑ j ∈ range (enter m), β j) - ∑ j ∈ range (enter 0), β j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hPrev := ih (by intro i hi; exact hNext i (by omega))
    have hLast := prefix_mono β hβ (hNext m (by omega))
    rw [sum_range_succ]
    linarith

def globalMinimumOrder (L M r : ℕ) : ℕ := 2 ^ (L - r) * M

theorem globalMinimumOrder_le {L M r : ℕ} : M ≤ globalMinimumOrder L M r := by
  dsimp [globalMinimumOrder]
  have hp : 1 ≤ 2 ^ (L - r) := Nat.one_le_pow _ _ (by decide)
  nlinarith

theorem globalMinimumOrder_prepare {L M r s n m : ℕ}
    (hr : r < s) (hs : s ≤ L)
    (hn : globalMinimumOrder L M r ≤ n) (hm : n ≤ 2 * m) :
    globalMinimumOrder L M s ≤ m := by
  have hexp : L - r = (L - (r + 1)) + 1 := by omega
  have hpow : 2 ^ (L - s) ≤ 2 ^ (L - (r + 1)) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpMul := Nat.mul_le_mul_right M hpow
  have heq : globalMinimumOrder L M r = 2 * (2 ^ (L - (r + 1)) * M) := by
    dsimp [globalMinimumOrder]
    rw [hexp, pow_succ]
    ring
  dsimp [globalMinimumOrder]
  rw [heq] at hn
  omega

#print axioms globalGeometryFloor_sample
#print axioms globalGeometryFloor_prepare
#print axioms globalGeometryFloor_half_le
#print axioms globalMinimumOrder_prepare
end TypedTriangle.Vortex
