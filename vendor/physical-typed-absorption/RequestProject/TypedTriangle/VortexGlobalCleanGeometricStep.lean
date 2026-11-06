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

open Finset Classical S07V24
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex

/-- Uniform clean sampling with the intrinsic global-index debt held fixed
through the geometric step. -/
theorem exists_global_clean_geometric_step (α₀ q D : ℝ) (h M L : ℕ) (β : ℕ → ℝ)
    (hα : 0 < α₀) (hq : 0 < q) (hq32 : q ≤ 1 / 32)
    (hh : 1 ≤ h) (hM : 1 ≤ M) (hD : 0 ≤ D)
    (hβ : ∀ j, 0 ≤ β j)
    (hDebt : D * (∑ j ∈ range (L + 1), β j) ≤ α₀ / 4) :
    ∃ N : ℝ, 0 < N ∧ ∀ {V I : Type*} [Fintype V]
      (H : Host V I) (F : Set (Multiset I)) (r : ℕ), r ≤ L →
      N ≤ (Fintype.card V : ℝ) →
      CommonNbrCond H F (globalGeometryFloor α₀ h D β (Fintype.card V) r) →
      CleanHingeCond H F (globalGeometryFloor α₀ h D β (Fintype.card V) r) h →
      ∃ W : Finset V, M ≤ W.card ∧ 16 * W.card ≤ Fintype.card V ∧
        CommonNbrCond (restrictedHost H (univ \ W)) F (globalGeometryFloor α₀ h D β W.card r) ∧
        CleanHingeCond (restrictedHost H (univ \ W)) F (globalGeometryFloor α₀ h D β W.card r) h ∧
        ∀ U : Finset V, W ⊆ U →
          CommonNbrCond (restrictedHost H (univ \ U)) F (α₀ * q ^ h / 4) ∧
          HingeCond (restrictedHost H (univ \ U)) F (α₀ * q ^ h / 4) h := by
  have hq1 : q ≤ 1 := by linarith
  obtain ⟨Ns, hSample⟩ := exists_automatic_clean_relative_sample_uniform
    (α₀ / 2) q h (by positivity) hq hq1
  let B : ℝ := 8 * ((h : ℝ) + 1)
  let N : ℝ := max (max Ns (B ^ 4)) (max (2 * (M : ℝ) / q) 1)
  have hN1 : 1 ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨N, lt_of_lt_of_le zero_lt_one hN1, ?_⟩
  intro V I _ H F r hr hn h3 hClean
  let n : ℝ := Fintype.card V
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one (hN1.trans hn)
  have hnSample : Ns ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hnPower : B ^ 4 ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
  have hnScale : 2 * (M : ℝ) / q ≤ n :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hPrefix : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range (L + 1), β j :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intro j _ _; exact hβ j)
  have hDebtPrefix : D * (∑ j ∈ range r, β j) ≤ α₀ / 4 :=
    (mul_le_mul_of_nonneg_left hPrefix hD).trans hDebt
  have hαFloor : α₀ / 2 ≤ globalGeometryFloor α₀ h D β n r :=
    globalGeometryFloor_half_le α₀ D h β n r hα.le hnPower hDebtPrefix
  have hαPos : 0 < globalGeometryFloor α₀ h D β n r := lt_of_lt_of_le (by positivity) hαFloor
  obtain ⟨hηpos, hηlt, W, hWlo, hWhi, hpool, hhinge⟩ :=
    hSample H F (globalGeometryFloor α₀ h D β n r) hαFloor hnSample h3 hClean
  have hB : 0 < B := by dsimp [B]; positivity
  have hErr := automaticRelativeError_le_of_power_bound B n hB hnPower
  have hTwoB : (2 : ℝ) ≤ B := by dsimp [B]; nlinarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ (h : ℝ))]
  have hηhalf : automaticRelativeError n ≤ 1 / 2 := by
    have hInv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hTwoB
    exact hErr.trans (by simpa only [one_div] using hInv)
  change (1 - automaticRelativeError n) * q * n ≤ (W.card : ℝ) at hWlo
  change (W.card : ℝ) < (1 + automaticRelativeError n) * q * n at hWhi
  have hMReal : (M : ℝ) ≤ W.card := by
    have hscale := (div_le_iff₀ hq).mp hnScale
    have hhalf : (1 / 2 : ℝ) ≤ 1 - automaticRelativeError n := by linarith
    have hmul := mul_le_mul_of_nonneg_right hhalf (mul_nonneg hq.le hnpos.le)
    nlinarith [hWlo]
  have hMW : M ≤ W.card := by exact_mod_cast hMReal
  have hWpos : 0 < W.card := lt_of_lt_of_le zero_lt_one (hM.trans hMW)
  have hWposR : (0 : ℝ) < W.card := by exact_mod_cast hWpos
  have hUpper : (W.card : ℝ) ≤ (2 * q) * n := by
    calc
      _ ≤ (1 + automaticRelativeError n) * q * n := hWhi.le
      _ ≤ (2 * q) * n := by gcongr; linarith
  have hqScale : 16 * (2 * q) ≤ 1 := by linarith
  have h16 : 16 * (W.card : ℝ) ≤ n := by
    have hmul := mul_le_mul_of_nonneg_right hqScale hnpos.le
    nlinarith [hUpper]
  have h16N : 16 * W.card ≤ Fintype.card V := by
    change 16 * (W.card : ℝ) ≤ (Fintype.card V : ℝ) at h16
    exact_mod_cast h16
  have hGeo := clean_relative_sample_child_geometry H F hαPos hq
    hηpos.le hηlt hh hClean W hWhi.le hpool hhinge
  have hFloorStep := globalGeometryFloor_sample α₀ D h β hα.le hD hβ
    n W.card r r hnpos hWposR h16 le_rfl
  refine ⟨W, hMW, h16N, commonNbrCond_mono hGeo.1 hFloorStep,
    hGeo.2.mono hFloorStep, ?_⟩
  intro U hWU
  have hInter := anchored_clean_intermediate_geometry H F hαPos hq hq1 hηlt hh
    hClean W U hWU hpool hhinge
  have hFirst : globalGeometryFloor α₀ h D β n r / 2 ≤
      (1 - automaticRelativeError n) * globalGeometryFloor α₀ h D β n r := by
    have hmul := mul_le_mul_of_nonneg_right hηhalf hαPos.le
    nlinarith
  have hBase : α₀ / 4 ≤ (1 - automaticRelativeError n) * globalGeometryFloor α₀ h D β n r := by
    linarith
  have hScaled := mul_le_mul_of_nonneg_right hBase (pow_nonneg hq.le h)
  have hCoeff : α₀ * q ^ h / 4 ≤
      (1 - automaticRelativeError n) * globalGeometryFloor α₀ h D β n r * q ^ h := by
    convert hScaled using 1 <;> ring
  exact ⟨commonNbrCond_mono hInter.1 hCoeff, hingeCond_mono hInter.2.hingeCond hCoeff⟩


#print axioms exists_global_clean_geometric_step
end TypedTriangle.Vortex
