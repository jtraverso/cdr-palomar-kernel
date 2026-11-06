/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexCleanIntermediateGeometry
public import RequestProject.TypedTriangle.VortexCleanHingeGeometry
public import RequestProject.TypedTriangle.VortexAutomaticLossBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A uniformly executable step for a bare geometric vortex. The density
potential depends on current order, so no history or fixed depth is assumed.
The output retains intermediate geometry for the quotient-map argument. -/

open Finset Classical S07V24
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex

def geometryFloor (α₀ : ℝ) (h : ℕ) (n : ℝ) : ℝ :=
  α₀ * (1 - 2 * ((h : ℝ) + 1) * automaticRelativeError n)

theorem geometryFloor_le (α₀ : ℝ) (h : ℕ) (n : ℝ) (hα : 0 ≤ α₀) :
    geometryFloor α₀ h n ≤ α₀ := by
  dsimp [geometryFloor]
  have hprod : 0 ≤ α₀ * (2 * ((h : ℝ) + 1) * automaticRelativeError n) :=
    mul_nonneg hα (mul_nonneg (by positivity) (automaticRelativeError_nonneg n))
  nlinarith

theorem geometryFloor_half_le (α₀ : ℝ) (h : ℕ) (n : ℝ) (hα : 0 ≤ α₀)
    (hn : (4 * ((h : ℝ) + 1)) ^ 4 ≤ n) :
    α₀ / 2 ≤ geometryFloor α₀ h n := by
  have hB : 0 < 4 * ((h : ℝ) + 1) := by positivity
  have hErr := automaticRelativeError_le_of_power_bound _ _ hB hn
  have hscale := mul_le_mul_of_nonneg_left hErr
    (by positivity : 0 ≤ 2 * ((h : ℝ) + 1))
  have heq : 2 * ((h : ℝ) + 1) * (4 * ((h : ℝ) + 1))⁻¹ = (1 / 2 : ℝ) := by
    field_simp
    ring
  rw [heq] at hscale
  have hcoeff : (1 / 2 : ℝ) ≤ 1 - 2 * ((h : ℝ) + 1) * automaticRelativeError n := by
    linarith
  have hs := mul_le_mul_of_nonneg_left hcoeff hα
  simpa only [geometryFloor, mul_one_div] using hs

theorem geometryFloor_step (α₀ : ℝ) (h : ℕ) (x y : ℝ)
    (hα : 0 ≤ α₀) (hx : 0 < x) (hy : 0 < y) (hxy : 16 * y ≤ x) :
    geometryFloor α₀ h y ≤
      geometryFloor α₀ h x * (1 - ((h : ℝ) + 1) * automaticRelativeError x) := by
  have hcontract := automaticRelativeError_contract x y hx hy hxy
  have hC : 0 ≤ (h : ℝ) + 1 := by positivity
  have hs := mul_le_mul_of_nonneg_left hcontract hC
  have hnonneg : 0 ≤ ((h : ℝ) + 1) * automaticRelativeError x :=
    mul_nonneg hC (automaticRelativeError_nonneg x)
  have hcoeff : 1 - 2 * ((h : ℝ) + 1) * automaticRelativeError y ≤
      (1 - 2 * ((h : ℝ) + 1) * automaticRelativeError x) *
        (1 - ((h : ℝ) + 1) * automaticRelativeError x) := by
    nlinarith [sq_nonneg (((h : ℝ) + 1) * automaticRelativeError x)]
  have hscaled := mul_le_mul_of_nonneg_left hcoeff hα
  dsimp [geometryFloor]
  convert hscaled using 1 <;> ring

theorem exists_clean_geometric_step (α₀ q : ℝ) (h M : ℕ)
    (hα : 0 < α₀) (hq : 0 < q) (hq32 : q ≤ 1 / 32)
    (hh : 1 ≤ h) (hM : 1 ≤ M) :
    ∃ N : ℝ, 0 < N ∧ ∀ {V I : Type*} [Fintype V]
      (H : Host V I) (F : Set (Multiset I)), N ≤ (Fintype.card V : ℝ) →
      CommonNbrCond H F (geometryFloor α₀ h (Fintype.card V)) →
      CleanHingeCond H F (geometryFloor α₀ h (Fintype.card V)) h →
      ∃ W : Finset V, M ≤ W.card ∧ 16 * W.card ≤ Fintype.card V ∧
        CommonNbrCond (restrictedHost H (univ \ W)) F (geometryFloor α₀ h W.card) ∧
        CleanHingeCond (restrictedHost H (univ \ W)) F (geometryFloor α₀ h W.card) h ∧
        ∀ U : Finset V, W ⊆ U →
          CommonNbrCond (restrictedHost H (univ \ U)) F (α₀ * q ^ h / 4) ∧
          HingeCond (restrictedHost H (univ \ U)) F (α₀ * q ^ h / 4) h := by
  have hq1 : q ≤ 1 := by linarith
  obtain ⟨Ns, hSample⟩ := exists_automatic_clean_relative_sample_uniform
    (α₀ / 2) q h (by positivity) hq hq1
  let B : ℝ := 4 * ((h : ℝ) + 1)
  let N : ℝ := max (max Ns (B ^ 4)) (max (2 * (M : ℝ) / q) 1)
  have hN1 : 1 ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨N, lt_of_lt_of_le zero_lt_one hN1, ?_⟩
  intro V I _ H F hn h3 hClean
  let n : ℝ := Fintype.card V
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one (hN1.trans hn)
  have hnSample : Ns ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hnPower : B ^ 4 ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
  have hnScale : 2 * (M : ℝ) / q ≤ n :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hαFloor : α₀ / 2 ≤ geometryFloor α₀ h n := geometryFloor_half_le α₀ h n hα.le hnPower
  have hαPos : 0 < geometryFloor α₀ h n := lt_of_lt_of_le (by positivity) hαFloor
  obtain ⟨hηpos, hηlt, W, hWlo, hWhi, hpool, hhinge⟩ :=
    hSample H F (geometryFloor α₀ h n) hαFloor hnSample h3 hClean
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
  have hFloorStep := geometryFloor_step α₀ h n W.card hα.le hnpos hWposR h16
  refine ⟨W, hMW, h16N, commonNbrCond_mono hGeo.1 hFloorStep,
    hGeo.2.mono hFloorStep, ?_⟩
  intro U hWU
  have hInter := anchored_clean_intermediate_geometry H F hαPos hq hq1 hηlt hh
    hClean W U hWU hpool hhinge
  have hFirst : geometryFloor α₀ h n / 2 ≤
      (1 - automaticRelativeError n) * geometryFloor α₀ h n := by
    have hmul := mul_le_mul_of_nonneg_right hηhalf hαPos.le
    nlinarith
  have hBase : α₀ / 4 ≤ (1 - automaticRelativeError n) * geometryFloor α₀ h n := by
    linarith
  have hScaled := mul_le_mul_of_nonneg_right hBase (pow_nonneg hq.le h)
  have hCoeff : α₀ * q ^ h / 4 ≤
      (1 - automaticRelativeError n) * geometryFloor α₀ h n * q ^ h := by
    convert hScaled using 1 <;> ring
  exact ⟨commonNbrCond_mono hInter.1 hCoeff, hingeCond_mono hInter.2.hingeCond hCoeff⟩

/-- A finite bare vortex. Every recursive edge is the actual induced host;
intermediate geometry is retained for the global quotient-map audit. No
packing, paid-mode or terminal absorber is supplied by this datatype. -/
inductive BareCleanVortex {I : Type} (F : Set (Multiset I))
    (α₀ q : ℝ) (h M : ℕ) (N : ℝ) :
    ∀ {V : Type} [Fintype V], Host V I → Type 1 where
  | terminal {V : Type} [Fintype V] (H : Host V I)
      (hLo : M ≤ Fintype.card V) (hHi : (Fintype.card V : ℝ) ≤ N)
      (h3 : CommonNbrCond H F (geometryFloor α₀ h (Fintype.card V)))
      (hClean : CleanHingeCond H F (geometryFloor α₀ h (Fintype.card V)) h) :
      BareCleanVortex F α₀ q h M N H
  | descend {V : Type} [Fintype V] (H : Host V I) (W : Finset V)
      (h3 : CommonNbrCond H F (geometryFloor α₀ h (Fintype.card V)))
      (hClean : CleanHingeCond H F (geometryFloor α₀ h (Fintype.card V)) h)
      (hLo : M ≤ W.card) (hShrink : 16 * W.card ≤ Fintype.card V)
      (hInter : ∀ U : Finset V, W ⊆ U →
        CommonNbrCond (restrictedHost H (univ \ U)) F (α₀ * q ^ h / 4) ∧
        HingeCond (restrictedHost H (univ \ U)) F (α₀ * q ^ h / 4) h)
      (tail : BareCleanVortex F α₀ q h M N (restrictedHost H (univ \ W))) :
      BareCleanVortex F α₀ q h M N H

def BareCleanVortex.terminalOrder {I V : Type} [Fintype V]
    {F : Set (Multiset I)} {α₀ q : ℝ} {h M : ℕ} {N : ℝ} {H : Host V I}
    (chain : BareCleanVortex F α₀ q h M N H) : ℕ := by
  induction chain with
  | @terminal V _ H hLo hHi h3 hClean => exact Fintype.card V
  | descend H W h3 hClean hLo hShrink hInter tail ih => exact ih

theorem BareCleanVortex.terminalOrder_bounds {I V : Type} [Fintype V]
    {F : Set (Multiset I)} {α₀ q : ℝ} {h M : ℕ} {N : ℝ} {H : Host V I}
    (chain : BareCleanVortex F α₀ q h M N H) :
    M ≤ chain.terminalOrder ∧ (chain.terminalOrder : ℝ) ≤ N := by
  induction chain with
  | terminal H hLo hHi h3 hClean => exact ⟨hLo, hHi⟩
  | descend H W h3 hClean hLo hShrink hInter tail ih => exact ih

theorem exists_bare_clean_vortex {I : Type} (F : Set (Multiset I))
    (α₀ q : ℝ) (h M : ℕ) (hα : 0 < α₀) (hq : 0 < q) (hq32 : q ≤ 1 / 32)
    (hh : 1 ≤ h) (hM : 1 ≤ M) :
    ∃ N : ℝ, 0 < N ∧ ∀ {V : Type} [Fintype V] (H : Host V I),
      M ≤ Fintype.card V → CommonNbrCond H F α₀ → CleanHingeCond H F α₀ h →
      Nonempty (BareCleanVortex F α₀ q h M N H) := by
  obtain ⟨N, hN, hStep⟩ := exists_clean_geometric_step α₀ q h M hα hq hq32 hh hM
  refine ⟨N, hN, ?_⟩
  have hAll : ∀ n : ℕ, ∀ {V : Type} [Fintype V] (H : Host V I),
      Fintype.card V = n → M ≤ n →
      CommonNbrCond H F (geometryFloor α₀ h (Fintype.card V)) →
      CleanHingeCond H F (geometryFloor α₀ h (Fintype.card V)) h →
      Nonempty (BareCleanVortex F α₀ q h M N H) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ H hcard hMcur h3 hClean
      by_cases hstop : (Fintype.card V : ℝ) ≤ N
      · exact ⟨.terminal H (by simpa only [hcard] using hMcur) hstop h3 hClean⟩
      · have hn : N ≤ (Fintype.card V : ℝ) := (lt_of_not_ge hstop).le
        obtain ⟨W, hWlo, hShrink, h3W, hCleanW, hInter⟩ := hStep H F hn h3 hClean
        have hWpos : 0 < W.card := lt_of_lt_of_le zero_lt_one (hM.trans hWlo)
        have hWlt : W.card < n := by omega
        obtain ⟨tail⟩ := ih W.card hWlt (restrictedHost H (univ \ W))
          (CorePaid.card_survivors_compl W) hWlo
          (by simpa only [CorePaid.card_survivors_compl] using h3W)
          (by simpa only [CorePaid.card_survivors_compl] using hCleanW)
        exact ⟨.descend H W h3 hClean hWlo hShrink hInter tail⟩
  intro V _ H hOrder h3 hClean
  exact hAll (Fintype.card V) H rfl hOrder
    (commonNbrCond_mono h3 (geometryFloor_le α₀ h _ hα.le))
    (hClean.mono (geometryFloor_le α₀ h _ hα.le))

theorem bare_clean_vortex_of_H3H4 {I : Type} (F : Set (Multiset I))
    (α q : ℝ) (h M : ℕ) (hα : 0 < α) (hq : 0 < q) (hq32 : q ≤ 1 / 32)
    (hh : 6 ≤ h) (hM : 1 ≤ M) :
    let α₀ := min α (S07V49.hingeConstB α 1 h)
    let h₀ := 2 * h - 3
    ∃ Nroot Nterminal : ℝ, 0 < Nterminal ∧
      ∀ {V : Type} [Fintype V] (H : Host V I),
        Nroot ≤ (Fintype.card V : ℝ) → CommonNbrCond H F α → HingeCond H F α h →
        Nonempty (BareCleanVortex F α₀ q h₀ M Nterminal H) := by
  dsimp only
  have hβ : 0 < S07V49.hingeConstB α 1 h :=
    S07V49.hingeConstB_pos hα (by norm_num) (by omega)
  obtain ⟨Nclean, hMakeClean⟩ := clean_hinge_of_H3H4 α h hα hh
  obtain ⟨Nterminal, hNt, hChain⟩ := exists_bare_clean_vortex F
    (min α (S07V49.hingeConstB α 1 h)) q (2 * h - 3) M
    (lt_min hα hβ) hq hq32 (by omega) hM
  refine ⟨max (Nclean : ℝ) M, Nterminal, hNt, ?_⟩
  intro V _ H hn h3 h4
  have hnClean : Nclean ≤ Fintype.card V := by
    exact_mod_cast (le_max_left (Nclean : ℝ) M).trans hn
  have hnM : M ≤ Fintype.card V := by
    exact_mod_cast (le_max_right (Nclean : ℝ) M).trans hn
  have hClean := hMakeClean H F hnClean h3 h4
  exact hChain H hnM (commonNbrCond_mono h3 (min_le_left _ _))
    (hClean.mono (min_le_right _ _))

#print axioms geometryFloor_half_le
#print axioms geometryFloor_step
#print axioms exists_clean_geometric_step
#print axioms BareCleanVortex.terminalOrder_bounds
#print axioms exists_bare_clean_vortex
#print axioms bare_clean_vortex_of_H3H4

end TypedTriangle.Vortex
