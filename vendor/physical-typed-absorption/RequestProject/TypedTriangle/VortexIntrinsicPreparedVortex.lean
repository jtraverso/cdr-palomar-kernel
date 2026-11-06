/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexIntrinsicPreparation
public import RequestProject.TypedTriangle.VortexGlobalCleanGeometricStep
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A finite, globally prepared geometric vortex. All hosts and samples are
actual induced subtypes. This constructs no paid layers or decomposition. -/
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex

structure IntrinsicPreparedLayer {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (α₀ : ℝ) (β : ℕ → ℝ)
    (h N M d T : ℕ) where
  trim : Finset V
  index : ℕ
  index_le : index ≤ d + (d + 1) * Nat.log 2 T
  index_enter : physicalPotential H F T ≤ index
  index_eq : physicalPotential (restrictedHost H trim) F T = index
  cost : (trim.card : ℝ) ≤ Fintype.card V *
    ((∑ j ∈ range index, β j) - ∑ j ∈ range (physicalPotential H F T), β j)
  h3 : CommonNbrCond (restrictedHost H trim) F (α₀ / 4)
  clean : CleanHingeCond (restrictedHost H trim) F (α₀ / 4) h
  prepared : Dispersal.PreparedCore (restrictedHost H trim).G (restrictedHost H trim).lab
    F ((α₀ / 4) / 2) h N (β index)
  lower : M ≤ Fintype.card (Survivors trim)

inductive IntrinsicPreparedVortex {I : Type} (F : Set (Multiset I))
    (α₀ q : ℝ) (β : ℕ → ℝ) (h N M d T : ℕ) (t : ℝ) :
    ∀ {V : Type} [Fintype V], Host V I → Type 1 where
  | terminal {V : Type} [Fintype V] {H : Host V I}
      (node : IntrinsicPreparedLayer H F α₀ β h N M d T)
      (upper : (Fintype.card (Survivors node.trim) : ℝ) ≤ t) :
      IntrinsicPreparedVortex F α₀ q β h N M d T t H
  | descend {V : Type} [Fintype V] {H : Host V I}
      (node : IntrinsicPreparedLayer H F α₀ β h N M d T)
      (W : Finset (Survivors node.trim))
      (lower : 2 * M ≤ W.card)
      (shrink : 16 * W.card ≤ Fintype.card (Survivors node.trim))
      (intermediate : letI : DecidableEq (Survivors node.trim) := Classical.decEq _
        ∀ U : Finset (Survivors node.trim), W ⊆ U →
        CommonNbrCond (restrictedHost (restrictedHost H node.trim) (univ \ U)) F (α₀ * q ^ h / 4) ∧
        HingeCond (restrictedHost (restrictedHost H node.trim) (univ \ U)) F (α₀ * q ^ h / 4) h)
      (next_index : letI : DecidableEq (Survivors node.trim) := Classical.decEq _
        node.index ≤ physicalPotential
        (restrictedHost (restrictedHost H node.trim) (univ \ W)) F T)
      (tail : letI : DecidableEq (Survivors node.trim) := Classical.decEq _
        IntrinsicPreparedVortex F α₀ q β h N M d T t
        (restrictedHost (restrictedHost H node.trim) (univ \ W))) :
      IntrinsicPreparedVortex F α₀ q β h N M d T t H

def IntrinsicPreparedVortex.terminalOrder {I V : Type} [Fintype V]
    {F : Set (Multiset I)} {α₀ q : ℝ} {β : ℕ → ℝ} {h N M d T : ℕ} {t : ℝ} {H : Host V I}
    (chain : IntrinsicPreparedVortex F α₀ q β h N M d T t H) : ℕ := by
  induction chain with
  | terminal node upper => exact Fintype.card (Survivors node.trim)
  | descend node W lower shrink intermediate next_index tail ih => exact ih

theorem IntrinsicPreparedVortex.terminalOrder_bounds {I V : Type} [Fintype V]
    {F : Set (Multiset I)} {α₀ q : ℝ} {β : ℕ → ℝ} {h N M d T : ℕ} {t : ℝ} {H : Host V I}
    (chain : IntrinsicPreparedVortex F α₀ q β h N M d T t H) :
    M ≤ chain.terminalOrder ∧ (chain.terminalOrder : ℝ) ≤ t := by
  induction chain with
  | terminal node upper => exact ⟨node.lower, upper⟩
  | descend node W lower shrink intermediate next_index tail ih => exact ih

theorem exists_intrinsic_prepared_vortex {I : Type} (F : Set (Multiset I))
    (α₀ q : ℝ) (h : ℕ) (hα : 0 < α₀) (hq : 0 < q) (hq32 : q ≤ 1 / 32) (hh : 1 ≤ h) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ d T : ℕ, 1 ≤ T ∧
      let L := d + (d + 1) * Nat.log 2 T
      ∀ β : ℕ → ℝ, (∀ j, 0 ≤ β j) → (∑ j ∈ range (L + 1), β j) ≤ ε →
      ∀ N Mrequired : ℕ, ∃ M nRoot : ℕ, Mrequired ≤ M ∧ 1 ≤ M ∧ ∃ t : ℝ, 0 < t ∧
      ∀ {V : Type} [Fintype V] (H : Host V I), nRoot ≤ Fintype.card V →
        CommonNbrCond H F α₀ → CleanHingeCond H F α₀ h →
        Nonempty (IntrinsicPreparedVortex F α₀ q β h N M d T t H) := by
  let D : ℝ := 2 ^ Nat.choose h 2
  have hD : 0 < D := by positivity
  obtain ⟨εPrep, hεPrep, d, T, hT, hPrepareAll⟩ :=
    intrinsic_preparation_with_clean_geometry (α₀ / 4) h (by positivity)
  let ε := min εPrep (α₀ / (4 * D))
  have hε : 0 < ε := lt_min hεPrep (by positivity)
  refine ⟨ε, hε, d, T, hT, ?_⟩
  dsimp only
  let L := d + (d + 1) * Nat.log 2 T
  intro β hβ hBudget N Mrequired
  obtain ⟨nPrep, hQuot, hPrepare⟩ := hPrepareAll N
  let κ : ℝ := α₀ * q ^ h / 4
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let R : ℝ := max ((8 * ((h : ℝ) + 1)) ^ 4)
    (max (4 / κ) (2 * (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 / κ))
  let M := max (max nPrep Mrequired) (max 1 (⌈R⌉₊ + 1))
  have hMprep : nPrep ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMreq : Mrequired ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hM1 : 1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hCeil : (⌈R⌉₊ : ℝ) ≤ M := by
    exact_mod_cast (show ⌈R⌉₊ ≤ M from (Nat.le_succ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hRM : R ≤ M := (Nat.le_ceil _).trans hCeil
  have hPower : (8 * ((h : ℝ) + 1)) ^ 4 ≤ M := (le_max_left _ _).trans hRM
  have hW1 : 3 < κ * M := by
    have hs : 4 / κ ≤ (M : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hRM
    have hs' := (div_le_iff₀ hκ).mp hs
    linarith
  have hW2 : (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 ≤ κ / 2 * M := by
    have hs : 2 * (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 / κ ≤ (M : ℝ) :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hRM
    have hs' := (div_le_iff₀ hκ).mp hs
    nlinarith
  have hBudgetPrep := hBudget.trans (min_le_left _ _)
  have hDebt : D * (∑ j ∈ range (L + 1), β j) ≤ α₀ / 4 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 4 * D)).mp (hBudget.trans (min_le_right _ _))
    nlinarith
  have hFloor (n : ℝ) (r : ℕ) (hn : (M : ℝ) ≤ n) (hr : r ≤ L) :
      α₀ / 2 ≤ globalGeometryFloor α₀ h D β n r := by
    have hp : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range (L + 1), β j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intro j _ _; exact hβ j)
    exact globalGeometryFloor_half_le α₀ D h β n r hα.le (hPower.trans hn)
      ((mul_le_mul_of_nonneg_left hp hD.le).trans hDebt)
  obtain ⟨Ns, hNs, hStep⟩ := exists_global_clean_geometric_step α₀ q D h (2 * M) L β
    hα hq hq32 hh (by omega) hD.le hβ hDebt
  let t : ℝ := max Ns M
  have ht : 0 < t := hNs.trans_le (le_max_left _ _)
  refine ⟨M, 2 * M, hMreq, hM1, t, ht, ?_⟩
  have hAll : ∀ n : ℕ, ∀ {V : Type} [Fintype V] (H : Host V I), Fintype.card V = n →
      2 * M ≤ n → physicalPotential H F T ≤ L →
      CommonNbrCond H F (globalGeometryFloor α₀ h D β n (physicalPotential H F T)) →
      CleanHingeCond H F (globalGeometryFloor α₀ h D β n (physicalPotential H F T)) h →
      Nonempty (IntrinsicPreparedVortex F α₀ q β h N M d T t H) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ H hcard hMin hp h3 hClean
      have hMcur : M ≤ Fintype.card V := by omega
      have hMcurR : (M : ℝ) ≤ Fintype.card V := by exact_mod_cast hMcur
      have hFloorCur := hFloor (Fintype.card V) (physicalPotential H F T) hMcurR hp
      rw [← hcard] at h3 hClean
      obtain ⟨r, hr, A, hpEnter, hpA, hCost, hHalf, h3A, hCleanA, hPc⟩ :=
        hPrepare β hβ hBudgetPrep H F _ (hMprep.trans hMcur) (by linarith) h3 hClean
      letI : DecidableEq (Survivors A) := Classical.decEq _
      have hMA : M ≤ Fintype.card (Survivors A) := by
        have hnR : (2 : ℝ) * M ≤ Fintype.card V := by exact_mod_cast (show 2 * M ≤ Fintype.card V by omega)
        have hOut : (M : ℝ) ≤ Fintype.card (Survivors A) := by linarith
        exact_mod_cast hOut
      have hMAR : (M : ℝ) ≤ Fintype.card (Survivors A) := by exact_mod_cast hMA
      have hSize : Fintype.card (Survivors A) ≤ Fintype.card V := by
        have hc := card_survivors_add_card A
        omega
      have hSizeR : (Fintype.card (Survivors A) : ℝ) ≤ Fintype.card V := by exact_mod_cast hSize
      have hAPos : (0 : ℝ) < Fintype.card (Survivors A) := by
        exact_mod_cast (show 0 < Fintype.card (Survivors A) by omega)
      have hTrim := globalGeometryFloor_trim α₀ D h β hα.le (Fintype.card V)
        (Fintype.card (Survivors A)) (physicalPotential H F T) r hAPos hSizeR
      have h3Prepared := commonNbrCond_mono h3A hTrim
      have hCleanPrepared := hCleanA.mono hTrim
      have hPreparedFloor := hFloor (Fintype.card (Survivors A)) r hMAR hr
      have h3base := commonNbrCond_mono h3Prepared (show α₀ / 4 ≤ _ by linarith)
      have hCleanbase := hCleanPrepared.mono (show α₀ / 4 ≤ _ by linarith)
      let node : IntrinsicPreparedLayer H F α₀ β h N M d T :=
        ⟨A, r, hr, hpEnter, hpA, hCost, h3base, hCleanbase, hPc, hMA⟩
      by_cases hStop : (Fintype.card (Survivors A) : ℝ) ≤ t
      · exact ⟨.terminal node hStop⟩
      · have hnStep : Ns ≤ (Fintype.card (Survivors A) : ℝ) :=
          (le_max_left _ _).trans (lt_of_not_ge hStop).le
        obtain ⟨W, hWmin, hShrink, h3W, hCleanW, hInter⟩ :=
          hStep (restrictedHost H A) F r hr hnStep h3Prepared hCleanPrepared
        have hWM : M ≤ W.card := by omega
        have hWMR : (M : ℝ) ≤ W.card := by exact_mod_cast hWM
        have hChildFloor := hFloor W.card r hWMR hr
        have hChild3 := commonNbrCond_mono h3W (show α₀ / 4 ≤ _ by linarith)
        have hChild4 := hingeCond_mono hCleanW.hingeCond (show α₀ / 4 ≤ _ by linarith)
        have hChildOrder : nPrep ≤ Fintype.card (Survivors (univ \ W)) := by
          rw [CorePaid.card_survivors_compl]
          exact hMprep.trans hWM
        have hChildQuot := hQuot (restrictedHost (restrictedHost H A) (univ \ W)) F
          hChildOrder hChild3 hChild4
        have hChildIndex := physicalPotential_le _ F d T hChildQuot.1 hChildQuot.2
        have hParentQuot := hQuot (restrictedHost H A) F (hMprep.trans hMA) h3base hCleanbase.hingeCond
        have hw1 : 3 < κ * W.card := hW1.trans_le (mul_le_mul_of_nonneg_left hWMR hκ.le)
        have hw2 : (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 ≤ κ / 2 * W.card :=
          hW2.trans (mul_le_mul_of_nonneg_left hWMR (by positivity))
        have hNext := physicalPotential_sample_mono (restrictedHost H A) F W κ h T hκ
          hInter hw1 hw2 hParentQuot.2
        rw [hpA] at hNext
        have hPrefix : (∑ j ∈ range r, β j) ≤
            ∑ j ∈ range (physicalPotential (restrictedHost (restrictedHost H A) (univ \ W)) F T), β j :=
          sum_le_sum_of_subset_of_nonneg (range_mono hNext) (by intro j _ _; exact hβ j)
        have hWeaken : globalGeometryFloor α₀ h D β W.card
            (physicalPotential (restrictedHost (restrictedHost H A) (univ \ W)) F T) ≤
            globalGeometryFloor α₀ h D β W.card r := by
          dsimp [globalGeometryFloor]
          nlinarith [mul_le_mul_of_nonneg_left hPrefix hD.le]
        have hShrinkA : 16 * W.card ≤ Fintype.card (Survivors A) := by
          simpa only [← Nat.card_eq_fintype_card] using hShrink
        have hWlt : W.card < n := by omega
        obtain ⟨tail⟩ := ih W.card hWlt (restrictedHost (restrictedHost H A) (univ \ W))
          (CorePaid.card_survivors_compl W) hWmin hChildIndex
          (by simpa only [CorePaid.card_survivors_compl] using commonNbrCond_mono h3W hWeaken)
          (by simpa only [CorePaid.card_survivors_compl] using hCleanW.mono hWeaken)
        exact ⟨.descend node W hWmin hShrink hInter hNext tail⟩
  intro V _ H hn h3 hClean
  have hOrder : nPrep ≤ Fintype.card V := hMprep.trans (by omega)
  have hBounds := hQuot H F hOrder
    (commonNbrCond_mono h3 (show α₀ / 4 ≤ α₀ by linarith))
    (hingeCond_mono hClean.hingeCond (show α₀ / 4 ≤ α₀ by linarith))
  have hp := physicalPotential_le H F d T hBounds.1 hBounds.2
  have hNonneg : 0 ≤ D * ∑ j ∈ range (physicalPotential H F T), β j :=
    mul_nonneg hD.le (sum_nonneg (by intro j _; exact hβ j))
  have hFloorLe : globalGeometryFloor α₀ h D β (Fintype.card V) (physicalPotential H F T) ≤ α₀ := by
    exact (sub_le_self _ hNonneg).trans (geometryFloor_le α₀ h _ hα.le)
  exact hAll (Fintype.card V) H rfl hn hp (commonNbrCond_mono h3 hFloorLe) (hClean.mono hFloorLe)

#print axioms IntrinsicPreparedVortex.terminalOrder_bounds
#print axioms exists_intrinsic_prepared_vortex
end TypedTriangle.Vortex
