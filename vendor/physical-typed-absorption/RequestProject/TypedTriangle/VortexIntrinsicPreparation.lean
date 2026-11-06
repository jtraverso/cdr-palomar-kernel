/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexIntrinsicPreparedCore
public import RequestProject.TypedTriangle.VortexCleanVertexDeletion
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The concrete intrinsic preparation step, including clean H4 at fixed
order and PreparedCore on the same actual surviving host. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex

theorem intrinsic_preparation_with_clean_geometry (α : ℝ) (h : ℕ) (hα : 0 < α) :
    let D : ℝ := 2 ^ Nat.choose h 2
    ∃ ε : ℝ, 0 < ε ∧ ∃ d T : ℕ, 1 ≤ T ∧ ∀ N : ℕ, ∃ n₀ : ℕ,
      (∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        Module.finrank ℤ (physQuot H F) ≤ d ∧
          Nat.card (Submodule.torsion ℤ (physQuot H F)) ≤ T) ∧
      let L := d + (d + 1) * Nat.log 2 T
      ∀ β : ℕ → ℝ, (∀ j, 0 ≤ β j) → (∑ j ∈ range (L + 1), β j) ≤ ε →
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (γ : ℝ),
        n₀ ≤ Fintype.card V → 2 * α ≤ γ →
        CommonNbrCond H F γ → CleanHingeCond H F γ h →
        ∃ r ≤ L, ∃ A : Finset V,
          physicalPotential H F T ≤ r ∧ physicalPotential (restrictedHost H A) F T = r ∧
          let debt := (∑ j ∈ range r, β j) - ∑ j ∈ range (physicalPotential H F T), β j
          (A.card : ℝ) ≤ Fintype.card V * debt ∧
          (Fintype.card V : ℝ) / 2 ≤ Fintype.card (Survivors A) ∧
          CommonNbrCond (restrictedHost H A) F (γ - D * debt) ∧
          CleanHingeCond (restrictedHost H A) F (γ - D * debt) h ∧
          Dispersal.PreparedCore (restrictedHost H A).G (restrictedHost H A).lab
            F (α / 2) h N (β r) := by
  dsimp only
  let D : ℝ := 2 ^ Nat.choose h 2
  have hD : 0 < D := by positivity
  have hD1 : 1 ≤ D := one_le_pow₀ (by norm_num)
  obtain ⟨εEntry, hεEntry, d, T, nEntry, hT, hQuot, hEntry⟩ := intrinsic_first_entry_of_H3H4 α h hα
  obtain ⟨εPc, hεPc, hPcAll⟩ := preparedCore_on_stable_host α h hα
  let ε : ℝ := min (min εEntry εPc) (min (1 / 2) (α / (2 * D)))
  have hε : 0 < ε := lt_min (lt_min hεEntry hεPc) (lt_min (by norm_num) (by positivity))
  refine ⟨ε, hε, d, T, hT, ?_⟩
  intro N
  obtain ⟨nPc, hPc⟩ := hPcAll N
  let n₀ := max nEntry (2 * max nEntry nPc)
  refine ⟨n₀, ?_, ?_⟩
  · intro V I _ H F hn h3 h4
    exact hQuot H F ((le_max_left _ _).trans hn) h3 h4
  let L := d + (d + 1) * Nat.log 2 T
  intro β hβ hBudget V I _ H F γ hn hγ h3 hClean
  have h3base := commonNbrCond_mono h3 (show α ≤ γ by linarith)
  have h4base := hingeCond_mono hClean.hingeCond (show α ≤ γ by linarith)
  have hBudgetEntry : (∑ j ∈ range (L + 1), β j) ≤ εEntry :=
    hBudget.trans ((min_le_left _ _).trans (min_le_left _ _))
  obtain ⟨r, hr, A, hp₀r, hpA, hA, hStable⟩ :=
    hEntry β hβ hBudgetEntry H F ((le_max_left _ _).trans hn) h3base h4base
  let debt := (∑ j ∈ range r, β j) - ∑ j ∈ range (physicalPotential H F T), β j
  have hDebt0 : 0 ≤ debt := by
    have hs := sum_le_sum_of_subset_of_nonneg (range_mono hp₀r) (by intro j _ _; exact hβ j)
    dsimp [debt]
    linarith
  have hDebtε : debt ≤ ε := by
    have hs : (∑ j ∈ range r, β j) ≤ ∑ j ∈ range (L + 1), β j :=
      sum_le_sum_of_subset_of_nonneg (range_mono (show r ≤ L + 1 by omega))
        (by intro j _ _; exact hβ j)
    have hPrior : 0 ≤ ∑ j ∈ range (physicalPotential H F T), β j :=
      sum_nonneg (by intro j _; exact hβ j)
    dsimp [debt]
    linarith
  have hLoss : D * debt ≤ α / 2 := by
    have hεcap : ε ≤ α / (2 * D) := (min_le_right _ _).trans (min_le_right _ _)
    have hc := (le_div_iff₀ (by positivity : 0 < 2 * D)).mp (hDebtε.trans hεcap)
    nlinarith
  have hResultNonneg : 0 ≤ γ - D * debt := by linarith
  have hCleanA := clean_hinge_after_vertex_deletion H F γ (D * debt) h A hClean
    hResultNonneg (by
      have hs := mul_le_mul_of_nonneg_right hA hD.le
      dsimp only [D] at hs ⊢
      nlinarith)
  have h3A := commonNbr_after_vertex_deletion_additive H F γ (D * debt) A h3
    hResultNonneg (by
      have hd := mul_le_mul_of_nonneg_right hD1 hDebt0
      have hs := mul_le_mul_of_nonneg_right hd (by positivity : (0 : ℝ) ≤ Fintype.card V)
      nlinarith [hA])
  have hαA : α ≤ γ - D * debt := by linarith
  have h3Abase := commonNbrCond_mono h3A hαA
  have h4Abase := hingeCond_mono hCleanA.hingeCond hαA
  have hAhalf : (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
    have hεhalf : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hs := mul_le_mul_of_nonneg_left (hDebtε.trans hεhalf)
      (by positivity : (0 : ℝ) ≤ Fintype.card V)
    nlinarith [hA]
  have hcR : (Fintype.card (Survivors A) : ℝ) + A.card = Fintype.card V := by
    exact_mod_cast card_survivors_add_card A
  have hHalf : (Fintype.card V : ℝ) / 2 ≤ Fintype.card (Survivors A) := by linarith
  have hLarge : max nEntry nPc ≤ Fintype.card (Survivors A) := by
    have hIn : 2 * max nEntry nPc ≤ Fintype.card V := (le_max_right _ _).trans hn
    have hInR : (2 : ℝ) * max nEntry nPc ≤ Fintype.card V := by exact_mod_cast hIn
    have hOut : ((max nEntry nPc : ℕ) : ℝ) ≤ Fintype.card (Survivors A) := by linarith
    exact_mod_cast hOut
  have hβrε : β r ≤ ε := by
    have hmem : r ∈ range (L + 1) := mem_range.mpr (by omega)
    exact (single_le_sum (by intro j _; exact hβ j) hmem).trans hBudget
  have hβrPc : β r ≤ εPc := hβrε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hActualStable := intrinsic_stability_on_actual_host H F A (β r) hStable
  have hPrepared := hPc (β r) hβrPc (restrictedHost H A) F
    ((le_max_right _ _).trans hLarge) h3Abase h4Abase hActualStable
  exact ⟨r, hr, A, hp₀r, hpA, hA, hHalf, h3A, hCleanA, hPrepared⟩

#print axioms intrinsic_preparation_with_clean_geometry
end TypedTriangle.Vortex
