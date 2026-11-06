/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexPhysicalPotential
public import RequestProject.TypedTriangle.UniformVertexChains
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Intrinsic first entry. The radius index is the potential of the physical
quotient, not a local counter restarted at each level. A maximum over actual
vertex sets constructs the stable core from original H3--H4. Only radii
strictly between the entering and exiting intrinsic indices are charged. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex

private theorem radiusPrefix_mono (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j)
    {r s : ℕ} (hrs : r ≤ s) :
    (∑ j ∈ range r, β j) ≤ ∑ j ∈ range s, β j :=
  sum_le_sum_of_subset_of_nonneg (range_mono hrs) (by intro j _ _; exact hβ j)

/-- Original hypotheses construct quotient stability at its actual global
index. The deletion budget begins at the entering index, so it can be
summed over arbitrary many sampled levels without restarting the budget. -/
theorem intrinsic_first_entry_of_H3H4 (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ d T n₀ : ℕ, 1 ≤ T ∧
      (∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        Module.finrank ℤ (physQuot H F) ≤ d ∧
          Nat.card (Submodule.torsion ℤ (physQuot H F)) ≤ T) ∧
      let L := d + (d + 1) * Nat.log 2 T
      ∀ β : ℕ → ℝ, (∀ j, 0 ≤ β j) → (∑ j ∈ range (L + 1), β j) ≤ ε →
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        ∃ r ≤ L, ∃ A : Finset V,
          physicalPotential H F T ≤ r ∧
          physicalPotential (restrictedHost H A) F T = r ∧
          (A.card : ℝ) ≤ Fintype.card V *
            ((∑ j ∈ range r, β j) - ∑ j ∈ range (physicalPotential H F T), β j) ∧
          ∀ B : Finset V, (B.card : ℝ) ≤ β r * Fintype.card (Survivors A) →
            Function.Injective (nestedVertexQuotMap H F A B) := by
  obtain ⟨ε₁, hε₁, d₁, T₁, N₁, hT₁, hControl⟩ := physical_vertex_chain_control α h hα
  obtain ⟨δ, hδ, d, T, N₂, hT, hBounds⟩ :=
    physQuot_vertexDeleted_bounds_of_original_geometry α h hα
  let ε := min ε₁ δ
  have hε : 0 < ε := lt_min hε₁ hδ
  refine ⟨ε, hε, d, T, max N₁ N₂, hT, ?_, ?_⟩
  · intro V I _ H F hn h3 h4
    have heq : vertexDeleted H ∅ = H := by
      have hg : (vertexDeleted H ∅).G = H.G := by ext u v; simp [vertexDeleted]
      exact congrArg (fun G => (⟨G, H.lab⟩ : Host V I)) hg
    have hb := hBounds H F ∅ ((le_max_right _ _).trans hn) h3 h4
      (by simp only [card_empty, Nat.cast_zero]; positivity)
    exact (congrArg (fun K : Host V I => Module.finrank ℤ (physQuot K F) ≤ d ∧
      Nat.card (Submodule.torsion ℤ (physQuot K F)) ≤ T) heq).mp hb
  dsimp only
  let L := d + (d + 1) * Nat.log 2 T
  intro β hβ hBudget V I _ H F hn h3 h4
  let n : ℝ := Fintype.card V
  let p₀ := physicalPotential H F T
  let p : Finset V → ℕ := fun A => physicalPotential (vertexDeleted H A) F T
  let S : ℕ → ℝ := fun r => ∑ j ∈ range r, β j
  have hn0 : 0 ≤ n := by positivity
  have hS0 (r : ℕ) : 0 ≤ S r := sum_nonneg (by intro j _; exact hβ j)
  have hSmono {r s : ℕ} (hrs : r ≤ s) : S r ≤ S s := radiusPrefix_mono β hβ hrs
  have hBounds' (A : Finset V) (hA : (A.card : ℝ) ≤ ε * n) :=
    hBounds H F A ((le_max_right _ _).trans hn) h3 h4
      (hA.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0))
  have hSurj (A B : Finset V) (hA : (A.card : ℝ) ≤ ε * n)
      (hB : (B.card : ℝ) ≤ ε * n) : Function.Surjective (nestedVertexQuotMap H F A B) :=
    (hControl H F ((le_max_left _ _).trans hn) h3 h4).1 A B
      (hA.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0))
      (hB.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0))
  have hpBound (A : Finset V) (hA : (A.card : ℝ) ≤ ε * n) : p A ≤ L :=
    physicalPotential_le _ F d T (hBounds' A hA).1 (hBounds' A hA).2
  have heq : vertexDeleted H ∅ = H := by
    have hg : (vertexDeleted H ∅).G = H.G := by ext u v; simp [vertexDeleted]
    exact congrArg (fun G => (⟨G, H.lab⟩ : Host V I)) hg
  have hpEmpty : p ∅ = p₀ := by dsimp [p, p₀]; rw [heq]
  have hp₀ : p₀ ≤ L := by
    rw [← hpEmpty]
    exact hpBound ∅ (by simp only [card_empty, Nat.cast_zero]; positivity)
  let C := univ.powerset.filter (fun A : Finset V =>
    p₀ ≤ p A ∧ p A ≤ L ∧ (A.card : ℝ) ≤ n * (S (p A) - S p₀))
  have hEmpty : ∅ ∈ C := by
    simp only [C, mem_filter, mem_powerset, empty_subset, hpEmpty,
      le_refl, hp₀, card_empty, Nat.cast_zero, sub_self, mul_zero, and_self]
  obtain ⟨A, hAC, hMax⟩ := Finset.exists_max_image C p ⟨∅, hEmpty⟩
  obtain ⟨hp₀A, hpAL, hA⟩ := (mem_filter.mp hAC).2
  have hAsmall : (A.card : ℝ) ≤ ε * n := by
    have hSum := hSmono (show p A ≤ L + 1 by omega)
    have hTot : S (L + 1) ≤ ε := hBudget
    have hCap := mul_le_mul_of_nonneg_left hSum hn0
    have hCap' := mul_le_mul_of_nonneg_left hTot hn0
    have hPrior := mul_nonneg hn0 (hS0 p₀)
    nlinarith
  refine ⟨p A, hpAL, A, hp₀A, (physicalPotential_vertexDeleted_eq H F A T).symm, hA, ?_⟩
  intro B hB
  by_contra hBad
  have hSurv : (Fintype.card (Survivors A) : ℝ) ≤ n := by
    have hc := card_survivors_add_card A
    have hcR : (Fintype.card (Survivors A) : ℝ) + A.card = n := by
      dsimp [n]
      exact_mod_cast hc
    have hANonneg : (0 : ℝ) ≤ A.card := by positivity
    linarith
  have hBroot : (B.card : ℝ) ≤ β (p A) * n :=
    hB.trans (mul_le_mul_of_nonneg_left hSurv (hβ _))
  have hIndex : p A + 1 ≤ L + 1 := by omega
  have hStepPrefix : S (p A) + β (p A) ≤ S (L + 1) := by
    simpa only [S, sum_range_succ] using hSmono hIndex
  have hTot : S (L + 1) ≤ ε := hBudget
  have hBsmall : (B.card : ℝ) ≤ ε * n := by
    have hRadius : β (p A) ≤ ε := by linarith [hS0 (p A)]
    exact hBroot.trans (mul_le_mul_of_nonneg_right hRadius hn0)
  have hUnion : ((A ∪ B).card : ℝ) ≤ (A.card : ℝ) + B.card := by
    exact_mod_cast card_union_le A B
  have hABsmall : ((A ∪ B).card : ℝ) ≤ ε * n := by
    have hCap := mul_le_mul_of_nonneg_left (hStepPrefix.trans hTot) hn0
    have hPrior := mul_nonneg hn0 (hS0 p₀)
    nlinarith
  have hStrict : p A < p (A ∪ B) :=
    physicalPotential_map_strict F T
      (vertexDeleted_antitone H subset_union_left) rfl
      (hSurj A B hAsmall hBsmall) (hBounds' A hAsmall).2 hBad
  have hpABL : p (A ∪ B) ≤ L := hpBound (A ∪ B) hABsmall
  have hPrefix : S (p A) + β (p A) ≤ S (p (A ∪ B)) := by
    simpa only [S, sum_range_succ] using hSmono (show p A + 1 ≤ p (A ∪ B) by omega)
  have hABbudget : ((A ∪ B).card : ℝ) ≤ n * (S (p (A ∪ B)) - S p₀) := by
    have hCap := mul_le_mul_of_nonneg_left hPrefix hn0
    nlinarith
  have hABC : A ∪ B ∈ C := mem_filter.mpr
    ⟨mem_powerset.mpr (subset_univ _), hp₀A.trans hStrict.le, hpABL, hABbudget⟩
  have hContr := hMax (A ∪ B) hABC
  omega

#print axioms intrinsic_first_entry_of_H3H4
end TypedTriangle.Vortex
