/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexCleanGeometricStep
public import RequestProject.TypedTriangle.VortexLargeSampleQuotientChain
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A large sampled deletion gives one genuine surjective physical quotient
map. Intermediate anchored geometry pays the deletion one vertex at a time;
the resulting map can then be counted as a single global event. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex

private theorem quotMap_comp_apply {V I : Type*} [Fintype V]
    {H K L : Host V I} {F : Set (Multiset I)}
    (hHK : H.G ≤ K.G) (hKL : K.G ≤ L.G)
    (hHL : H.G ≤ L.G) (hlHK : H.lab = K.lab) (hlKL : K.lab = L.lab)
    (hlHL : H.lab = L.lab) (x : physQuot H F) :
    quotMap (F := F) hKL hlKL (quotMap (F := F) hHK hlHK x) =
      quotMap (F := F) hHL hlHL x := by
  induction x using Submodule.Quotient.induction_on with
  | H x => rfl

private theorem quotMap_surjective_comp {V I : Type*} [Fintype V]
    {H K L : Host V I} {F : Set (Multiset I)}
    (hHK : H.G ≤ K.G) (hKL : K.G ≤ L.G)
    (hHL : H.G ≤ L.G) (hlHK : H.lab = K.lab) (hlKL : K.lab = L.lab)
    (hlHL : H.lab = L.lab)
    (h1 : Function.Surjective (quotMap (F := F) hHK hlHK))
    (h2 : Function.Surjective (quotMap (F := F) hKL hlKL)) :
    Function.Surjective (quotMap (F := F) hHL hlHL) := by
  intro y
  obtain ⟨z, hz⟩ := h2 y
  obtain ⟨x, hx⟩ := h1 z
  refine ⟨x, ?_⟩
  rw [← quotMap_comp_apply hHK hKL hHL hlHK hlKL hlHL x, hx, hz]

theorem quotient_sample_surjective_of_intermediate_geometry
    {V I : Type*} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (W : Finset V) (α : ℝ) (h : ℕ) (hα : 0 < α)
    (hGeom : ∀ U : Finset V, W ⊆ U →
      CommonNbrCond (restrictedHost H (univ \ U)) F α ∧
      HingeCond (restrictedHost H (univ \ U)) F α h)
    (hw1 : 3 < α * W.card)
    (hw2 : (1 + (h : ℝ)) * 2 ^ Nat.choose h 2 ≤ α / 2 * W.card) :
    Function.Surjective
      (quotMap (F := F) (vertexDeleted_le H (univ \ W)) rfl) := by
  have hAll : ∀ A : Finset V, A ⊆ univ \ W →
      Function.Surjective (quotMap (F := F) (vertexDeleted_le H A) rfl) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro _
      have heq : vertexDeleted H ∅ = H := by
        have hg : (vertexDeleted H ∅).G = H.G := by
          ext u v
          simp [vertexDeleted]
        exact congrArg (fun G => (⟨G, H.lab⟩ : Host V I)) hg
      have hSelf : Function.Surjective
          (quotMap (F := F) (show H.G ≤ H.G from le_rfl) rfl) := by
        intro y
        refine ⟨y, ?_⟩
        induction y using Submodule.Quotient.induction_on with
        | H y => rfl
      exact (quotMap_surjective_congr_source heq _ _ _ _).2 hSelf
    | @insert a A ha ih =>
      intro hA
      have hAsub : A ⊆ univ \ W := (subset_insert _ _).trans hA
      have hWU : W ⊆ univ \ A := by
        intro v hv
        refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
        intro hvA
        exact (mem_sdiff.mp (hAsub hvA)).2 hv
      have hGeoA := hGeom (univ \ A) hWU
      have heqU : univ \ (univ \ A) = A := by ext v; simp
      rw [heqU] at hGeoA
      have hWcard : W.card ≤ Fintype.card (Survivors A) := by
        have hc := card_le_card hWU
        have hSurv := card_survivors_add_card A
        have hComplement := card_sdiff_add_card_eq_card (subset_univ A)
        rw [card_univ] at hComplement
        omega
      have hWcardR : (W.card : ℝ) ≤ Fintype.card (Survivors A) := by exact_mod_cast hWcard
      have hWin1 : (({a} : Finset V).card : ℝ) + 2 <
          α * Fintype.card (Survivors A) := by
        simp only [card_singleton, Nat.cast_one]
        nlinarith
      have hWin2 : ((({a} : Finset V).card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤
          α / 2 * Fintype.card (Survivors A) := by
        simp only [card_singleton, Nat.cast_one]
        exact hw2.trans (mul_le_mul_of_nonneg_left hWcardR (by positivity))
      have hStep := quotient_step_surjective_of_intermediate_geometry H F A {a}
        α h hα hGeoA.1 hGeoA.2 hWin1 hWin2
      have heqInsert : A ∪ {a} = insert a A := by ext v; simp
      have hG : (vertexDeleted H (insert a A)).G ≤ (vertexDeleted H A).G :=
        vertexDeleted_antitone H (subset_insert _ _)
      have hStep' : Function.Surjective (quotMap (F := F) hG rfl) := by
        exact (quotMap_surjective_congr_source (congrArg (vertexDeleted H) heqInsert)
          _ _ _ _).1 hStep
      exact quotMap_surjective_comp hG (vertexDeleted_le H A)
        (vertexDeleted_le H (insert a A)) rfl rfl rfl hStep' (ih hAsub)
  exact hAll (univ \ W) subset_rfl

#print axioms quotient_sample_surjective_of_intermediate_geometry
end TypedTriangle.Vortex
