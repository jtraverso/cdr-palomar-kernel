/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V28.PlacementWindow
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# Mode gluing for a finite catalogue of absorbers (V31)

All statements use the visible V28 `SparseEdge` interface (`IsDecomposition`, `IsAbsorber`).

* `isDecomposition_union`: decompositions of two edge-disjoint sets glue.
* `exists_isDecomposition_biUnion`: decompositions of a pairwise edge-disjoint finite family
  glue.
* `mode_gluing`: given absorbers `A i` for pieces `P i` (pieces may overlap arbitrarily) such
  that the `A i` are pairwise edge-disjoint and every `A i` is disjoint from the activated piece
  `P i₀`, the union `R = ⋃ A` together with `P i₀` has a permitted decomposition: `A i₀` is used
  in its full mode (`A i₀ ∪ P i₀`) and every other absorber in its empty mode (`A j`).
-/

open Finset

noncomputable section
open Classical

namespace S07V31

open TypedTriangle.SparseEdge S07V28

variable {V I : Type*}

lemma triEdges_subset_of_dec {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {X : Finset (Sym2 V)} {D : Finset (Finset V)} (h : IsDecomposition G lab F X D)
    {T : Finset V} (hT : T ∈ D) : triEdges T ⊆ X := by
  rw [← h.2.2]
  exact subset_biUnion_of_mem triEdges hT

/-- Decompositions of two edge-disjoint sets glue. -/
lemma isDecomposition_union {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {X Y : Finset (Sym2 V)} {D₁ D₂ : Finset (Finset V)}
    (h₁ : IsDecomposition G lab F X D₁) (h₂ : IsDecomposition G lab F Y D₂)
    (hXY : Disjoint X Y) : IsDecomposition G lab F (X ∪ Y) (D₁ ∪ D₂) := by
  refine ⟨fun T hT => ?_, ?_, ?_⟩
  · rcases mem_union.1 hT with h | h
    exacts [h₁.1 T h, h₂.1 T h]
  · rw [coe_union, Set.pairwiseDisjoint_union]
    refine ⟨h₁.2.1, h₂.2.1, fun T hT T' hT' _ => ?_⟩
    exact hXY.mono (triEdges_subset_of_dec h₁ hT) (triEdges_subset_of_dec h₂ hT')
  · rw [union_biUnion, h₁.2.2, h₂.2.2]

/-- Decompositions of a pairwise edge-disjoint finite family glue. -/
lemma exists_isDecomposition_biUnion {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {ι : Type*} (s : Finset ι) (X : ι → Finset (Sym2 V))
    (hX : ∀ i ∈ s, ∃ D, IsDecomposition G lab F (X i) D)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (X i) (X j)) :
    ∃ D, IsDecomposition G lab F (s.biUnion X) D := by
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simpa using isDecomposition_empty G lab F⟩
  | insert a s ha ih =>
    obtain ⟨D₁, h₁⟩ := hX a (mem_insert_self a s)
    obtain ⟨D₂, h₂⟩ := ih (fun i hi => hX i (mem_insert_of_mem hi))
      (fun i hi j hj hij => hdisj i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
    rw [biUnion_insert]
    refine ⟨D₁ ∪ D₂, isDecomposition_union h₁ h₂ ?_⟩
    rw [disjoint_biUnion_right]
    intro j hj
    exact hdisj a (mem_insert_self a s) j (mem_insert_of_mem hj) (fun h => ha (h ▸ hj))

/-- **Mode gluing.** Activate the absorber of the piece `P i₀`, keep all the other absorbers
in their empty modes. The pieces `P i` may overlap; only the activated one has to be disjoint
from the absorbers. -/
theorem mode_gluing {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {ι : Type*} [Fintype ι] (P A : ι → Finset (Sym2 V))
    (habs : ∀ i, IsAbsorber G lab F (P i) (A i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (i₀ : ι)
    (hP : ∀ j, Disjoint (A j) (P i₀)) :
    ∃ D, IsDecomposition G lab F (univ.biUnion A ∪ P i₀) D := by
  set X : ι → Finset (Sym2 V) := Function.update A i₀ (A i₀ ∪ P i₀) with hXdef
  have hXi₀ : X i₀ = A i₀ ∪ P i₀ := by simp [X]
  have hXj : ∀ j, j ≠ i₀ → X j = A j := fun j hj => by simp [X, hj]
  have heq : univ.biUnion A ∪ P i₀ = univ.biUnion X := by
    ext e
    simp only [mem_union, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro (⟨j, hj⟩ | he)
      · by_cases hji : j = i₀
        · subst hji; exact ⟨j, by rw [hXi₀]; exact mem_union_left _ hj⟩
        · exact ⟨j, by rw [hXj j hji]; exact hj⟩
      · exact ⟨i₀, by rw [hXi₀]; exact mem_union_right _ he⟩
    · rintro ⟨j, hj⟩
      by_cases hji : j = i₀
      · subst hji
        rw [hXi₀, mem_union] at hj
        rcases hj with h | h
        exacts [Or.inl ⟨j, h⟩, Or.inr h]
      · rw [hXj j hji] at hj; exact Or.inl ⟨j, hj⟩
  rw [heq]
  refine exists_isDecomposition_biUnion univ X (fun j _ => ?_) (fun i _ j _ hij => ?_)
  · by_cases hji : j = i₀
    · subst hji; rw [hXi₀]; exact (habs j).2.2
    · rw [hXj j hji]; exact (habs j).2.1
  · have key : ∀ a b, a ≠ b → a = i₀ → Disjoint (X a) (X b) := by
      intro a b hab ha
      subst ha
      rw [hXi₀, hXj b (Ne.symm hab)]
      exact disjoint_union_left.2 ⟨hdisj a b hab, (hP b).symm⟩
    by_cases hi : i = i₀
    · exact key i j hij hi
    · by_cases hj : j = i₀
      · exact (key j i (Ne.symm hij) hj).symm
      · rw [hXj i hi, hXj j hj]; exact hdisj i j hij

end S07V31
