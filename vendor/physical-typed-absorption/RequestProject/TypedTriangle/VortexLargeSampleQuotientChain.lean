/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NestedVertexQuotients
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The quotient-map part of a large vertex sample is paid one small deletion
at a time. This requires H3/H4 on the *true surviving vertex type* at every
intermediate step. Geometry on `vertexDeleted H Z` would be false because its
deleted vertices remain in the type as isolated roots. The intermediate
geometry must be established by witnesses anchored in the final window for
all roots of the parent. No bound on the total deleted set is assumed here. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem quotient_step_surjective_of_intermediate_geometry
    {V I : Type*} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (Z B : Finset V) (α : ℝ) (h : ℕ)
    (hα : 0 < α)
    (hH3 : CommonNbrCond (restrictedHost H Z) F α)
    (hH4 : HingeCond (restrictedHost H Z) F α h)
    (hw1 : (B.card : ℝ) + 2 < α * Fintype.card (Survivors Z))
    (hw2 : ((B.card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤
      α / 2 * Fintype.card (Survivors Z)) :
    Function.Surjective
      (quotMap (F := F) (vertexDeleted_antitone H Finset.subset_union_left)
        (show (vertexDeleted H (Z ∪ B)).lab = (vertexDeleted H Z).lab from rfl)) := by
  let D := B.subtype (fun v => v ∉ Z)
  have hDc : D.card ≤ B.card := by
    dsimp [D]
    rw [Finset.card_subtype]
    exact Finset.card_filter_le _ _
  have hDcR : (D.card : ℝ) ≤ B.card := by exact_mod_cast hDc
  have hw1' : (D.card : ℝ) + 2 < α * Fintype.card (Survivors Z) := by linarith
  have hw2' : ((D.card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤
      α / 2 * Fintype.card (Survivors Z) := by
    have hp : (0 : ℝ) ≤ 2 ^ Nat.choose h 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right (add_le_add_right hDcR h) hp
    nlinarith
  have hs := quotMap_vertexDeleted_surjective hα hH3 hH4 D hw1' hw2'
  have hin : Function.Surjective
      (quotMap (F := F) (restrictedHost_mono (vertexDeleted_le H B) Z)
        (restrictedHost_labels rfl Z)) := by
    exact (quotMap_surjective_congr_source
      (restrictedHost_vertexDeleted H Z B).symm _ _ _ _).1 hs
  have hout := quotMap_deleted_surjective_of_restricted F (vertexDeleted_le H B) rfl Z hin
  have heq' : vertexDeleted H (Z ∪ B) = vertexDeleted (vertexDeleted H B) Z := by
    rw [vertexDeleted_vertexDeleted]
  exact (quotMap_surjective_congr_source (F := F) heq' _ _ _ _).2 hout

/-- Uniform geometry on all intermediate hosts turns arbitrary cumulative
deletion into a chain of surjective quotient maps. The `B i` are individual
small payments; their union may be a fixed positive fraction of the parent. -/
theorem quotient_chain_surjective_of_intermediate_geometry
    {V I : Type*} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (Z B : ℕ → Finset V) (m : ℕ) (α : ℝ) (h : ℕ)
    (hZ : ∀ i, Z (i + 1) = Z i ∪ B i)
    (hα : 0 < α)
    (hGeom : ∀ i < m,
      CommonNbrCond (restrictedHost H (Z i)) F α ∧
      HingeCond (restrictedHost H (Z i)) F α h)
    (hw1 : ∀ i < m, ((B i).card : ℝ) + 2 <
      α * Fintype.card (Survivors (Z i)))
    (hw2 : ∀ i < m, (((B i).card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤
      α / 2 * Fintype.card (Survivors (Z i))) :
    ∀ i < m, Function.Surjective
      (quotMap (F := F)
        (vertexDeleted_antitone H (by rw [hZ i]; exact Finset.subset_union_left))
        (show (vertexDeleted H (Z (i + 1))).lab =
          (vertexDeleted H (Z i)).lab from rfl)) := by
  intro i hi
  obtain ⟨h3,h4⟩ := hGeom i hi
  have hs := quotient_step_surjective_of_intermediate_geometry H F
    (Z i) (B i) α h hα h3 h4 (hw1 i hi) (hw2 i hi)
  have heq : vertexDeleted H (Z (i + 1)) =
      vertexDeleted H (Z i ∪ B i) := congrArg (vertexDeleted H) (hZ i)
  exact (quotMap_surjective_congr_source (F := F) heq _ _ _ _).2 hs

/-- The global strict-change budget survives a large sampled deletion once
every intermediate host has uniform geometry. The number of small deletion
steps may grow with the order; only non-isomorphisms are bounded. -/
theorem quotient_chain_strict_count_of_intermediate_geometry
    {V I : Type*} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (Z B : ℕ → Finset V) (m : ℕ) (α : ℝ) (h d T : ℕ)
    (hZ : ∀ i, Z (i + 1) = Z i ∪ B i)
    (hα : 0 < α)
    (hGeom : ∀ i < m,
      CommonNbrCond (restrictedHost H (Z i)) F α ∧
      HingeCond (restrictedHost H (Z i)) F α h)
    (hw1 : ∀ i < m, ((B i).card : ℝ) + 2 <
      α * Fintype.card (Survivors (Z i)))
    (hw2 : ∀ i < m, (((B i).card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤
      α / 2 * Fintype.card (Survivors (Z i)))
    (hd : ∀ i ≤ m, Module.finrank ℤ
      (physQuot (vertexDeleted H (Z i)) F) ≤ d)
    (hT : ∀ i ≤ m, Nat.card
      (Submodule.torsion ℤ (physQuot (vertexDeleted H (Z i)) F)) ≤ T) :
    ((range m).filter fun i => ¬ Function.Injective
      (quotMap (F := F)
        (vertexDeleted_antitone H (by rw [hZ i]; exact Finset.subset_union_left))
        (show (vertexDeleted H (Z (i + 1))).lab =
          (vertexDeleted H (Z i)).lab from rfl))).card ≤
      d + (d + 1) * Nat.log 2 T := by
  let Hs : ℕ → Host V I := fun i => vertexDeleted H (Z i)
  let hG : ∀ i, (Hs (i + 1)).G ≤ (Hs i).G := fun i =>
    vertexDeleted_antitone H (by rw [hZ i]; exact Finset.subset_union_left)
  have hs := quotient_chain_surjective_of_intermediate_geometry H F Z B m α h
    hZ hα hGeom hw1 hw2
  exact physical_chain_strict_count Hs F hG (fun _ => rfl) m d T hs hd hT

#print axioms quotient_step_surjective_of_intermediate_geometry
#print axioms quotient_chain_surjective_of_intermediate_geometry
#print axioms quotient_chain_strict_count_of_intermediate_geometry

end TypedTriangle.Vortex
