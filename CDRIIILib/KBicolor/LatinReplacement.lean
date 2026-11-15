/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Counting

/-! # Latin replacements preserve occupied pairs and exact type counts

These are the geometric replacement steps for the exact-types/Pasch route.
No claim about the mixed Pasch terms is made here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor
open Finset TypedTriangle CDRBicolour.Absorption
variable {k n m : ℕ} {lab : Fin n → Fin k} {X Y : Fin k}
variable {r c s : Fin m → Fin n} (h : LatPlace lab X Y r c s)
include h

theorem card_latPackK (l : Fin m → Fin m → Fin m) : #(latPackK r c s l) = m^2 := by
  classical
  have hinj : Function.Injective (fun p : Fin m × Fin m =>
      ({r p.1, c p.2, s (l p.1 p.2)} : Finset (Fin n))) := by
    intro p q he
    obtain ⟨hi, hj, _⟩ := mem_tri_iffK h he
    exact Prod.ext hi hj
  rw [latPackK, card_image_of_injective _ hinj]
  simp [sq]

theorem labels_latPackK (l : Fin m → Fin m → Fin m) {T : Finset (Fin n)}
    (hT : T ∈ latPackK r c s l) : T.val.map lab = {X, X, Y} := by
  classical
  obtain ⟨⟨i, j⟩, _, rfl⟩ := mem_image.mp hT
  rw [map_triple_lab lab (h.rc i j) (h.rs i _) (h.cs j _), h.lr, h.lc, h.ls]

theorem typeCount_latPackK (l : Fin m → Fin m → Fin m) (A B : Fin k) (hAB : A ≠ B) :
    kTypeCount lab (latPackK r c s l) A B = if X = A ∧ Y = B then m^2 else 0 := by
  classical
  unfold kTypeCount
  by_cases hp : X = A ∧ Y = B
  · rcases hp with ⟨rfl, rfl⟩
    rw [if_pos ⟨rfl, rfl⟩, filter_eq_self.mpr (fun T hT => labels_latPackK h l hT)]
    exact card_latPackK h l
  · rw [if_neg hp]
    have hempty : ((latPackK r c s l).filter
        (fun T => T.val.map lab = {A, A, B})) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro T hT he
      exact hp (xxy_inj h.hXY hAB ((labels_latPackK h l hT).symm.trans he))
    rw [hempty, card_empty]

theorem latPackK_edges_subset (l l' : Fin m → Fin m → Fin m)
    (hl' : _root_.STS.IsLatin l') :
    (latPackK r c s l).biUnion triEdges ⊆ (latPackK r c s l').biUnion triEdges := by
  classical
  intro e he
  obtain ⟨T, hT, he⟩ := mem_biUnion.mp he
  obtain ⟨⟨i, j⟩, _, rfl⟩ := mem_image.mp hT
  rw [triEdges_triple (h.rc i j) (h.rs i _) (h.cs j _)] at he
  simp only [mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · refine mem_biUnion.mpr ⟨_, mem_image.mpr ⟨(i, j), mem_univ _, rfl⟩, ?_⟩
    rw [triEdges_triple (h.rc i j) (h.rs i _) (h.cs j _)]
    simp
  · obtain ⟨j', hj'⟩ := (hl'.1 i).2 (l i j)
    refine mem_biUnion.mpr ⟨_, mem_image.mpr ⟨(i, j'), mem_univ _, rfl⟩, ?_⟩
    rw [triEdges_triple (h.rc i j') (h.rs i _) (h.cs j' _)]
    simp [hj']
  · obtain ⟨i', hi'⟩ := (hl'.2 j).2 (l i j)
    refine mem_biUnion.mpr ⟨_, mem_image.mpr ⟨(i', j), mem_univ _, rfl⟩, ?_⟩
    rw [triEdges_triple (h.rc i' j) (h.rs i' _) (h.cs j _)]
    simp [hi']

theorem latPackK_edges_eq (l l' : Fin m → Fin m → Fin m)
    (hl : _root_.STS.IsLatin l) (hl' : _root_.STS.IsLatin l') :
    (latPackK r c s l).biUnion triEdges = (latPackK r c s l').biUnion triEdges :=
  Subset.antisymm (latPackK_edges_subset h l l' hl') (latPackK_edges_subset h l' l hl)

theorem typeCount_latPackK_eq (l l' : Fin m → Fin m → Fin m) (A B : Fin k) (hAB : A ≠ B) :
    kTypeCount lab (latPackK r c s l) A B = kTypeCount lab (latPackK r c s l') A B := by
  rw [typeCount_latPackK h l A B hAB, typeCount_latPackK h l' A B hAB]

end CDRBicolour.KBicolor
