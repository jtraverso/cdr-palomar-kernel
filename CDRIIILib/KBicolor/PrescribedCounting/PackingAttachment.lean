/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.PrescribedCounting.SparseHostCompletion

/-! # Attach a packing to a decomposition of its actual complement -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical TypedTriangle

theorem attach_to_host {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
    (B : Finset (Sym2 V)) (Q D : Finset (Finset V))
    (hB : B ⊆ edges H) (hQ : IsDecomposition H F B Q)
    (hD : IsDecomposition (residual H B) F (edges (residual H B)) D) :
    IsDecomposition H F (edges H) (D ∪ Q) ∧ Disjoint D Q := by
  have hD' : IsDecomposition H F (edges H \ B) D := by
    refine ⟨fun T hT => isAllowed_mono (subHost_le H _) rfl (hD.1 T hT),hD.2.1,?_⟩
    exact hD.2.2.trans (Residual.edges_subHost_eq sdiff_subset)
  have hd : Disjoint (edges H \ B) B := disjoint_left.mpr (fun _ he heB => (mem_sdiff.mp he).2 heB)
  have hnew := hD'.union hQ hd
  have hcover : (edges H \ B) ∪ B=edges H := sdiff_union_of_subset hB
  rw [hcover] at hnew
  refine ⟨hnew,disjoint_left.mpr ?_⟩
  intro T hTD hTQ
  obtain ⟨e,he⟩ := card_pos.mp (by rw [card_triEdges_three (hQ.1 T hTQ).1]; norm_num)
  exact disjoint_left.mp hd (hD'.subset hTD he) (hQ.subset hTQ he)

end CDRBicolour.KBicolor.PrescribedCounting
