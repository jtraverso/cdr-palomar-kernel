/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4ActualPackingEntry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Lift the SAME packing executed on the complement of a retained dense child
back to the parent host. No new packing is chosen and no child edges disappear. -/

open Finset Classical
noncomputable section
namespace TypedTriangle.StockEntry
variable {V I : Type*} [Fintype V]

theorem g4_lift_actual_complement (H : Host V I) (F : Set (Multiset I))
    (C : Finset (Sym2 V)) (hC : C ⊆ edges H)
    (Q : Finset (Finset V))
    (hQ : IsPacking (subHost H (edges H\C)) F Q)
    (R L : Finset (Sym2 V))
    (hLeft : edges (subHost H (edges H\C))\Q.biUnion triEdges = R∪L) :
    IsPacking H F Q ∧ Disjoint (Q.biUnion triEdges) C ∧
      edges H\Q.biUnion triEdges = C∪(R∪L) := by
  let E := edges H\C
  have hQH : IsPacking H F Q :=
    ⟨fun T hT => isAllowed_mono (subHost_le H _) rfl (hQ.1 T hT),hQ.2⟩
  have hQE : Q.biUnion triEdges ⊆ E := by
    change Q.biUnion triEdges ⊆ edges H\C
    rw [←Residual.edges_subHost_eq (sdiff_subset : edges H\C ⊆ edges H)]
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hQ.1 T hT) heT
  have hQC : Disjoint (Q.biUnion triEdges) C := by
    apply disjoint_left.mpr
    intro e heQ heC
    exact (mem_sdiff.mp (hQE heQ)).2 heC
  refine ⟨hQH,hQC,?_⟩
  rw [Residual.edges_subHost_eq (sdiff_subset : edges H\C ⊆ edges H)] at hLeft
  ext e
  have hCE : e ∈ C → e ∈ edges H := fun he => hC he
  have hQinE : e ∈ Q.biUnion triEdges → e ∈ E := fun he => hQE he
  simp only [mem_sdiff,mem_union] at hLeft ⊢
  change (e ∈ edges H ∧ e ∉ Q.biUnion triEdges) ↔
    e ∈ C ∨ e ∈ R ∨ e ∈ L
  have hleftE : (e ∈ edges H ∧ e ∉ C ∧ e ∉ Q.biUnion triEdges) ↔
      e ∈ R ∨ e ∈ L := by
    simpa only [E,mem_sdiff,mem_union,and_assoc] using (Finset.ext_iff.mp hLeft e)
  have hnoQC : e ∈ C → e ∉ Q.biUnion triEdges :=
    fun heC heQ => disjoint_left.mp hQC heQ heC
  tauto

end TypedTriangle.StockEntry
