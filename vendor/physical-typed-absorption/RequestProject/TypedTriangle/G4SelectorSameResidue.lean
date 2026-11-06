/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4DenseComplementLift
public import RequestProject.S07V42.PolarizeStep
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Apply the preconstructed positive selector to the leftover of the actual
packing. The universal mode is instantiated only after Q and its physical
remainder have been obtained; no alternate residue is substituted. -/

open Finset Classical
noncomputable section
namespace TypedTriangle.StockEntry
variable {V I : Type*} [Fintype V]

theorem g4_positive_payload_in_child (H : Host V I) (W : Finset V)
    (Y : Finset (Sym2 V)) (hYE : Y ⊆ edges H)
    (hW : ∀ e ∈ Y, ∀ v ∈ e, v ∈ W) :
    Y ⊆ SparseEdge.edges (S07V42.indG H.G W) := by
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    have hUV : H.G.Adj u v := by
      have hh := hYE he
      change s(u,v) ∈ SparseEdge.edges H.G at hh
      rw [SparseEdge.mem_edges,SimpleGraph.mem_edgeSet] at hh
      exact hh
    exact S07V42.mem_edges_indG hUV
      (hW s(u,v) he u (Sym2.mem_mk_left u v))
      (hW s(u,v) he v (Sym2.mem_mk_right u v))

theorem g4_selector_on_actual_remainder (H : Host V I) (F : Set (Multiset I))
    (X R : Finset (Sym2 V)) (hRE : R ⊆ edges H)
    (Q : Finset (Finset V)) (_hQ : IsPacking H F Q)
    (hQR : Disjoint (Q.biUnion triEdges) R)
    (hSub : edges H\(R∪Q.biUnion triEdges) ⊆ X)
    (hPhys : IsPhysical H F (edges H\(R∪Q.biUnion triEdges)))
    (hMode : ∀ L : Finset (Sym2 V), L ⊆ X → IsPhysical H F L →
      ∃ Ps Y : Finset (Sym2 V), R∪L=Ps∪Y ∧ Disjoint Ps Y ∧
        Basal H F Ps ∧ IsPhysical H F Y) :
    ∃ Ps Y : Finset (Sym2 V), Basal H F Ps ∧ IsPhysical H F Y ∧
      Disjoint Ps Y ∧ R∪(edges H\(R∪Q.biUnion triEdges))=Ps∪Y ∧
      edges H\Q.biUnion triEdges = Ps∪Y := by
  let L := edges H\(R∪Q.biUnion triEdges)
  obtain ⟨Ps,Y,hModeEq,hPY,hPs,hY⟩ := hMode L hSub hPhys
  have hFinal : edges H\Q.biUnion triEdges = R∪L := by
    ext e
    have hrE : e ∈ R → e ∈ edges H := fun he => hRE he
    have hqR : e ∈ Q.biUnion triEdges → e ∉ R :=
      fun heQ heR => disjoint_left.mp hQR heQ heR
    simp only [L,mem_sdiff,mem_union,not_or]
    tauto
  exact ⟨Ps,Y,hPs,hY,hPY,hModeEq,hFinal.trans hModeEq⟩

end TypedTriangle.StockEntry
