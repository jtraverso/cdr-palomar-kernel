/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.CorePaidLayer
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Exact finite-edge/graph adapters used by the fork--selector composition. -/
open Finset Classical
noncomputable section
namespace TypedTriangle.CorePaid
variable {V I : Type*} [Fintype V]

lemma edgeFinset_fromEdges (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    (SimpleGraph.fromEdgeSet (E:Set (Sym2 V))).edgeFinset = E := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_sdiff,mem_coe,Sym2.mem_diagSet]
  exact ⟨fun h => h.1,fun h => ⟨h,hE e h⟩⟩

lemma fromEdges_degree_le (E : Finset (Sym2 V)) {r : ℕ}
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (hd : ∀ v, SelSimul.edeg E v ≤ r) :
    ∀ v, (SimpleGraph.fromEdgeSet (E:Set (Sym2 V))).degree v ≤ r := by
  intro v
  rw [← SimpleGraph.card_incidenceFinset_eq_degree,SimpleGraph.incidenceFinset_eq_filter,
    edgeFinset_fromEdges E hE]
  exact hd v

lemma edges_diagonal_free {H : Host V I} {E : Finset (Sym2 V)} (hE : E ⊆ edges H) :
    ∀ e ∈ E, ¬ e.IsDiag := fun e he => H.G.not_isDiag_of_mem_edgeSet ((mem_filter.mp (hE he)).2)

lemma fromEdges_le_host {H : Host V I} {E : Finset (Sym2 V)} (hE : E ⊆ edges H) :
    SimpleGraph.fromEdgeSet (E:Set (Sym2 V)) ≤ H.G := by
  intro u v he
  exact (mem_filter.mp (hE he.1)).2

lemma basal_subset_edges {H : Host V I} {F : Set (Multiset I)} {E : Finset (Sym2 V)}
    (hE : Basal H F E) : E ⊆ edges H := by
  obtain ⟨D,hD⟩ := hE
  rw [← hD.2.2]
  intro e he
  obtain ⟨T,hT,he⟩ := mem_biUnion.mp he
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨hu,hv,hne⟩ := mem_triEdges.mp he
    exact mem_filter.mpr ⟨mem_univ _,by simpa using (hD.1 T hT).2.1 u hu v hv hne⟩

end TypedTriangle.CorePaid
