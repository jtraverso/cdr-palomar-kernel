/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.ChildDegreeBudget
public import RequestProject.TypedTriangle.SampledBasalLift
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! A sampled reference, lifted from the actual induced host, consumes at
most the sampled-core size at every ambient vertex. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.SampledResource

theorem lift_degree_le_core_card {V I : Type} [Fintype V]
    (H : Host V I) (W : Finset V)
    (E : Finset (Sym2 {x // x ∈ W}))
    (hE : E ⊆ edges
      (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ : Host {x // x ∈ W} I)) :
    ∀ v, SparseEdge.degIn (lift W E) v ≤ W.card := by
  have hSub : lift W E ⊆ SparseEdge.edges (S07V42.indG H.G W) := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    induction f using Sym2.ind with
    | _ u v =>
      have huv : H.G.Adj u.1 v.1 := by
        have h := hE hf
        simpa [edges] using h
      change (s(u.1,v.1) : Sym2 V) ∈ SparseEdge.edges (S07V42.indG H.G W)
      have hAdj : (S07V42.indG H.G W).Adj u.1 v.1 :=
        ⟨huv,u.property,v.property⟩
      simpa only [SparseEdge.edges, Finset.mem_filter, Finset.mem_univ,
        true_and, SimpleGraph.mem_edgeSet] using hAdj
  exact degree_le_child_card H W (lift W E) hSub

#print axioms lift_degree_le_core_card

theorem full_reserved_degree_le {V I : Type} [Fintype V]
    (H : Host V I) (W : Finset V) (U : Finset (Sym2 V))
    (E : Finset (Sym2 {x // x ∈ W})) (dU : ℕ)
    (hU : ∀ v, SparseEdge.degIn U v ≤ dU)
    (hE : E ⊆ edges
      (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ : Host {x // x ∈ W} I)) :
    ∀ v, SparseEdge.degIn (U∪lift W E) v ≤ dU+W.card := by
  intro v
  have hUnion := SelSimul.edeg_union_le U (lift W E) v
  change SparseEdge.degIn (U∪lift W E) v ≤
    SparseEdge.degIn U v + SparseEdge.degIn (lift W E) v at hUnion
  exact hUnion.trans (Nat.add_le_add (hU v) (lift_degree_le_core_card H W E hE v))

#print axioms full_reserved_degree_le

end TypedTriangle.SampledResource
