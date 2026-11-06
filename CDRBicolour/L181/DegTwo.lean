/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Components of a graph of maximum degree two

In a finite simple graph with all degrees `≤ 2`, the total *deficit* `∑ (2 - deg v)` over a
connected component is `0` or `2` (a component is a cycle or a path).  This is the counting
behind the port groups of L181: a group has at most two free ports.
-/

@[expose] public section

namespace CDRBicolour.L181

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] (Γ : SimpleGraph α) [DecidableRel Γ.Adj]

/-- Vertex set of a connected component, as a `Finset`. -/
noncomputable def compFinset (C : Γ.ConnectedComponent) : Finset α := by
  classical exact univ.filter fun v => Γ.connectedComponentMk v = C

theorem mem_compFinset {C : Γ.ConnectedComponent} {v : α} :
    v ∈ compFinset Γ C ↔ Γ.connectedComponentMk v = C := by
  classical
  unfold compFinset; simp

/-- **Deficit of a component.** If all degrees are `≤ 2`, the deficit of a component is `2·d`
with `d ≤ 1`. -/
theorem component_deficit (hdeg : ∀ v, Γ.degree v ≤ 2) (C : Γ.ConnectedComponent) :
    ∃ d, ∑ v ∈ compFinset Γ C, (2 - Γ.degree v) = 2 * d ∧ d ≤ 1 := by
  classical
  set s : Set α := C.supp with hs
  have hmem : ∀ v, v ∈ s ↔ v ∈ compFinset Γ C := fun v => by
    rw [mem_compFinset]; exact SimpleGraph.ConnectedComponent.mem_supp_iff C v
  set H : SimpleGraph s := Γ.induce s with hH
  have hconn : H.Connected := C.connected_toSimpleGraph
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at h1
  have hsum := H.sum_degrees_eq_twice_card_edges
  have hdegH : ∀ v : s, H.degree v = Γ.degree v.1 := by
    intro v
    apply SimpleGraph.degree_induce_of_neighborSet_subset
    intro u hu
    exact C.mem_supp_of_adj_mem_supp v.2 hu
  simp_rw [hdegH] at hsum
  have hsum' : ∑ v ∈ compFinset Γ C, Γ.degree v = 2 * H.edgeFinset.card := by
    rw [← hsum]
    exact Finset.sum_subtype (compFinset Γ C) (fun v => (hmem v).symm) (fun v => Γ.degree v)
  have hcard : Fintype.card s = (compFinset Γ C).card := by
    rw [Fintype.card_subtype]
    congr 1
  have hsplit : ∑ v ∈ compFinset Γ C, (2 - Γ.degree v) + ∑ v ∈ compFinset Γ C, Γ.degree v =
      2 * (compFinset Γ C).card := by
    rw [← sum_add_distrib, sum_congr rfl fun v _ => Nat.sub_add_cancel (hdeg v), sum_const,
      smul_eq_mul, mul_comm]
  rw [hcard] at h1
  refine ⟨(compFinset Γ C).card - H.edgeFinset.card, ?_, by omega⟩
  omega

end CDRBicolour.L181
