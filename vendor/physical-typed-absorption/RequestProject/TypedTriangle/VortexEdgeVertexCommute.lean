/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.RestrictedHingeTransport
public import RequestProject.TypedTriangle.PhysicalResidual
@[expose] public section

/-! Borrado de aristas y paso al subtipo superviviente, sobre el mismo host
físico. Este cuadrado es necesario para transferir la persistencia reticular
de PreparedCore al hijo pagado. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem restricted_paid_child_eq_paid_restricted {V I : Type*} [Fintype V]
    (H : Host V I) (Z : Finset V) (B : Finset (Sym2 V)) :
    restrictedHost (subHost H (edges H \ B)) Z =
      subHost (restrictedHost H Z)
        (edges (restrictedHost H Z) \ restrictEdgeSet Z B) := by
  have hG :
      (restrictedHost (subHost H (edges H \ B)) Z).G =
        (subHost (restrictedHost H Z)
          (edges (restrictedHost H Z) \ restrictEdgeSet Z B)).G := by
    classical
    ext u v
    change (subHost H (edges H \ B)).G.Adj u.1 v.1 ↔
      (subHost (restrictedHost H Z)
        (edges (restrictedHost H Z) \ restrictEdgeSet Z B)).G.Adj u v
    simp only [subHost, SimpleGraph.inf_adj, SimpleGraph.fromEdgeSet_adj]
    simp only [SetLike.mem_coe, mem_sdiff, mem_restrictEdgeSet]
    have hleft : s(u.1,v.1) ∈ edges H ↔ H.G.Adj u.1 v.1 := by
      simp [edges]
    have hright : s(u,v) ∈ edges (restrictedHost H Z) ↔ H.G.Adj u.1 v.1 := by
      simp only [edges, mem_filter, mem_univ, true_and, SimpleGraph.mem_edgeSet]
      rfl
    rw [hleft, hright]
    simp only [Sym2.map_mk]
    have heq : u = v ↔ u.1 = v.1 := Subtype.ext_iff
    simp only [ne_eq, heq, restrictedHost]
  exact congrArg (fun G => (⟨G, fun v => H.lab v.1⟩ : Host (Survivors Z) I)) hG

#print axioms restricted_paid_child_eq_paid_restricted

end TypedTriangle.Vortex
