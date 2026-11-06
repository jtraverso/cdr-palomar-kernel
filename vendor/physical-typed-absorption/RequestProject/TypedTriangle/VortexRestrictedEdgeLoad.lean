/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.RestrictedHingeTransport
public import RequestProject.TypedTriangle.SubtypeCert
@[expose] public section

/-! Local edge load cannot increase when passing to a surviving-vertex subtype. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem restricted_edge_load_le {V : Type*} [Fintype V]
    (Z : Finset V) (B : Finset (Sym2 V)) (v : Survivors Z) :
    ((restrictEdgeSet Z B).filter (fun e => v ∈ e)).card ≤
      (B.filter (fun e => v.1 ∈ e)).card := by
  apply Finset.card_le_card_of_injOn (Sym2.map Subtype.val)
  · intro e he
    obtain ⟨heB, hve⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨(mem_restrictEdgeSet Z B e).mp heB,
      Sym2.mem_map.mpr ⟨v, hve, rfl⟩⟩
  · exact (Sym2.map.injective Subtype.val_injective).injOn

theorem restricted_edge_zero {V : Type*} [Fintype V]
    (Z : Finset V) (B : Finset (Sym2 V)) (y : Sym2 V → ℤ)
    (hzero : ∀ e ∈ B, y e = 0) :
    ∀ e ∈ restrictEdgeSet Z B, Dispersal.restr Z y e = 0 := by
  intro e he
  exact hzero _ ((mem_restrictEdgeSet Z B e).mp he)

#print axioms restricted_edge_load_le
#print axioms restricted_edge_zero

end TypedTriangle.Vortex
