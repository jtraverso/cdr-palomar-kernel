/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.SparseEdgeDefs
public import RequestProject.Selectors.SubdivBridge

@[expose] public section

/-!
# The typed link `L_v(G, F)` and odd subdivisions inside it — V20

* `typedLink G lab F v` : `u ~ w` iff `u ≠ w` and `{v, u, w}` is a PERMITTED triangle
  (`TypedTriangle.SparseEdge.IsAllowed`).  This is the same body as
  `TypedTriangle.ComponentRows.link` (see `TypedLinkAdapter.lean`, `typedLink_eq_link`).
* `typedLink_le_linkGraph` : the typed link is contained in the ambient link
  `SelSubdiv.linkGraph G v` (`xy, vx, vy ∈ E(G)`).  The converse is false in general:
  ambient adjacency (`SelBridge.InLink`) does NOT certify the triangle type.
* `OddSubdivision.mono` : an odd subdivision transfers along `H ≤ H'` with the same data
  (so the same base edges, internals and mode edges).
* `typed_pathEdge` / `typed_modeEdge` : every base edge `xy` of an odd subdivision in the
  typed link — in particular every base of every mode triangle `v x y` — is an edge of the
  typed link, i.e. `{v, x, y}` is a permitted triangle.
-/

namespace SelTyped

open Finset SelSubdiv

section Classical

open Classical

variable {V I : Type*}

/-- The typed link `L_v(G, F)`: `u ~ w` iff `u ≠ w` and `{v, u, w}` is a permitted triangle. -/
def typedLink (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V) :
    SimpleGraph V where
  Adj u w := u ≠ w ∧ TypedTriangle.SparseEdge.IsAllowed G lab F {v, u, w}
  symm := ⟨fun u w h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end Classical

variable {V I : Type*} [DecidableEq V]

/-- Typed adjacency is typed permissibility of `{v, x, y}` (for any decidable equality). -/
theorem typedLink_adj_iff {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v x y : V} :
    (typedLink G lab F v).Adj x y ↔ x ≠ y ∧ TypedTriangle.SparseEdge.IsAllowed G lab F {v, x, y} := by
  unfold typedLink
  simp only
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> convert h2

/-- **The typed link lies in the ambient link.** -/
theorem typedLink_le_linkGraph (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V) :
    typedLink G lab F v ≤ linkGraph G v := by
  intro x y h
  obtain ⟨hxy, hcard, hadj, -⟩ := typedLink_adj_iff.mp h
  have hvx : v ≠ x := by
    rintro rfl
    simp at hcard
    have := Finset.card_le_two (a := v) (b := y); omega
  have hvy : v ≠ y := by
    rintro rfl
    rw [Finset.pair_comm] at hcard
    simp at hcard
    have := Finset.card_le_two (a := v) (b := x); omega
  exact ⟨hadj x (by simp) y (by simp) hxy, hadj v (by simp) x (by simp) hvx,
    hadj v (by simp) y (by simp) hvy⟩

variable {α : Type*} [DecidableEq α] {Q : Finset (Sym2 α)}

/-- Transfer of an odd subdivision along `H ≤ H'` (same data). -/
def _root_.SelSubdiv.OddSubdivision.mono {H H' : SimpleGraph V} (h : H ≤ H')
    (D : OddSubdivision H Q) : OddSubdivision H' Q :=
  { D with adj := fun e he j hj => h (D.adj e he j hj) }

omit [DecidableEq V] [DecidableEq α] in
@[simp] lemma mono_φ {H H' : SimpleGraph V} (h : H ≤ H') (D : OddSubdivision H Q) :
    (D.mono h).φ = D.φ := rfl

omit [DecidableEq α] in
lemma mono_pathEdges {H H' : SimpleGraph V} (h : H ≤ H') (D : OddSubdivision H Q) :
    (D.mono h).pathEdges = D.pathEdges := rfl

omit [DecidableEq α] in
lemma mono_internals {H H' : SimpleGraph V} (h : H ≤ H') (D : OddSubdivision H Q) :
    (D.mono h).internals = D.internals := rfl

lemma mono_modeEdges {H H' : SimpleGraph V} (h : H ≤ H') (D : OddSubdivision H Q)
    (F' : Finset (Sym2 α)) : (D.mono h).modeEdges F' = D.modeEdges F' := rfl

omit [DecidableEq α] in
/-- **Typed certificate of every base edge.** -/
theorem typed_pathEdge {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    (D : OddSubdivision (typedLink G lab F v) Q) :
    ∀ f ∈ D.pathEdges, ∃ x y, f = s(x, y) ∧ (typedLink G lab F v).Adj x y := by
  intro f hf
  obtain ⟨e, he, j, hj, rfl⟩ := (OddSubdivision.mem_pathEdges _).mp hf
  exact ⟨_, _, rfl, D.adj e he j hj⟩

/-- **Typed certificate of every mode triangle**: for every abstract mode `F'`, each base `xy`
of the host mode gives a permitted triangle `{v, x, y}`. -/
theorem typed_modeEdge {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    (D : OddSubdivision (typedLink G lab F v) Q) (F' : Finset (Sym2 α)) :
    ∀ f ∈ D.modeEdges F', ∃ x y, f = s(x, y) ∧ x ≠ y ∧
      TypedTriangle.SparseEdge.IsAllowed G lab F {v, x, y} := by
  intro f hf
  obtain ⟨x, y, rfl, h⟩ := typed_pathEdge D f (OddSubdivision.modeEdges_subset F' hf)
  exact ⟨x, y, rfl, typedLink_adj_iff.mp h⟩

end SelTyped
