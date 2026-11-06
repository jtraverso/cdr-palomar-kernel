/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Selectors.OddSubdivision
public import RequestProject.Selectors.ParitySelector
public import RequestProject.Selectors.BalancedSelector

@[expose] public section

/-!
# Positive modes of an odd-subdivided selector in a link

`linkGraph G v` is the physical link graph of the root `v`: `x ~ y` iff `x y`, `v x`, `v y`
are all edges of `G`.  For an odd subdivision `D` of a finite abstract selector `Q` inside
`linkGraph G v`, one fuel

  `R = E(D) ∪ {v z : z ∈ φ(W) ∪ internals(D)}`

is fixed before the active set `S`.  For EVERY abstract mode `F` covering exactly `W ∪ S`,
`SelBridge.positive_mode` applies with `W' = φ(W) ∪ internals`, `S' = φ(S)` and the host mode
`modeEdges D F`:

* triangles `v x y` (`xy ∈ modeEdges D F`) are triangles of `G`, pairwise edge-disjoint;
* `R ∩ {v u : u ∈ S'} = ∅`;
* `R ∪ {v u : u ∈ S'} = E(D_S) ⊔ (E(D) \ modeEdges D F)` exactly (residual tokens);
* base cost `|E(D)| = ∑_e (2 t_e + 1)`, radial cost `|W| + ∑_e 2 t_e`,
  `|R| = ∑_e (2t_e+1) + |W| + ∑_e 2 t_e`.

Instances: all even modes of the subdivided parity selector, all balanced modes of the
subdivided balanced selector (each for the SAME subdivision `D`).
-/

namespace SelSubdiv

open Finset SelBridge

variable {V : Type*} [DecidableEq V]

/-- The physical link graph of a root `v`. -/
def linkGraph (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ G.Adj v x ∧ G.Adj v y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

variable {α : Type*} [DecidableEq α] {G : SimpleGraph V} {v : V} {Q : Finset (Sym2 α)}

namespace OddSubdivision

omit [DecidableEq α] in
/-- The subdivision edges of a subdivision inside the link lie in the link. -/
theorem pathEdges_inLink (D : OddSubdivision (linkGraph G v) Q) : InLink G v D.pathEdges := by
  intro f hf
  obtain ⟨e, he, j, hj, rfl⟩ := (mem_pathEdges _).mp hf
  have h := D.adj e he j hj
  refine ⟨h.1, ?_⟩
  intro x hx
  rcases (Sym2.mem_iff.mp hx) with rfl | rfl
  · exact h.2.1
  · exact h.2.2

/-- The fixed non-port covered set `W' = φ(W) ∪ internals`. -/
def auxCover (D : OddSubdivision (linkGraph G v) Q) (W : Finset α) : Finset V :=
  W.image D.φ ∪ D.internals

/-- **Positive mode through an odd subdivision.**  The fuel
`fuel v E(D) (φ(W) ∪ internals)` depends only on `D` and `W`; for every abstract mode `F`
covering exactly `W ∪ S` with `S ∩ W = ∅` the host mode `modeEdges D F` gives the exact
positive partition, with the stated costs. -/
theorem subdiv_positive_mode (D : OddSubdivision (linkGraph G v) Q) {W S : Finset α}
    {F : Finset (Sym2 α)} (hM : IsMode Q W S F) (hSW : Disjoint S W) :
    IsMode D.pathEdges (D.auxCover W) (S.image D.φ) (D.modeEdges F) ∧
    (∀ e ∈ D.modeEdges F, ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ G.Adj v x ∧ G.Adj v y) ∧
    (D.modeEdges F : Set (Sym2 V)).PairwiseDisjoint (triE v) ∧
    Disjoint (fuel v D.pathEdges (D.auxCover W)) (radial v (S.image D.φ)) ∧
    fuel v D.pathEdges (D.auxCover W) ∪ radial v (S.image D.φ) =
      (D.modeEdges F).biUnion (triE v) ∪ (D.pathEdges \ D.modeEdges F) ∧
    Disjoint ((D.modeEdges F).biUnion (triE v)) (D.pathEdges \ D.modeEdges F) ∧
    D.pathEdges.card = ∑ e ∈ Q, (2 * D.t e + 1) ∧
    (radial v (D.auxCover W)).card = W.card + ∑ e ∈ Q, 2 * D.t e ∧
    (fuel v D.pathEdges (D.auxCover W)).card =
      ∑ e ∈ Q, (2 * D.t e + 1) + (W.card + ∑ e ∈ Q, 2 * D.t e) := by
  have hM' := modeEdges_isMode (D := D) hM
  have hE := pathEdges_inLink D
  have hSW' : Disjoint (S.image D.φ) (D.auxCover W) := by
    rw [auxCover, disjoint_union_right]
    exact ⟨disjoint_image D.φ_inj |>.mpr hSW, disjoint_image_internals S⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := positive_mode hE hM' hSW'
  refine ⟨hM', h1, h2, h3, h4, h5, pathEdges_card, ?_, ?_⟩
  · rw [radial_card, auxCover, auxCover_card]
  · unfold auxCover; rw [h6, pathEdges_card, auxCover_card]

/-! ### All parity modes of the same subdivided parity selector -/

open ParitySel in
/-- Every even mode of the subdivided parity selector, with ONE fuel fixed by `D`. -/
theorem parity_subdiv_positive_modes {r : ℕ}
    (D : OddSubdivision (linkGraph G v) (paritySelector r).edgeFinset)
    (S : Finset (Fin r)) (hS : Even S.card) :
    ∃ F : Finset (Sym2 (PV r)), IsMode (paritySelector r).edgeFinset (auxSet r) (portSet S) F ∧
      IsMode D.pathEdges (D.auxCover (auxSet r)) ((portSet S).image D.φ) (D.modeEdges F) ∧
      (∀ e ∈ D.modeEdges F, ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ G.Adj v x ∧ G.Adj v y) ∧
      (D.modeEdges F : Set (Sym2 V)).PairwiseDisjoint (triE v) ∧
      Disjoint (fuel v D.pathEdges (D.auxCover (auxSet r))) (radial v ((portSet S).image D.φ)) ∧
      fuel v D.pathEdges (D.auxCover (auxSet r)) ∪ radial v ((portSet S).image D.φ) =
        (D.modeEdges F).biUnion (triE v) ∪ (D.pathEdges \ D.modeEdges F) ∧
      Disjoint ((D.modeEdges F).biUnion (triE v)) (D.pathEdges \ D.modeEdges F) := by
  obtain ⟨F, hFsub, hcov, hout⟩ := paritySelector_even_mode_edges r S hS
  have hM : IsMode (paritySelector r).edgeFinset (auxSet r) (portSet S) F := ⟨hFsub, hcov, hout⟩
  have hSW : Disjoint (portSet S) (auxSet r) := by
    rw [disjoint_left]
    intro x hx hx'
    simp only [portSet, mem_map, Function.Embedding.inl_apply] at hx
    obtain ⟨i, _, rfl⟩ := hx
    simp [auxSet] at hx'
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := subdiv_positive_mode D hM hSW
  exact ⟨F, hM, h0, h1, h2, h3, h4, h5⟩

/-! ### All balanced modes of the same subdivided balanced selector -/

/-- A matching subgraph gives an edge-form mode. -/
theorem isMode_of_subgraph {β : Type*} [Fintype β] [DecidableEq β] (Γ : SimpleGraph β)
    [DecidableRel Γ.Adj] (Mt : Γ.Subgraph) (W S : Finset β)
    (hverts : Mt.verts = ↑(W ∪ S)) (hM : Mt.IsMatching) :
    ∃ F : Finset (Sym2 β), IsMode Γ.edgeFinset W S F := by
  classical
  refine ⟨univ.filter (fun e => e ∈ Mt.edgeSet), ?_, ?_, ?_⟩
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    rw [SimpleGraph.mem_edgeFinset]
    exact Mt.edgeSet_subset he
  · intro x hx
    have hxv : x ∈ Mt.verts := by rw [hverts]; exact_mod_cast hx
    obtain ⟨w, hw, hu⟩ := hM hxv
    rw [card_eq_one]
    refine ⟨s(x, w), ?_⟩
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨he, hxe⟩
      induction e using Sym2.ind with
      | h a b =>
        rw [SimpleGraph.Subgraph.mem_edgeSet] at he
        rcases Sym2.mem_iff.mp hxe with rfl | rfl
        · rw [hu b he]
        · rw [hu a he.symm]; exact Sym2.eq_swap
    · rintro rfl
      exact ⟨hw, Sym2.mem_mk_left _ _⟩
  · intro x hx e he hxe
    simp only [mem_filter, mem_univ, true_and] at he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.Subgraph.mem_edgeSet] at he
      have hxv : x ∈ Mt.verts := by
        rcases Sym2.mem_iff.mp hxe with rfl | rfl
        · exact Mt.edge_vert he
        · exact Mt.edge_vert he.symm
      rw [hverts] at hxv
      exact hx (by exact_mod_cast hxv)

open SelBalanced

/-- Auxiliaries `A ⊔ B` of the balanced selector. -/
def auxB (l r : ℕ) : Finset (BV l r) :=
  (univ : Finset (Fin (4 * max l r))).image (fun a => Sum.inl (Sum.inl a)) ∪
    (univ : Finset (Fin (4 * max l r))).image (fun b => Sum.inr (Sum.inl b))

/-- Active ports `S_L ⊔ S_R` of the balanced selector. -/
def portsB {l r : ℕ} (SL : Finset (Fin l)) (SR : Finset (Fin r)) : Finset (BV l r) :=
  SL.image (fun p => Sum.inl (Sum.inr p)) ∪ SR.image (fun q => Sum.inr (Sum.inr q))

lemma activeVerts_eq {l r : ℕ} (SL : Finset (Fin l)) (SR : Finset (Fin r)) :
    activeVerts SL SR = auxB l r ∪ portsB SL SR := by
  ext x
  rw [mem_activeVerts]
  rcases x with (a | p) | (b | q) <;> simp [auxB, portsB]

lemma portsB_disjoint {l r : ℕ} (SL : Finset (Fin l)) (SR : Finset (Fin r)) :
    Disjoint (portsB SL SR) (auxB l r) := by
  rw [disjoint_left]
  intro x hx hx'
  simp only [portsB, auxB, mem_union, mem_image, mem_univ, true_and] at hx hx'
  rcases hx with ⟨p, _, rfl⟩ | ⟨q, _, rfl⟩ <;>
    rcases hx' with ⟨a, ha⟩ | ⟨b, hb⟩ <;> simp_all

/-- Every balanced mode of a subdivided balanced selector `QB` (any graph with the balanced
matching property, e.g. the one of `SelBalanced.balancedSelector_exists`), with ONE fuel
fixed by the subdivision `D`. -/
theorem balanced_subdiv_positive_modes {l r : ℕ} (QB : SimpleGraph (BV l r))
    [DecidableRel QB.Adj]
    (hQB : ∀ (SL : Finset (Fin l)) (SR : Finset (Fin r)), SL.card = SR.card →
      ∃ Mt : QB.Subgraph, Mt.verts = ↑(activeVerts SL SR) ∧ Mt.IsMatching)
    (D : OddSubdivision (linkGraph G v) QB.edgeFinset)
    (SL : Finset (Fin l)) (SR : Finset (Fin r)) (hS : SL.card = SR.card) :
    ∃ F : Finset (Sym2 (BV l r)), IsMode QB.edgeFinset (auxB l r) (portsB SL SR) F ∧
      IsMode D.pathEdges (D.auxCover (auxB l r)) ((portsB SL SR).image D.φ) (D.modeEdges F) ∧
      (∀ e ∈ D.modeEdges F, ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ G.Adj v x ∧ G.Adj v y) ∧
      (D.modeEdges F : Set (Sym2 V)).PairwiseDisjoint (triE v) ∧
      Disjoint (fuel v D.pathEdges (D.auxCover (auxB l r)))
        (radial v ((portsB SL SR).image D.φ)) ∧
      fuel v D.pathEdges (D.auxCover (auxB l r)) ∪ radial v ((portsB SL SR).image D.φ) =
        (D.modeEdges F).biUnion (triE v) ∪ (D.pathEdges \ D.modeEdges F) ∧
      Disjoint ((D.modeEdges F).biUnion (triE v)) (D.pathEdges \ D.modeEdges F) := by
  obtain ⟨Mt, hv, hm⟩ := hQB SL SR hS
  rw [activeVerts_eq] at hv
  obtain ⟨F, hM⟩ := isMode_of_subgraph QB Mt _ _ hv hm
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := subdiv_positive_mode D hM (portsB_disjoint SL SR)
  exact ⟨F, hM, h0, h1, h2, h3, h4, h5⟩

end OddSubdivision

end SelSubdiv
