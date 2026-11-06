/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.EdgeColouring.Defs
public import Plantholt.Main
public import OneFactor.Plantholt67

/-!
# Plantholt's criterion from the Palomar formalization, with Chetwynd–Hilton 1985

`Plantholt.theorem_1_2` (Palomar PALOMAR-2026-11-04-000016 v1, `jtraverso/plantholt-overfull-criterion`
@ `28ff33d`) is Plantholt 2004, Theorem 1.2, for any `c ≥ 3/4` such that regular graphs of even
order `n` and degree `≥ c n` are 1-factorizable.  Chetwynd–Hilton 1985 gives `c = 6/7`
(`CH1985_OneFactor`, the same literal statement as `Master.ChetwyndHilton_1985`), so:

`plantholt_of_CH`: if `G` has even order `n` and `12 n + 7 Δ ≤ 21 δ` (i.e. `3δ − Δ ≥ 12n/7`) and
`G` is not `Δ`-edge-colourable, then some odd set `S`, `|S| ≥ 3`, induces a `Δ`-overfull subgraph.

This replaces the external hypothesis `Plantholt_Corollary_1_7` in L183.
-/

@[expose] public section

namespace CDRBicolour

open Finset

universe u

/-- **Chetwynd–Hilton (1985)**: a `d`-regular simple graph of even order `N` with `d ≥ 6N/7` is
1-factorizable.  Same literal statement as `Master.ChetwyndHilton_1985` (definitionally equal). -/
def CH1985_OneFactor : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ),
    Even (Fintype.card V) → (∀ v, G.degree v = d) → 6 * Fintype.card V ≤ 7 * d →
      EdgeColourable G d

theorem regularOneFactorable_of_CH (h : CH1985_OneFactor.{u}) :
    Plantholt.RegularOneFactorable.{u} (6 / 7) := by
  intro W _ _ H _ d hev hreg hcd
  have h7 : 6 * Fintype.card W ≤ 7 * d := by
    have : ((6 * Fintype.card W : ℕ) : ℝ) ≤ ((7 * d : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  exact h W H d hev (fun v => by convert hreg v) h7

/-- A `Δ`-overfull subgraph in Plantholt's sense gives an odd set inducing a `Δ`-overfull
subgraph in our sense. -/
theorem exists_inducesOverfull_of_hasOverfull {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : Plantholt.HasOverfullSubgraph G) :
    ∃ S : Finset V, InducesOverfull G G.maxDegree S := by
  classical
  obtain ⟨H, hodd, h3, hov⟩ := h
  refine ⟨H.verts.toFinset, ?_⟩
  have hc : H.verts.toFinset.card = H.verts.ncard := (Set.ncard_eq_toFinset_card' _).symm
  have hE : H.edgeSet.ncard ≤ (edgesIn G H.verts.toFinset).card := by
    rw [← Set.ncard_coe_finset (edgesIn G H.verts.toFinset)]
    refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : H.Adj x y := he
      simp only [edgesIn, coe_filter, Set.mem_ofPred_eq, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, Sym2.mem_iff, forall_eq_or_imp, forall_eq, Set.mem_toFinset]
      exact ⟨H.adj_sub hxy, H.edge_vert hxy, H.edge_vert hxy.symm⟩
  refine ⟨hc ▸ hodd, hc ▸ h3, ?_⟩
  rw [hc]
  omega

/-- **Plantholt's criterion with `c = 6/7`, from Chetwynd–Hilton 1985** (one direction). -/
theorem plantholt_of_CH (hCH : CH1985_OneFactor.{u}) {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hev : Even (Fintype.card V))
    (hdeg : 12 * Fintype.card V + 7 * G.maxDegree ≤ 21 * G.minDegree)
    (hnc : ¬ EdgeColourable G G.maxDegree) : ∃ S : Finset V, InducesOverfull G G.maxDegree S := by
  have hreal : 2 * (6 / 7 : ℝ) * Fintype.card V ≤ 3 * (G.minDegree : ℝ) - G.maxDegree := by
    have : ((12 * Fintype.card V + 7 * G.maxDegree : ℕ) : ℝ) ≤ ((21 * G.minDegree : ℕ) : ℝ) := by
      exact_mod_cast hdeg
    push_cast at this
    linarith
  have key := Plantholt.theorem_1_2 (by norm_num) (regularOneFactorable_of_CH hCH) G hev hreal
  have hov : Plantholt.HasOverfullSubgraph G := by
    by_contra hno
    exact hnc (key.2 hno)
  exact exists_inducesOverfull_of_hasOverfull G hov

/-- **Plantholt's criterion with `c = 6/7`** (Palomar `OneFactor.overfull_criterion67`, no
hypothesis): even order `n`, `11 n ≤ 6 (3δ − Δ)`, not `Δ`-edge-colourable ⇒ an odd set `|S| ≥ 3`
induces a `Δ`-overfull subgraph. -/
theorem plantholt_67 {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hev : Even (Fintype.card V))
    (hdeg : 12 * Fintype.card V ≤ 7 * (3 * G.minDegree - G.maxDegree))
    (hnc : ¬ EdgeColourable G G.maxDegree) : ∃ S : Finset V, InducesOverfull G G.maxDegree S := by
  have key := OneFactor.overfull_criterion67 G hev hdeg
  have hov : Plantholt.HasOverfullSubgraph G := by
    by_contra hno
    exact hnc (key.2 hno)
  exact exists_inducesOverfull_of_hasOverfull G hov

end CDRBicolour
