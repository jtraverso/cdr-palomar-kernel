/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Plantholt.Cases3
public import LeanPool.Vizing.Main

/-!
# Plantholt 2004, Theorem 1.2

**Theorem 1.2** (M. Plantholt, *Overfull conjecture for graphs with high minimum degree*,
J. Graph Theory 47 (2004) 73–80). Let `c ≥ 3/4` be such that every regular graph of even order
`n` and degree at least `c n` is 1-factorable. If `G` has even order `n` and
`(3δ − Δ)/2 ≥ c n`, then `G` is Class 1 (`χ′ = Δ`) if and only if it has no `Δ`-overfull subgraph.

The proof follows the paper: add edges while keeping the maximum degree and the absence of overfull
subgraphs (`step`, preconditioning), then remove matchings and induct. The induction runs on
`D − δ'` for degree bounds `δ' ≤ deg ≤ D`. Two remarks on the proof:
* the paper uses Seymour's theorem only to show that, in Case 1, at most two vertices have the
  minimum degree; this follows from the deficiency count `Σ_v (Δ − deg v) = 2 (Δ − δ)`;
* the paper excludes orders `n ≤ 10` by the known classification; the degree conditions make every
  matching exist for all even `n` (and force `n ≥ 12` in Subcase 3).
-/

@[expose] public section

namespace Plantholt

open SimpleGraph Finset

section Core

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem colorable_of_no_adj {G : SimpleGraph V} (h : ∀ u v, ¬ G.Adj u v) (k : ℕ) :
    G.lineGraph.Colorable k := by
  have hF : G.edgeSet → False := fun e => by
    obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | hf u v => exact h u v he
  exact ⟨Coloring.mk (fun e => (hF e).elim) fun {e} _ => (hF e).elim⟩

theorem degree_sup_edge_le (G : SimpleGraph V) {u v : V} (w : V) :
    (G ⊔ edge u v).degree w ≤ G.degree w + (if w = u ∨ w = v then 1 else 0) := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  set T : Finset V := if w = u then {v} else if w = v then {u} else ∅ with hT
  have hTc : #T ≤ (if w = u ∨ w = v then 1 else 0) := by
    rw [hT]; split_ifs <;> simp_all
  have hsub : (G ⊔ edge u v).neighborFinset w ⊆ G.neighborFinset w ∪ T := by
    intro x hx
    rw [mem_neighborFinset, sup_adj, edge_adj] at hx
    rw [mem_union, mem_neighborFinset]
    rcases hx with hx | ⟨hx, -⟩
    · exact Or.inl hx
    · right
      rw [hT]
      rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp
      · split_ifs with h h' <;> simp_all
  calc _ ≤ #(G.neighborFinset w ∪ T) := card_le_card hsub
    _ ≤ #(G.neighborFinset w) + #T := card_union_le _ _
    _ ≤ _ := by omega

theorem eIn_sup_edge_le (G : SimpleGraph V) (u v : V) (S : Finset V) :
    eIn (G ⊔ edge u v) S ≤ eIn G S + 1 := by
  rw [eIn, eIn]
  calc _ ≤ #(insert s(u, v) (inside G S).edgeFinset) := card_le_card ?_
    _ ≤ _ := card_insert_le _ _
  intro e he
  rw [mem_edgeFinset] at he
  rw [mem_insert, mem_edgeFinset]
  induction e using Sym2.inductionOn with
  | hf a b =>
    simp only [mem_edgeSet, inside, sup_adj, edge_adj] at he ⊢
    rcases he with ⟨hab | ⟨hab, -⟩, ha, hb⟩
    · exact Or.inr ⟨hab, ha, hb⟩
    · left
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap

/-- The inductive step: preconditioning and the case analysis. -/
theorem step {c : ℝ} (hc34 : 3 / 4 ≤ c) (hev : Even (Fintype.card V))
    (hC : ∀ (H : SimpleGraph V) (d : ℕ), (∀ v, H.degree v = d) → c * Fintype.card V ≤ d →
      H.lineGraph.Colorable d)
    {G : SimpleGraph V} {D δ0 : ℕ} (hg : Good c G D δ0) (ih : IndHyp V c (D - δ0)) :
    G.lineGraph.Colorable D := by
  rcases isEmpty_or_nonempty V with hV | hV
  · exact colorable_of_no_adj (fun u => isEmptyElim u) D
  by_cases hlow : ∀ v, G.degree v < D
  · have h1 := maxDegree_le_of_forall_degree_le G (D - 1) fun v => by
      have := hlow v; omega
    have h2 := hlow (Classical.arbitrary V)
    exact (LeanPool.Vizing.lineGraph_colorable G).mono (by omega)
  push_neg at hlow
  obtain ⟨x0, hx0⟩ := hlow
  -- preconditioning: a maximal supergraph
  set 𝒢 := univ.filter fun G' : SimpleGraph V =>
    G ≤ G' ∧ (∀ v, G'.degree v ≤ D) ∧ NoOverfull G' D
  have hG : G ∈ 𝒢 := mem_filter.2 ⟨mem_univ _, le_rfl, hg.1, hg.2.2.2⟩
  obtain ⟨G', hG', hmaxl⟩ := 𝒢.exists_max_image (fun G' => #G'.edgeFinset) ⟨G, hG⟩
  obtain ⟨hle, hmax', hno'⟩ := (mem_filter.1 hG').2
  refine colorable_of_le hle ?_
  have hmin' : ∀ v, δ0 ≤ G'.degree v := fun v => (hg.2.1 v).trans (degree_le_of_le hle)
  have hx0' : G'.degree x0 = D := le_antisymm (hmax' x0) (hx0.trans (degree_le_of_le hle))
  have hcond := hg.2.2.1
  have hδD : δ0 ≤ D := hx0' ▸ hmin' x0
  have hD1 : D + 1 ≤ Fintype.card V := hx0' ▸ G'.degree_lt_card_verts x0
  have hcn : c * Fintype.card V ≤ δ0 := by
    have : (δ0 : ℝ) ≤ D := by exact_mod_cast hδD
    linarith
  have hN : 3 * Fintype.card V + 2 * D ≤ 6 * δ0 := by
    have h1 : 3 / 4 * (Fintype.card V : ℝ) ≤ c * Fintype.card V :=
      mul_le_mul_of_nonneg_right hc34 (Nat.cast_nonneg _)
    have : (3 * Fintype.card V + 2 * D : ℝ) ≤ 6 * δ0 := by linarith
    exact_mod_cast this
  have hn0 : 0 < Fintype.card V := Fintype.card_pos
  have hn4 : 4 ≤ Fintype.card V := by obtain ⟨t, ht⟩ := hev; omega
  have hδ : Fintype.card V + 2 ≤ 2 * δ0 := by omega
  have X : Ctx c G' D δ0 :=
    { hev := hev, good := ⟨hmax', hmin', hcond, hno'⟩, hN := hN, hcn := hcn, hD1 := hD1,
      hn4 := hn4, hδ := hδ, hδD := hδD, ih := ih, hC := hC }
  by_cases hreg : ∀ v, G'.degree v = D
  · exact hC G' D hreg (by have : (δ0 : ℝ) ≤ D := (by exact_mod_cast hδD); linarith)
  push_neg at hreg
  have hnr : ∃ v, G'.degree v < D := by
    obtain ⟨v, hv⟩ := hreg; exact ⟨v, lt_of_le_of_ne (hmax' v) hv⟩
  by_cases hfull : ∃ S, IsFull G' D S
  · obtain ⟨S, hS⟩ := hfull
    exact case_full X hS hnr
  push_neg at hfull
  -- maximality: two vertices below `D` are adjacent
  have hcomp : ∀ u v, u ≠ v → G'.degree u < D → G'.degree v < D → G'.Adj u v := by
    intro u v huv hu hv
    by_contra hadj
    have hlt : #G'.edgeFinset < #(G' ⊔ edge u v).edgeFinset := by
      apply card_lt_card
      rw [edgeFinset_ssubset_edgeFinset]
      refine lt_of_le_of_ne le_sup_left fun h => hadj ?_
      have : (G' ⊔ edge u v).Adj u v := by
        rw [sup_adj, edge_adj]; exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
      rw [← h] at this; exact this
    have hdeg'' : ∀ w, (G' ⊔ edge u v).degree w ≤ D := fun w => by
      have := degree_sup_edge_le G' (u := u) (v := v) w
      split_ifs at this with hw
      · rcases hw with rfl | rfl <;> omega
      · have := hmax' w; omega
    have hno'' : NoOverfull (G' ⊔ edge u v) D := by
      intro S hS
      by_contra hlt2
      push_neg at hlt2
      have h1 := eIn_sup_edge_le G' u v S
      have h2 := two_mul_eIn_le_card (G' ⊔ edge u v) S
      obtain ⟨r, hr⟩ := hS
      have hS3 : 3 ≤ #S := by
        by_contra h3
        have : #S - 1 = 0 := by omega
        rw [this, mul_zero] at h2 hlt2
        omega
      have hpar : D * (#S - 1) = 2 * (D * r) := by
        rw [show #S - 1 = 2 * r by omega]; ring
      exact hfull S ⟨hS3, ⟨r, hr⟩, by omega⟩
    have hmem : (G' ⊔ edge u v) ∈ 𝒢 :=
      mem_filter.2 ⟨mem_univ _, hle.trans le_sup_left, hdeg'', hno''⟩
    have h2 : #(G' ⊔ edge u v).edgeFinset ≤ #G'.edgeFinset := by
      convert hmaxl (G' ⊔ edge u v) hmem
    omega
  exact case2 X hfull hcomp ⟨x0, hx0'⟩ hnr

theorem indHyp_all {c : ℝ} (hc34 : 3 / 4 ≤ c) (hev : Even (Fintype.card V))
    (hC : ∀ (H : SimpleGraph V) (d : ℕ), (∀ v, H.degree v = d) → c * Fintype.card V ≤ d →
      H.lineGraph.Colorable d) : ∀ m, IndHyp V c m := by
  intro m
  induction m with
  | zero => intro G D δ' h; exact absurd h (Nat.not_lt_zero _)
  | succ m ihm =>
    intro G D δ' hlt hg
    exact step hc34 hev hC hg fun G₁ D₁ δ₁ h₁ hg₁ => ihm G₁ D₁ δ₁ (by omega) hg₁

end Core

/-! ### The statement -/

universe u

/-- `G` contains a `Δ(G)`-overfull subgraph: a subgraph `H` with an odd number `≥ 3` of vertices
and `|E(H)| > Δ(G) ⌊|V(H)|/2⌋`. -/
def HasOverfullSubgraph {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  ∃ H : G.Subgraph, Odd H.verts.ncard ∧ 3 ≤ H.verts.ncard ∧
    G.maxDegree * (H.verts.ncard - 1) < 2 * H.edgeSet.ncard

/-- Every `d`-regular graph of even order `n` with `d ≥ c n` is 1-factorable, i.e. its edges
split into `d` perfect matchings (equivalently, it is `d`-edge-colourable). -/
def RegularOneFactorable (c : ℝ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] (d : ℕ),
    Even (Fintype.card W) → H.IsRegularOfDegree d → c * Fintype.card W ≤ d →
      H.lineGraph.Colorable d

section Statement

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem edgeSet_ncard_le_eIn (G : SimpleGraph V) (H : G.Subgraph) :
    H.edgeSet.ncard ≤ eIn G H.verts.toFinset := by
  rw [eIn, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
    rw [Subgraph.mem_edgeSet] at he
    rw [coe_edgeFinset, mem_edgeSet]
    exact ⟨H.adj_sub he, Set.mem_toFinset.2 (H.edge_vert he),
      Set.mem_toFinset.2 (H.edge_vert he.symm)⟩

theorem induce_edgeSet_ncard (G : SimpleGraph V) (S : Finset V) :
    ((⊤ : G.Subgraph).induce (S : Set V)).edgeSet.ncard = eIn G S := by
  rw [eIn, ← Set.ncard_coe_finset]
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
    rw [Subgraph.mem_edgeSet, coe_edgeFinset, mem_edgeSet]
    simp only [Subgraph.induce_adj, Subgraph.top_adj, inside, mem_coe]
    tauto

theorem noOverfull_iff (G : SimpleGraph V) :
    NoOverfull G G.maxDegree ↔ ¬ HasOverfullSubgraph G := by
  constructor
  · rintro hno ⟨H, hodd, h3, hlt⟩
    have h1 := edgeSet_ncard_le_eIn G H
    rw [Set.ncard_eq_toFinset_card'] at hodd h3 hlt
    have := hno _ hodd
    omega
  · intro h S hS
    by_contra hlt
    push_neg at hlt
    apply h
    have h2 := two_mul_eIn_le_card G S
    have hS3 : 3 ≤ #S := by
      by_contra h3
      have : #S - 1 = 0 := by obtain ⟨r, hr⟩ := hS; omega
      rw [this, mul_zero] at h2 hlt
      omega
    refine ⟨(⊤ : G.Subgraph).induce (S : Set V), ?_, ?_, ?_⟩
    · rw [Subgraph.induce_verts, Set.ncard_coe_finset]; exact hS
    · rw [Subgraph.induce_verts, Set.ncard_coe_finset]; exact hS3
    · rw [Subgraph.induce_verts, Set.ncard_coe_finset, induce_edgeSet_ncard]; exact hlt

end Statement

/-- **Plantholt 2004, Theorem 1.2.** -/
theorem theorem_1_2 {c : ℝ} (hc : 3 / 4 ≤ c) (hC : RegularOneFactorable.{u} c)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hev : Even (Fintype.card V))
    (hdeg : 2 * c * Fintype.card V ≤ 3 * (G.minDegree : ℝ) - G.maxDegree) :
    G.lineGraph.Colorable G.maxDegree ↔ ¬ HasOverfullSubgraph G := by
  classical
  obtain rfl : ‹DecidableRel G.Adj› = fun a b => Classical.propDecidable (G.Adj a b) :=
    Subsingleton.elim _ _
  rw [← noOverfull_iff]
  constructor
  · intro hcol S hS
    exact two_mul_eIn_le_of_colorable G hcol hS
  · intro hno
    have hC' : ∀ (H : SimpleGraph V) (d : ℕ), (∀ v, H.degree v = d) →
        c * Fintype.card V ≤ d → H.lineGraph.Colorable d := fun H d hreg hcd =>
      hC V H d hev hreg hcd
    exact indHyp_all hc hev hC' (G.maxDegree - G.minDegree + 1) G G.maxDegree G.minDegree
      (by omega) ⟨fun v => G.degree_le_maxDegree v, fun v => G.minDegree_le_degree v, hdeg, hno⟩

end Plantholt
