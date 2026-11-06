/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Plantholt.Basic

/-!
# Plantholt 2004: matchings and colourings of line graphs

* `exists_matchingOn`: an even set `W` in which every vertex has at least `|W|/2` neighbours is
  covered by a matching of `G[W]` (Dirac-type, via Tutte).
* `degree_sdiff_add`: removing a subgraph `M ≤ G` lowers degrees by the `M`-degrees.
* `colorable_of_le`, `colorable_succ_of_matching`: monotonicity, and one more colour for a
  matching.
* `two_mul_eIn_le_of_colorable`: a `D`-edge-colourable graph has no `D`-overfull odd set.
-/

@[expose] public section

namespace Plantholt

open SimpleGraph Finset
open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-! ### Matchings -/

/-- `M ≤ G` is a matching covering exactly `W`. -/
def IsMatchingOn (M : SimpleGraph V) (W : Finset V) : Prop :=
  M ≤ G ∧ (∀ v ∈ W, M.degree v = 1) ∧ ∀ v ∉ W, M.degree v = 0

theorem card_neighborFinset_induce (W : Finset V) (x : (W : Set V)) :
    (G.induce (W : Set V)).degree x = #(nbIn G W x.1) := by
  rw [← card_neighborFinset_eq_degree, ← card_map (Function.Embedding.subtype _)]
  congr 1
  ext u
  simp only [mem_map, mem_neighborFinset, Function.Embedding.subtype_apply, nbIn, mem_filter,
    comap_adj, Function.Embedding.coe_subtype, Subtype.exists, coe_mem, exists_and_right,
    exists_eq_right, induce_adj]
  constructor
  · rintro ⟨hu, h⟩; exact ⟨h, hu⟩
  · rintro ⟨h, hu⟩; exact ⟨hu, h⟩

/-- **Matching from high minimum degree.** -/
theorem exists_matchingOn {W : Finset V} (hev : Even #W)
    (hdeg : ∀ v ∈ W, #W ≤ 2 * #(nbIn G W v)) :
    ∃ M : SimpleGraph V, IsMatchingOn G M W := by
  rcases W.eq_empty_or_nonempty with rfl | hne
  · refine ⟨⊥, bot_le, fun v hv => absurd hv (notMem_empty v), fun v _ => ?_⟩
    rw [← card_neighborFinset_eq_degree]
    simp
  set H := G.induce (W : Set V)
  have hcardW : Fintype.card (W : Set V) = #W := by simp
  haveI : Nonempty (W : Set V) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hev' : Even (Fintype.card (W : Set V)) := by rw [hcardW]; exact hev
  have hmin : Fintype.card (W : Set V) ≤ 2 * H.minDegree := by
    obtain ⟨x, hx⟩ := H.exists_minimal_degree_vertex
    rw [hx, card_neighborFinset_induce, hcardW]
    exact hdeg x.1 x.2
  obtain ⟨P, hP⟩ := exists_isPerfectMatching_of_minDegree H hev' hmin
  let M : SimpleGraph V :=
    { Adj := fun u v => ∃ hu : u ∈ W, ∃ hv : v ∈ W, P.Adj ⟨u, hu⟩ ⟨v, hv⟩
      symm.symm := by
        rintro u v ⟨hu, hv, h⟩
        exact ⟨hv, hu, P.adj_symm h⟩
      loopless := ⟨fun _ ⟨_, _, h⟩ => (P.adj_sub h).ne rfl⟩ }
  have hMG : M ≤ G := by
    rintro u v ⟨hu, hv, h⟩
    exact P.adj_sub h
  refine ⟨M, hMG, fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨w, hw, huniq⟩ := hP.1 (hP.2 ⟨v, hv⟩)
    rw [← card_neighborFinset_eq_degree, card_eq_one]
    refine ⟨w.1, ?_⟩
    ext u
    simp only [mem_neighborFinset, mem_singleton]
    constructor
    · rintro ⟨_, hu, h⟩
      exact congrArg Subtype.val (huniq ⟨u, hu⟩ h)
    · rintro rfl
      exact ⟨hv, w.2, hw⟩
  · rw [← card_neighborFinset_eq_degree, card_eq_zero]
    ext u
    simp only [mem_neighborFinset, notMem_empty, iff_false]
    rintro ⟨hv', _, _⟩
    exact hv hv'

theorem degree_sdiff_add {M : SimpleGraph V} (hM : M ≤ G) (v : V) :
    (G \ M).degree v + M.degree v = G.degree v := by
  simp only [← card_neighborFinset_eq_degree]
  have hsub : M.neighborFinset v ⊆ G.neighborFinset v := fun u hu => by
    rw [mem_neighborFinset] at hu ⊢; exact hM hu
  have : (G \ M).neighborFinset v = G.neighborFinset v \ M.neighborFinset v := by
    ext u; simp [mem_neighborFinset, sdiff_adj]
  rw [this]
  exact card_sdiff_add_card_eq_card hsub

/-! ### Colourings of line graphs -/

/-- Line-graph colourings restrict to subgraphs. -/
theorem colorable_of_le {G G' : SimpleGraph V} (h : G ≤ G') {k : ℕ}
    (hc : G'.lineGraph.Colorable k) : G.lineGraph.Colorable k := by
  let f : G.lineGraph →g G'.lineGraph :=
    { toFun := fun e => ⟨e.1, (edgeSet_subset_edgeSet.2 h) e.2⟩
      map_rel' := by
        intro e f hef
        rw [lineGraph_adj_iff_exists] at hef ⊢
        exact ⟨fun h' => hef.1 (Subtype.ext (Subtype.mk.inj h')), hef.2⟩ }
  exact ⟨hc.some.comp f⟩

/-- Two distinct edges of a matching do not meet. -/
theorem eq_of_matching {M : SimpleGraph V} (hM : ∀ v, M.degree v ≤ 1) {v a b : V}
    (ha : M.Adj v a) (hb : M.Adj v b) : a = b := by
  by_contra hab
  have : #({a, b} : Finset V) ≤ #(M.neighborFinset v) := by
    apply card_le_card
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact (mem_neighborFinset _ _ _).2 ha
    · rw [mem_singleton.1 hx]; exact (mem_neighborFinset _ _ _).2 hb
  rw [card_pair hab, card_neighborFinset_eq_degree] at this
  have := hM v
  omega

/-- A matching takes one more colour. -/
theorem colorable_succ_of_matching {M : SimpleGraph V} (hMG : M ≤ G)
    (hM : ∀ v, M.degree v ≤ 1) {k : ℕ} (hc : (G \ M).lineGraph.Colorable k) :
    G.lineGraph.Colorable (k + 1) := by
  obtain ⟨C⟩ := hc
  have hmem : ∀ e : G.edgeSet, e.1 ∉ M.edgeSet → e.1 ∈ (G \ M).edgeSet := fun e he => by
    rw [edgeSet_sdiff]; exact ⟨e.2, he⟩
  let col : G.edgeSet → Fin (k + 1) := fun e =>
    if he : e.1 ∈ M.edgeSet then Fin.last k else (C ⟨e.1, hmem e he⟩).castSucc
  refine ⟨Coloring.mk col ?_⟩
  intro e f hef hcol
  rw [lineGraph_adj_iff_exists] at hef
  obtain ⟨hne, v, hve, hvf⟩ := hef
  simp only [col] at hcol
  by_cases he : e.1 ∈ M.edgeSet <;> by_cases hf : f.1 ∈ M.edgeSet
  · apply hne
    obtain ⟨e, he'⟩ := e
    obtain ⟨f, hf'⟩ := f
    obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.1 hve
    obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.1 hvf
    have := eq_of_matching hM (v := v) ((mem_edgeSet M).1 he) ((mem_edgeSet M).1 hf)
    subst this
    rfl
  · rw [dif_pos he, dif_neg hf] at hcol
    exact (Fin.castSucc_lt_last _).ne' hcol
  · rw [dif_neg he, dif_pos hf] at hcol
    exact (Fin.castSucc_lt_last _).ne hcol
  · rw [dif_neg he, dif_neg hf] at hcol
    refine C.valid ?_ (Fin.castSucc_injective _ hcol)
    rw [lineGraph_adj_iff_exists]
    exact ⟨fun h => hne (Subtype.ext (Subtype.mk.inj h)), v, hve, hvf⟩

/-- **Overfull sets obstruct colourings.** If `G` is `D`-edge-colourable, then every odd set `S`
spans at most `D (|S| − 1) / 2` edges. -/
theorem two_mul_eIn_le_of_colorable {D : ℕ} (hc : G.lineGraph.Colorable D) {S : Finset V}
    (hS : Odd #S) : 2 * eIn G S ≤ D * (#S - 1) := by
  obtain ⟨C⟩ := hc
  have hsub : ∀ e ∈ (inside G S).edgeFinset, e ∈ G.edgeSet := fun e he => by
    rw [mem_edgeFinset] at he
    induction e using Sym2.inductionOn with
    | hf u v => exact he.1
  let col : Sym2 V → Option (Fin D) := fun e => if h : e ∈ G.edgeSet then some (C ⟨e, h⟩) else none
  -- each colour class inside `S` covers at most `|S| − 1` vertices
  have hcls : ∀ i : Fin D,
      2 * #((inside G S).edgeFinset.filter fun e => col e = some i) ≤ #S - 1 := by
    intro i
    set T := (inside G S).edgeFinset.filter fun e => col e = some i
    have hdisj : (↑T : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
      intro e he f hf hef
      rw [Function.onFun, Finset.disjoint_left]
      intro v hve hvf
      apply hef
      simp only [T, coe_filter, Set.mem_setOf_eq] at he hf
      have he' := hsub e he.1
      have hf' := hsub f hf.1
      by_contra hne
      have hadj : G.lineGraph.Adj ⟨e, he'⟩ ⟨f, hf'⟩ := by
        rw [lineGraph_adj_iff_exists]
        exact ⟨fun h => hne (congrArg Subtype.val h), v, Sym2.mem_toFinset.1 hve,
          Sym2.mem_toFinset.1 hvf⟩
      apply C.valid hadj
      have h1 := he.2
      have h2 := hf.2
      simp only [col, dif_pos he', dif_pos hf', Option.some.injEq] at h1 h2
      rw [h1, h2]
    have hU : T.biUnion Sym2.toFinset ⊆ S := by
      intro v hv
      rw [mem_biUnion] at hv
      obtain ⟨e, he, hve⟩ := hv
      have he1 := (mem_filter.1 he).1
      rw [mem_edgeFinset] at he1
      rw [Sym2.mem_toFinset] at hve
      induction e using Sym2.inductionOn with
      | hf a b =>
        rcases Sym2.mem_iff.1 hve with rfl | rfl
        · exact he1.2.1
        · exact he1.2.2
    have hcard := card_le_card hU
    rw [card_biUnion hdisj, sum_congr rfl (g := fun _ => 2), sum_const, smul_eq_mul] at hcard
    · rcases hS with ⟨r, hr⟩
      omega
    · intro e he
      apply Sym2.card_toFinset_of_not_isDiag
      have he1 := (mem_filter.1 he).1
      rw [mem_edgeFinset] at he1
      induction e using Sym2.inductionOn with
      | hf a b =>
        rw [Sym2.mk_isDiag_iff]
        exact he1.1.ne
  have hmaps : ∀ e ∈ (inside G S).edgeFinset, col e ∈ (univ : Finset (Fin D)).map
      ⟨some, Option.some_injective _⟩ := fun e he => by
    simp only [col, dif_pos (hsub e he), mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
    exact ⟨_, rfl⟩
  rw [eIn, card_eq_sum_card_fiberwise hmaps, sum_map, mul_sum]
  calc ∑ i : Fin D, 2 * #((inside G S).edgeFinset.filter fun e => col e = some i)
      ≤ ∑ _i : Fin D, (#S - 1) := sum_le_sum fun i _ => hcls i
    _ = D * (#S - 1) := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

end Plantholt
