/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Perfect matchings from high minimum degree

A finite simple graph of even order `n` and minimum degree at least `n/2` has a perfect
matching (via Tutte's theorem in Mathlib: there is no Tutte violator). Copied from the author's
`PaperIII.DiracMatching` (Erdős #81 series).
-/

@[expose] public section

namespace Plantholt

open SimpleGraph Finset
open scoped Classical

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [DecidableEq W] in
/-- The neighbourhood cardinality as an `ncard` equals the degree. -/
theorem neighborSet_ncard_eq_degree (H : SimpleGraph W) (v : W) :
    (H.neighborSet v).ncard = H.degree v := by
  rw [Set.ncard_eq_toFinset_card', ← card_neighborFinset_eq_degree]
  congr 1

/-- A connected component's support contains a vertex together with all of its
neighbours, hence has at least `deg v + 1` elements. -/
theorem comp_supp_card_ge (H : SimpleGraph W) (v : W) :
    (H.neighborSet v).ncard + 1 ≤ (H.connectedComponentMk v).supp.ncard := by
  rw [neighborSet_ncard_eq_degree]
  have hsub : (insert v (H.neighborFinset v) : Finset W) ⊆
      (H.connectedComponentMk v).supp.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, mem_neighborFinset] at hx
    rw [Set.mem_toFinset]
    rcases hx with rfl | hx
    · exact (ConnectedComponent.mem_supp_iff _ _).mpr rfl
    · exact (ConnectedComponent.mem_supp_iff _ _).mpr
        (ConnectedComponent.eq.mpr (Adj.reachable hx.symm))
  have hcard : (insert v (H.neighborFinset v)).card = H.degree v + 1 := by
    rw [Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree]
  calc H.degree v + 1 = (insert v (H.neighborFinset v)).card := hcard.symm
    _ ≤ (H.connectedComponentMk v).supp.toFinset.card := Finset.card_le_card hsub
    _ = (H.connectedComponentMk v).supp.ncard := by rw [Set.ncard_eq_toFinset_card']

/-- If every vertex of `H` has degree at least `d`, the number of connected components
times `d + 1` is at most `|W|`. -/
theorem num_components_le (H : SimpleGraph W) (d : ℕ)
    (hd : ∀ v : W, d ≤ (H.neighborSet v).ncard) :
    Fintype.card H.ConnectedComponent * (d + 1) ≤ Fintype.card W := by
  have sum_supp_card :
      ∑ c : H.ConnectedComponent, c.supp.toFinset.card = Fintype.card W := by
    rw [← Finset.card_univ, ← Finset.card_biUnion]
    · congr 1
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Set.mem_toFinset]
      exact ⟨fun _ => trivial,
        fun _ => ⟨H.connectedComponentMk v, (ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩⟩
    · intro c₁ _ c₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left]
      intro v h1 h2
      rw [Set.mem_toFinset, ConnectedComponent.mem_supp_iff] at h1 h2
      exact hne (h1 ▸ h2)
  rw [← sum_supp_card]
  have hge : ∀ c : H.ConnectedComponent, d + 1 ≤ c.supp.toFinset.card := by
    intro c
    rw [← Set.ncard_eq_toFinset_card']
    obtain ⟨v, hv⟩ := c.exists_rep
    have h := comp_supp_card_ge H v
    have hvc : H.connectedComponentMk v = c := hv
    rw [hvc] at h
    have := hd v
    omega
  calc Fintype.card H.ConnectedComponent * (d + 1)
      = ∑ _c : H.ConnectedComponent, (d + 1) := by
        rw [Finset.sum_const, Finset.card_univ]; ring
    _ ≤ ∑ c : H.ConnectedComponent, c.supp.toFinset.card :=
        Finset.sum_le_sum (fun c _ => hge c)

/-- The number of odd components is at most the total number of components. -/
theorem oddComponents_ncard_le (H : SimpleGraph W) :
    H.oddComponents.ncard ≤ Fintype.card H.ConnectedComponent := by
  calc H.oddComponents.ncard ≤ (Set.univ : Set H.ConnectedComponent).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    _ = Nat.card H.ConnectedComponent := Set.ncard_univ _
    _ = Fintype.card H.ConnectedComponent := Nat.card_eq_fintype_card

/-- Degree in the induced subgraph on `W \ u` is at least `δ(G) − |u|`. -/
theorem induced_degree_ge (G : SimpleGraph W) [DecidableRel G.Adj] (u : Finset W)
    (w : ((⊤ : G.Subgraph).deleteVerts (↑u : Set W)).verts) :
    G.minDegree - u.card ≤
      (((⊤ : G.Subgraph).deleteVerts (↑u : Set W)).coe.neighborSet w).ncard := by
  classical
  have hwu : (w : W) ∉ u := by
    have := w.2
    simp only [SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
      Set.mem_diff, Set.mem_univ, true_and, Finset.mem_coe] at this
    exact this
  have hinj : (((⊤ : G.Subgraph).deleteVerts (↑u:Set W)).coe.neighborSet w).ncard
      = ((G.neighborFinset (w : W)) \ u).card := by
    rw [Set.ncard_eq_toFinset_card']
    apply Finset.card_bij (fun (b : ((⊤ : G.Subgraph).deleteVerts (↑u:Set W)).verts)
        (_ : b ∈ _) => (b : W))
    · intro b hb
      rw [Set.mem_toFinset, SimpleGraph.mem_neighborSet, SimpleGraph.Subgraph.coe_adj] at hb
      simp only [SimpleGraph.Subgraph.deleteVerts_adj, SimpleGraph.Subgraph.top_adj,
        SimpleGraph.Subgraph.verts_top, Set.mem_univ, true_and, Finset.mem_coe] at hb
      simp only [Finset.mem_sdiff, mem_neighborFinset]
      exact ⟨hb.2.2, hb.2.1⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro c hc
      simp only [Finset.mem_sdiff, mem_neighborFinset] at hc
      have hcv : c ∈ ((⊤ : G.Subgraph).deleteVerts (↑u:Set W)).verts := by
        simp only [SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top,
          Set.mem_diff, Set.mem_univ, true_and, Finset.mem_coe]
        exact hc.2
      refine ⟨⟨c, hcv⟩, ?_, rfl⟩
      rw [Set.mem_toFinset, SimpleGraph.mem_neighborSet, SimpleGraph.Subgraph.coe_adj]
      simp only [SimpleGraph.Subgraph.deleteVerts_adj, SimpleGraph.Subgraph.top_adj,
        SimpleGraph.Subgraph.verts_top, Set.mem_univ, true_and, Finset.mem_coe]
      exact ⟨hwu, hc.2, hc.1⟩
  rw [hinj]
  have h1 : G.minDegree ≤ (G.neighborFinset (w:W)).card := by
    rw [card_neighborFinset_eq_degree]; exact G.minDegree_le_degree _
  have h2 : (G.neighborFinset (w:W)).card ≤ ((G.neighborFinset (w:W)) \ u).card + u.card :=
    Finset.card_le_card_sdiff_add_card
  omega

/-- Pure-`ℕ` arithmetic core behind the Tutte-count bound: from a component-count bound,
a trivial component bound, the parity fact and the size relations, the number of odd
components is at most `m`. -/
private lemma arith_core {O K V n d m : ℕ}
    (hOK : O ≤ K) (hK : K * (d - m + 1) ≤ V) (hK0 : K ≤ V)
    (hVn : V = n - m) (hmn : m ≤ n) (hn2d : n ≤ 2 * d)
    (hev : Even n) (hpar : Odd O ↔ Odd V) : O ≤ m := by
  by_cases hm0 : m = 0
  · subst hm0
    have hK1 : K ≤ 1 := by
      by_contra hc
      push_neg at hc
      have h2 : 2 * (d - 0 + 1) ≤ K * (d - 0 + 1) := Nat.mul_le_mul_right _ hc
      omega
    have hOle1 : O ≤ 1 := le_trans hOK hK1
    have hevV : Even V := by rw [hVn]; simpa using hev
    have hnodd : ¬ Odd O := by rw [hpar]; exact Nat.not_odd_iff_even.mpr hevV
    have hevO : Even O := Nat.not_odd_iff_even.mp hnodd
    rcases hevO with ⟨t, ht⟩
    omega
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    by_cases hmd : d ≤ m
    · omega
    · push_neg at hmd
      obtain ⟨a, hda, ha1⟩ : ∃ a, d = m + a ∧ 1 ≤ a := ⟨d - m, by omega, by omega⟩
      by_contra hcon
      push_neg at hcon
      have hKm : m + 1 ≤ K := by omega
      have hK' : K * (d - m + 1) ≤ n - m := by rw [← hVn]; exact hK
      have h3 : (m + 1) * (a + 1) ≤ n - m := by
        have := le_trans (Nat.mul_le_mul_right (d - m + 1) hKm) hK'
        have hae : d - m + 1 = a + 1 := by omega
        rwa [hae] at this
      have hb : n - m ≤ m + 2 * a := by omega
      have hexp : (m + 1) * (a + 1) = m * a + m + a + 1 := by ring
      rw [hexp] at h3
      have hma : a ≤ m * a := Nat.le_mul_of_pos_left a (by omega)
      omega

/-- **No Tutte violator at high minimum degree (even case).**  A finite graph with an even
number of vertices and `|V| ≤ 2·δ(G)` has no Tutte violator. -/
theorem no_tutte_violator_of_minDegree (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : Even (Fintype.card W)) (hcard : Fintype.card W ≤ 2 * G.minDegree)
    (u : Set W) : ¬ G.IsTutteViolator u := by
  classical
  simp only [SimpleGraph.IsTutteViolator, not_lt]
  obtain ⟨uF, huF⟩ : ∃ uF : Finset W, (↑uF : Set W) = u := ⟨u.toFinset, Set.coe_toFinset u⟩
  rw [← huF, Set.ncard_coe_finset]
  have hcardV : Fintype.card ((⊤ : G.Subgraph).deleteVerts (↑uF : Set W)).verts
      = Fintype.card W - uF.card := by
    rw [SimpleGraph.Subgraph.deleteVerts_verts, SimpleGraph.Subgraph.verts_top]
    have h : (Set.univ \ (↑uF : Set W)) = ((univ \ uF : Finset W) : Set W) := by simp
    rw [h]
    simp only [SetLike.coe_sort_coe, Fintype.card_coe]
    rw [Finset.card_univ_diff]
  have hK := num_components_le ((⊤ : G.Subgraph).deleteVerts (↑uF : Set W)).coe
    (G.minDegree - uF.card) (fun w => induced_degree_ge G uF w)
  have hK0 := num_components_le ((⊤ : G.Subgraph).deleteVerts (↑uF : Set W)).coe 0
    (fun _ => Nat.zero_le _)
  simp only [zero_add, mul_one] at hK0
  have hOK := oddComponents_ncard_le ((⊤ : G.Subgraph).deleteVerts (↑uF : Set W)).coe
  have hpar := SimpleGraph.odd_ncard_oddComponents
    ((⊤ : G.Subgraph).deleteVerts (↑uF : Set W)).coe
  rw [Nat.card_eq_fintype_card] at hpar
  have hnm : uF.card ≤ Fintype.card W := by simpa using Finset.card_le_univ uF
  exact arith_core hOK hK hK0 hcardV hnm hcard hev hpar

/-- **Perfect matching at high minimum degree (even case).** -/
theorem exists_isPerfectMatching_of_minDegree (G : SimpleGraph W) [DecidableRel G.Adj]
    (hev : Even (Fintype.card W)) (hcard : Fintype.card W ≤ 2 * G.minDegree) :
    ∃ M : G.Subgraph, M.IsPerfectMatching :=
  SimpleGraph.tutte.mpr (fun u => no_tutte_violator_of_minDegree G hev hcard u)

end Plantholt
