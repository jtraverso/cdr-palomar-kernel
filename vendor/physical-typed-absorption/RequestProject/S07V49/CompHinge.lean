/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V49.EdgeRoutes
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# V49 §3 — the two-hinge composition through a fresh apex, in the edge-deleted host

For roots `u v a b` and a fresh apex `t` (`uvt` allowed in `G \ B`, `t ∉ {a, b}`), an original
hinge `J₁` for `(uva, uvt)` and an original hinge `J₂` for `(uvt, uvb)` such that

* no edge of `J₁ ∪ J₂` is in `B`,
* `b ∉ supp J₁`, `a ∉ supp J₂`,
* the free vertices of `J₁` and `J₂` are disjoint,

compose (`composite_hinge`) into a hinge of `G \ B` for `(uva, uvb)`:

  `J = J₁ ∪ J₂ ∪ {ut, vt}`,  `J ∪ W_a = (J₁ ∪ W_a) ⊔ (J₂ ∪ W_t)`,  `J ∪ W_b = (J₁ ∪ W_t) ⊔ (J₂ ∪ W_b)`.

Its support is `supp J₁ ∪ supp J₂` with `supp J₁ ∩ supp J₂ = {u, v, t}`, so its order is EXACTLY
`i₁ + i₂ - 3 ≤ 2h - 3` (`card_support_composite`), and its free vertices are
`free(J₁) ∪ free(J₂) ∪ {t}` (`freeV_composite_subset`). The composite never uses the edge
`ab` nor any pair among the four fixed roots other than the six edges of `uva`, `uvb`; in
particular a deleted apex–apex edge `ab ∈ B` is harmless.
-/

open Finset

noncomputable section
open Classical

namespace S07V49

open TypedTriangle.SparseEdge S07V24

variable {V I : Type*} [Fintype V] {G B : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)}

lemma support_union (J K : Finset (Sym2 V)) : support (J ∪ K) = support J ∪ support K := by
  ext x; simp only [support, mem_filter, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨e, he | he, hx⟩
    exacts [Or.inl ⟨e, he, hx⟩, Or.inr ⟨e, he, hx⟩]
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    exacts [⟨e, Or.inl he, hx⟩, ⟨e, Or.inr he, hx⟩]

lemma support_wedge_subset (u v t : V) : support (wedge u v t) ⊆ {u, v, t} := by
  intro x hx
  simp only [support, mem_filter, mem_univ, true_and, wedge, mem_insert, mem_singleton] at hx
  obtain ⟨e, he, hx⟩ := hx
  rcases he with rfl | rfl <;> simp only [Sym2.mem_iff] at hx <;> simp <;> tauto

lemma not_mem_of_not_support {J : Finset (Sym2 V)} {x : V} (hx : x ∉ support J) (y : V) :
    s(x, y) ∉ J ∧ s(y, x) ∉ J :=
  ⟨fun h => hx (mem_support_of_mem h (by simp)), fun h => hx (mem_support_of_mem h (by simp))⟩

omit [Fintype V] in
lemma wedge_disjoint {u v a t : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hat : a ≠ t) :
    Disjoint (wedge u v a) (wedge u v t) := by
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [wedge, mem_insert, mem_singleton] at he he'
  rcases he with rfl | rfl <;> rcases he' with h | h <;> rw [Sym2.eq_iff] at h <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all

omit [Fintype V] in
lemma wedge_subset_triEdges {u v t : V} (huv : u ≠ v) (hut : u ≠ t) (hvt : v ≠ t) :
    wedge u v t ⊆ triEdges {u, v, t} := by
  rw [triEdges_triple huv hut hvt]; exact subset_insert _ _

/-- union of two edge-disjoint decompositions, transported to a host containing all edges -/
lemma dec_union {G' : SimpleGraph V} {X Y : Finset (Sym2 V)} {D1 D2 : Finset (Finset V)}
    (h1 : IsDecomposition G lab F X D1) (h2 : IsDecomposition G lab F Y D2)
    (hXY : Disjoint X Y) (hsub : X ∪ Y ⊆ edges G') :
    IsDecomposition G' lab F (X ∪ Y) (D1 ∪ D2) := by
  obtain ⟨a1, p1, e1⟩ := h1
  obtain ⟨a2, p2, e2⟩ := h2
  have hT1 : ∀ T ∈ D1, triEdges T ⊆ X := fun T hT => e1 ▸ subset_biUnion_of_mem _ hT
  have hT2 : ∀ T ∈ D2, triEdges T ⊆ Y := fun T hT => e2 ▸ subset_biUnion_of_mem _ hT
  refine ⟨fun T hT => ?_, ?_, by rw [union_biUnion, e1, e2]⟩
  · rcases mem_union.1 hT with hT | hT
    · exact isAllowed_of_triEdges_subset (a1 T hT)
        ((hT1 T hT).trans (subset_union_left.trans hsub))
    · exact isAllowed_of_triEdges_subset (a2 T hT)
        ((hT2 T hT).trans (subset_union_right.trans hsub))
  · intro T hT T' hT' hne
    simp only [coe_union, Set.mem_union, mem_coe] at hT hT'
    rcases hT with hT | hT <;> rcases hT' with hT' | hT'
    · exact p1 hT hT' hne
    · exact hXY.mono (hT1 T hT) (hT2 T' hT')
    · exact (hXY.mono (hT1 T' hT') (hT2 T hT)).symm
    · exact p2 hT hT' hne

/-- edges of a hinge are not diagonal and both ends are in the support -/
lemma hinge_edge_ends {J : Finset (Sym2 V)} {u v a b : V} (hJ : IsHinge G lab F u v a b J)
    {x y : V} (h : s(x, y) ∈ J) : x ≠ y ∧ x ∈ support J ∧ y ∈ support J := by
  refine ⟨fun hxy => ?_, mem_support_of_mem h (by simp), mem_support_of_mem h (by simp)⟩
  subst hxy
  exact not_isDiag_of_mem_edges (hJ.1 h) (by simp)

set_option maxHeartbeats 1000000 in
/-- **the two-hinge composition through a fresh apex `t`** -/
theorem composite_hinge {u v a b t : V} {J1 J2 : Finset (Sym2 V)}
    (hT : HingeTest (G \ B) lab F u v a b) (hTt : IsAllowed (G \ B) lab F {u, v, t})
    (hta : t ≠ a) (htb : t ≠ b)
    (hJ1 : IsHinge G lab F u v a t J1) (hJ2 : IsHinge G lab F u v t b J2)
    (hB1 : ∀ e ∈ J1, e ∉ B.edgeSet) (hB2 : ∀ e ∈ J2, e ∉ B.edgeSet)
    (hb1 : b ∉ support J1) (ha2 : a ∉ support J2)
    (hfree : Disjoint (freeV u v a t J1) (freeV u v t b J2)) :
    IsHinge (G \ B) lab F u v a b (J1 ∪ J2 ∪ wedge u v t) ∧
    support (J1 ∪ J2 ∪ wedge u v t) = support J1 ∪ support J2 ∧
    support J1 ∩ support J2 = {u, v, t} ∧ Disjoint J1 J2 ∧ Disjoint J2 (wedge u v t) := by
  obtain ⟨huv, hua, hva, hub, hvb, hab⟩ := roots_distinct hT
  obtain ⟨-, hut, hvt⟩ := distinct_of_allowed hTt
  have hR1 := S10V23.roots_subset_support' hJ1 huv hua hva hut hvt
  have hR2 := S10V23.roots_subset_support' hJ2 huv hut hvt hub hvb
  have hu1 : u ∈ support J1 := hR1 (by simp)
  have hv1 : v ∈ support J1 := hR1 (by simp)
  have ha1 : a ∈ support J1 := hR1 (by simp)
  have ht1 : t ∈ support J1 := hR1 (by simp)
  have hu2 : u ∈ support J2 := hR2 (by simp)
  have hv2 : v ∈ support J2 := hR2 (by simp)
  have ht2 : t ∈ support J2 := hR2 (by simp)
  have hb2 : b ∈ support J2 := hR2 (by simp)
  -- the support intersection
  have hinter : support J1 ∩ support J2 = {u, v, t} := by
    ext x
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hx1, hx2⟩
      by_contra hx
      push_neg at hx
      obtain ⟨hxu, hxv, hxt⟩ := hx
      have hxa : x ≠ a := by rintro rfl; exact ha2 hx2
      have hxb : x ≠ b := by rintro rfl; exact hb1 hx1
      have f1 : x ∈ freeV u v a t J1 := by
        simp only [freeV, mem_sdiff, mem_insert, mem_singleton]; tauto
      have f2 : x ∈ freeV u v t b J2 := by
        simp only [freeV, mem_sdiff, mem_insert, mem_singleton]; tauto
      exact Finset.disjoint_left.1 hfree f1 f2
    · rintro (rfl | rfl | rfl)
      exacts [⟨hu1, hu2⟩, ⟨hv1, hv2⟩, ⟨ht1, ht2⟩]
  -- `J1` and `J2` are edge-disjoint
  have hJ12 : Disjoint J1 J2 := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    induction e using Sym2.ind with
    | _ x y =>
    obtain ⟨hxy, hx1, hy1⟩ := hinge_edge_ends hJ1 he1
    obtain ⟨-, hx2, hy2⟩ := hinge_edge_ends hJ2 he2
    have hx : x ∈ ({u, v, t} : Finset V) := hinter ▸ mem_inter.2 ⟨hx1, hx2⟩
    have hy : y ∈ ({u, v, t} : Finset V) := hinter ▸ mem_inter.2 ⟨hy1, hy2⟩
    exact Finset.disjoint_left.1 hJ1.2.1 he1
      (mem_union_right _ (mem_triEdges.2 ⟨hx, hy, hxy⟩))
  -- wedges against hinges
  have hJ1t : Disjoint J1 (wedge u v t) :=
    hJ1.2.1.mono_right ((wedge_subset_triEdges huv hut hvt).trans subset_union_right)
  have hJ2t : Disjoint J2 (wedge u v t) :=
    hJ2.2.1.mono_right ((wedge_subset_triEdges huv hut hvt).trans subset_union_left)
  have hJ1b : Disjoint J1 (wedge u v b) := by
    rw [Finset.disjoint_right]
    intro e he
    simp only [wedge, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    exacts [(not_mem_of_not_support hb1 u).2, (not_mem_of_not_support hb1 v).2]
  have hJ2a : Disjoint J2 (wedge u v a) := by
    rw [Finset.disjoint_right]
    intro e he
    simp only [wedge, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    exacts [(not_mem_of_not_support ha2 u).2, (not_mem_of_not_support ha2 v).2]
  have hwat : Disjoint (wedge u v a) (wedge u v t) := wedge_disjoint huv hua hva (Ne.symm hta)
  have hwtb : Disjoint (wedge u v t) (wedge u v b) := wedge_disjoint huv hut hvt htb
  -- edges of `G \ B`
  have hsd : ∀ e, e ∈ edges G → e ∉ B.edgeSet → e ∈ edges (G \ B) := by
    intro e he hB
    rw [mem_edges, SimpleGraph.edgeSet_sdiff]
    exact ⟨mem_edges.1 he, hB⟩
  have hE1 : J1 ⊆ edges (G \ B) := fun e he => hsd e (hJ1.1 he) (hB1 e he)
  have hE2 : J2 ⊆ edges (G \ B) := fun e he => hsd e (hJ2.1 he) (hB2 e he)
  have hwedge : ∀ c, IsAllowed (G \ B) lab F {u, v, c} → u ≠ c → v ≠ c →
      wedge u v c ⊆ edges (G \ B) := fun c hc huc hvc =>
    (wedge_subset_triEdges huv huc hvc).trans (triEdges_subset_edges hc)
  have hEa := hwedge a hT.2.1 hua hva
  have hEb := hwedge b hT.2.2 hub hvb
  have hEt := hwedge t hTt hut hvt
  -- support of the composite
  have hsupp : support (J1 ∪ J2 ∪ wedge u v t) = support J1 ∪ support J2 := by
    rw [support_union, support_union]
    apply union_eq_left.2
    intro x hx
    have := support_wedge_subset u v t hx
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | rfl | rfl
    exacts [mem_union_left _ hu1, mem_union_left _ hv1, mem_union_left _ ht1]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hsupp, hinter, hJ12, hJ2t⟩
  · exact union_subset (union_subset hE1 hE2) hEt
  · -- disjoint from the two root triangles
    rw [Finset.disjoint_left]
    intro e he hE
    rw [mem_union, mem_union] at he
    rcases he with (he | he) | he
    · rcases mem_union.1 hE with hE | hE
      · exact Finset.disjoint_left.1 hJ1.2.1 he (mem_union_left _ hE)
      · rw [triEdges_triple huv hub hvb, mem_insert] at hE
        rcases hE with rfl | hE
        · exact Finset.disjoint_left.1 hJ1.2.1 he
            (mem_union_left _ (mem_triEdges.2 ⟨by simp, by simp, huv⟩))
        · exact Finset.disjoint_left.1 hJ1b he hE
    · rcases mem_union.1 hE with hE | hE
      · rw [triEdges_triple huv hua hva, mem_insert] at hE
        rcases hE with rfl | hE
        · exact Finset.disjoint_left.1 hJ2.2.1 he
            (mem_union_right _ (mem_triEdges.2 ⟨by simp, by simp, huv⟩))
        · exact Finset.disjoint_left.1 hJ2a he hE
      · exact Finset.disjoint_left.1 hJ2.2.1 he (mem_union_right _ hE)
    · simp only [wedge, mem_insert, mem_singleton] at he
      rcases he with rfl | rfl <;> rcases mem_union.1 hE with hE | hE <;>
        rw [mem_triEdges] at hE <;> obtain ⟨-, h, -⟩ := hE <;>
        simp only [mem_insert, mem_singleton] at h <;> rcases h with h | h | h <;>
        first | exact hut h.symm | exact hvt h.symm | exact hta h | exact htb h
  · -- `J ∪ W_a = (J1 ∪ W_a) ∪ (J2 ∪ W_t)`
    obtain ⟨D1, hD1⟩ := hJ1.2.2.1
    obtain ⟨D2, hD2⟩ := hJ2.2.2.1
    have hdisj : Disjoint (J1 ∪ wedge u v a) (J2 ∪ wedge u v t) := by
      rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
      exact ⟨⟨hJ12, hJ1t⟩, hJ2a.symm, hwat⟩
    have := dec_union (G' := G \ B) hD1 hD2 hdisj
      (union_subset (union_subset hE1 hEa) (union_subset hE2 hEt))
    have heq : J1 ∪ J2 ∪ wedge u v t ∪ wedge u v a =
        (J1 ∪ wedge u v a) ∪ (J2 ∪ wedge u v t) := by
      ext e; simp only [mem_union]; tauto
    exact ⟨D1 ∪ D2, heq ▸ this⟩
  · -- `J ∪ W_b = (J1 ∪ W_t) ∪ (J2 ∪ W_b)`
    obtain ⟨D1, hD1⟩ := hJ1.2.2.2
    obtain ⟨D2, hD2⟩ := hJ2.2.2.2
    have hdisj : Disjoint (J1 ∪ wedge u v t) (J2 ∪ wedge u v b) := by
      rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
      exact ⟨⟨hJ12, hJ1b⟩, hJ2t.symm, hwtb⟩
    have := dec_union (G' := G \ B) hD1 hD2 hdisj
      (union_subset (union_subset hE1 hEt) (union_subset hE2 hEb))
    have heq : J1 ∪ J2 ∪ wedge u v t ∪ wedge u v b =
        (J1 ∪ wedge u v t) ∪ (J2 ∪ wedge u v b) := by
      ext e; simp only [mem_union]; tauto
    exact ⟨D1 ∪ D2, heq ▸ this⟩

/-- **exact order of the composite**: `i₁ + i₂ - 3` -/
theorem card_support_composite {u v t : V} {J1 J2 : Finset (Sym2 V)}
    (hsupp : support J1 ∩ support J2 = {u, v, t}) (huv : u ≠ v) (hut : u ≠ t) (hvt : v ≠ t) :
    (support J1 ∪ support J2).card + 3 = (support J1).card + (support J2).card := by
  have := card_union_add_card_inter (support J1) (support J2)
  rw [hsupp, card_three_of_distinct huv hut hvt] at this
  exact this

/-- **free vertices of the composite** -/
theorem freeV_composite_subset {u v a b t : V} {J1 J2 : Finset (Sym2 V)} {U : Finset V}
    (hsupp : support (J1 ∪ J2 ∪ wedge u v t) = support J1 ∪ support J2)
    (h1 : freeV u v a t J1 ⊆ U) (h2 : freeV u v t b J2 ⊆ U) (htU : t ∈ U) :
    freeV u v a b (J1 ∪ J2 ∪ wedge u v t) ⊆ U := by
  intro x hx
  simp only [freeV, mem_sdiff, mem_insert, mem_singleton, hsupp, mem_union] at hx
  obtain ⟨hx | hx, hxr⟩ := hx
  · by_cases hxt : x = t
    · exact hxt ▸ htU
    · exact h1 (by simp only [freeV, mem_sdiff, mem_insert, mem_singleton]; tauto)
  · by_cases hxt : x = t
    · exact hxt ▸ htU
    · exact h2 (by simp only [freeV, mem_sdiff, mem_insert, mem_singleton]; tauto)

end S07V49
