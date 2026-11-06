/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.RestrictedQuotientTransport

@[expose] public section

/-! Pure transport of physical hinge modes. Local candidate; NOT kernel-checked. -/

open Finset
noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

def restrictEdgeSet (Z : Finset V) (J : Finset (Sym2 V)) : Finset (Sym2 (Survivors Z)) :=
  univ.filter (fun e => Sym2.map Subtype.val e ∈ J)

lemma mem_restrictEdgeSet (Z : Finset V) (J : Finset (Sym2 V))
    (e : Sym2 (Survivors Z)) : e ∈ restrictEdgeSet Z J ↔ Sym2.map Subtype.val e ∈ J := by
  simp [restrictEdgeSet]

lemma liftVertexSet_triple (Z : Finset V) (u v a : Survivors Z) :
    liftVertexSet Z {u,v,a} = {u.1,v.1,a.1} := by
  simp [liftVertexSet, survivingVertexEmbedding]

lemma mem_triEdges_subtypeVertexSet (Z T : Finset V) (hd : Disjoint T Z)
    (e : Sym2 (Survivors Z)) :
    e ∈ triEdges (T.subtype (fun v => v ∉ Z)) ↔ Sym2.map Subtype.val e ∈ triEdges T := by
  rw [← mem_triEdges_liftVertexSet, lift_subtypeVertexSet Z T hd]

lemma isAllowed_restricted_triple (H : Host V I) (F : Set (Multiset I))
    (Z : Finset V) (u v a : Survivors Z) :
    IsAllowed (restrictedHost H Z) F {u,v,a} ↔ IsAllowed H F {u.1,v.1,a.1} := by
  rw [isAllowed_liftVertexSet_iff, liftVertexSet_triple, isAllowed_vertexDeleted_iff]
  have hd : Disjoint ({u.1,v.1,a.1} : Finset V) Z := by
    rw [Finset.disjoint_left]
    intro w hw hwZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    exacts [u.2 hwZ, v.2 hwZ, a.2 hwZ]
  simp only [hd, and_true]

lemma restrictEdgeSet_union (Z : Finset V) (J K : Finset (Sym2 V)) :
    restrictEdgeSet Z (J ∪ K) = restrictEdgeSet Z J ∪ restrictEdgeSet Z K := by
  ext e
  simp only [mem_restrictEdgeSet, Finset.mem_union]

lemma restrictEdgeSet_wedge (Z : Finset V) (u v a : Survivors Z) :
    restrictEdgeSet Z (wedge u.1 v.1 a.1) = wedge u v a := by
  classical
  ext e
  have h (x y : Survivors Z) :
      Sym2.map Subtype.val e = s(x.1,y.1) ↔ e = s(x,y) := by
    change Sym2.map Subtype.val e = Sym2.map Subtype.val s(x,y) ↔ e = s(x,y)
    exact (Sym2.map.injective Subtype.val_injective).eq_iff
  simp only [mem_restrictEdgeSet, wedge, Finset.mem_insert, Finset.mem_singleton, h]

lemma avoid_edge_of_support_avoids (Z : Finset V) {J : Finset (Sym2 V)}
    (hd : Disjoint (support J) Z) {e : Sym2 V} (he : e ∈ J) : ∀ v ∈ e, v ∉ Z := by
  intro v hv hvZ
  apply Finset.disjoint_left.1 hd _ hvZ
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e, he, hv⟩

lemma support_restrictEdgeSet_iff (Z : Finset V) (J : Finset (Sym2 V))
    (hd : Disjoint (support J) Z) (v : Survivors Z) :
    v ∈ support (restrictEdgeSet Z J) ↔ v.1 ∈ support J := by
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, he, hv⟩
    exact ⟨Sym2.map Subtype.val e, (mem_restrictEdgeSet Z J e).1 he,
      Sym2.mem_map.2 ⟨v,hv,rfl⟩⟩
  · rintro ⟨e, he, hv⟩
    have hav := avoid_edge_of_support_avoids Z hd he
    refine ⟨e.attachWith hav, (mem_restrictEdgeSet Z J _).2 ?_, ?_⟩
    · simpa only [Sym2.attachWith_map_subtypeVal] using he
    · rw [← Sym2.attachWith_map_subtypeVal hav] at hv
      obtain ⟨w, hw, heq⟩ := Sym2.mem_map.1 hv
      have hwv : w = v := Subtype.ext heq
      simpa only [hwv] using hw

lemma card_support_restrictEdgeSet (Z : Finset V) (J : Finset (Sym2 V))
    (hd : Disjoint (support J) Z) :
    (support (restrictEdgeSet Z J)).card = (support J).card := by
  refine Finset.card_bij (fun v _ => v.1) ?_ ?_ ?_
  · intro v hv
    exact (support_restrictEdgeSet_iff Z J hd v).1 hv
  · intro v _ w _ heq
    exact Subtype.ext heq
  · intro v hv
    have hvZ : v ∉ Z := fun h => Finset.disjoint_left.1 hd hv h
    exact ⟨⟨v,hvZ⟩,(support_restrictEdgeSet_iff Z J hd ⟨v,hvZ⟩).2 hv,rfl⟩

lemma restrictEdgeSet_injective_on_avoiding (Z : Finset V) {J K : Finset (Sym2 V)}
    (hJ : Disjoint (support J) Z) (hK : Disjoint (support K) Z)
    (heq : restrictEdgeSet Z J = restrictEdgeSet Z K) : J = K := by
  have step : ∀ (A B : Finset (Sym2 V)), Disjoint (support A) Z →
      restrictEdgeSet Z A = restrictEdgeSet Z B → A ⊆ B := by
    intro A B hA hAB e he
    have hav := avoid_edge_of_support_avoids Z hA he
    have hm : e.attachWith hav ∈ restrictEdgeSet Z A := by
      rw [mem_restrictEdgeSet, Sym2.attachWith_map_subtypeVal]
      exact he
    rw [hAB, mem_restrictEdgeSet, Sym2.attachWith_map_subtypeVal] at hm
    exact hm
  exact Finset.Subset.antisymm (step J K hJ heq) (step K J hK heq.symm)

lemma edges_deleted_of_supported (H : Host V I) (Z : Finset V)
    {J : Finset (Sym2 V)} (hJ : J ⊆ edges H) (hd : Disjoint (support J) Z) :
    J ⊆ edges (vertexDeleted H Z) := by
  intro e he
  refine (edges_vertexDeleted_iff H Z e).2 ⟨hJ he, ?_⟩
  intro z hz hze
  exact avoid_edge_of_support_avoids Z hd he z hze hz

lemma isDecomposition_restrictEdgeSet (H : Host V I) (F : Set (Multiset I))
    (Z : Finset V) {J : Finset (Sym2 V)} {D : Finset (Finset V)}
    (hD : IsDecomposition H F J D) (hJ : J ⊆ edges (vertexDeleted H Z)) :
    IsDecomposition (restrictedHost H Z) F (restrictEdgeSet Z J)
      (D.image (fun T => T.subtype (fun v => v ∉ Z))) := by
  classical
  have hallowed : ∀ T ∈ D, IsAllowed (vertexDeleted H Z) F T := by
    intro T hT
    refine ⟨(hD.1 T hT).1, ?_, (hD.1 T hT).2.2⟩
    intro x hx y hy hxy
    have he := hJ (hD.subset hT (mem_triEdges.2 ⟨hx,hy,hxy⟩))
    have hadj : (vertexDeleted H Z).G.Adj x y := (Finset.mem_filter.mp he).2
    exact hadj
  have hd : ∀ T ∈ D, Disjoint T Z := fun T hT =>
    ((isAllowed_vertexDeleted_iff H F Z T).1 (hallowed T hT)).2
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.1 hT
    exact isAllowed_subtypeVertexSet H F Z S (hallowed S hS)
  · intro T hT U hU hTU
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.1 hT
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.1 hU
    have hAB : A ≠ B := fun h => hTU (congrArg (fun S => S.subtype (fun v => v ∉ Z)) h)
    change Disjoint (triEdges (A.subtype (fun v => v ∉ Z)))
      (triEdges (B.subtype (fun v => v ∉ Z)))
    rw [Finset.disjoint_left]
    intro e heA heB
    exact Finset.disjoint_left.1 (hD.2.1 hA hB hAB)
      ((mem_triEdges_subtypeVertexSet Z A (hd A hA) e).1 heA)
      ((mem_triEdges_subtypeVertexSet Z B (hd B hB) e).1 heB)
  · ext e
    rw [mem_restrictEdgeSet, ← hD.2.2]
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨T,hT,he⟩
      obtain ⟨A,hA,rfl⟩ := Finset.mem_image.1 hT
      exact ⟨A,hA,(mem_triEdges_subtypeVertexSet Z A (hd A hA) e).1 he⟩
    · rintro ⟨A,hA,he⟩
      exact ⟨A.subtype (fun v => v ∉ Z), Finset.mem_image.2 ⟨A,hA,rfl⟩,
        (mem_triEdges_subtypeVertexSet Z A (hd A hA) e).2 he⟩

theorem isHinge_restrictEdgeSet (H : Host V I) (F : Set (Multiset I))
    (Z : Finset V) (u v a b : Survivors Z) {J : Finset (Sym2 V)}
    (hJ : IsHinge H F u.1 v.1 a.1 b.1 J) (hd : Disjoint (support J) Z)
    (hTa : IsAllowed H F {u.1,v.1,a.1}) (hTb : IsAllowed H F {u.1,v.1,b.1}) :
    IsHinge (restrictedHost H Z) F u v a b (restrictEdgeSet Z J) := by
  classical
  have hJdel := edges_deleted_of_supported H Z hJ.1 hd
  have hW (c : Survivors Z) (hTc : IsAllowed H F {u.1,v.1,c.1}) :
      J ∪ wedge u.1 v.1 c.1 ⊆ edges (vertexDeleted H Z) := by
    have hc := (isAllowed_restricted_triple H F Z u v c).2 hTc
    have hcdel := (isAllowed_liftVertexSet_iff H F Z {u,v,c}).1 hc
    rw [liftVertexSet_triple] at hcdel
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · exact hJdel he
    · apply triEdges_subset_edges hcdel
      have hsub : wedge u.1 v.1 c.1 ⊆ triEdges {u.1,v.1,c.1} := by
        intro f hf
        induction f using Sym2.ind with
        | _ x y =>
          simp only [wedge, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at hf
          have hdist := distinct_of_card_three hTc.1
          rcases hf with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) | (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;>
            apply mem_triEdges.2 <;> simp_all [ne_comm]
      exact hsub he
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    exact (mem_edges_restrictedHost H Z e).1 (hJdel ((mem_restrictEdgeSet Z J e).1 he))
  · rw [Finset.disjoint_left]
    intro e heJ heT
    have heT' : e ∈ triEdges ({u,v,a} : Finset (Survivors Z)) ∪
        triEdges ({u,v,b} : Finset (Survivors Z)) := by
      convert heT using 1 <;> congr 1 <;> first
        | (congr 1 <;> exact Subsingleton.elim _ _)
        | (ext f; simp [triEdges])
    have hmap : Sym2.map Subtype.val e ∈ triEdges {u.1,v.1,a.1} ∪ triEdges {u.1,v.1,b.1} := by
      rcases Finset.mem_union.1 heT' with he | he
      · apply Finset.mem_union_left
        rw [← liftVertexSet_triple Z u v a]
        exact (mem_triEdges_liftVertexSet Z {u,v,a} e).2 he
      · apply Finset.mem_union_right
        rw [← liftVertexSet_triple Z u v b]
        exact (mem_triEdges_liftVertexSet Z {u,v,b} e).2 he
    exact Finset.disjoint_left.1 hJ.2.1 ((mem_restrictEdgeSet Z J e).1 heJ) hmap
  · obtain ⟨D,hD⟩ := hJ.2.2.1
    have hc := isDecomposition_restrictEdgeSet H F Z hD (hW a hTa)
    rw [restrictEdgeSet_union, restrictEdgeSet_wedge] at hc
    refine ⟨D.image (fun T => T.subtype (fun v => v ∉ Z)), ?_⟩
    convert hc using 1 <;> ext e <;> simp
  · obtain ⟨D,hD⟩ := hJ.2.2.2
    have hc := isDecomposition_restrictEdgeSet H F Z hD (hW b hTb)
    rw [restrictEdgeSet_union, restrictEdgeSet_wedge] at hc
    refine ⟨D.image (fun T => T.subtype (fun v => v ∉ Z)), ?_⟩
    convert hc using 1 <;> ext e <;> simp

end TypedTriangle
