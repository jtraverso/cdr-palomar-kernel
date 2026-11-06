/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V25.AltPath
public import RequestProject.S07.HingeCore
public import RequestProject.TypedTriangle.ComponentRows

@[expose] public section

/-!
# V25 — every ORIGINAL hinge contains an even path of the link `L_v` from `a` to `b`

Let `J` be a hinge (`SparseEdgeDefs.IsHinge`, unchanged) for the roots `u, v, a, b`. In the
decomposition of `J ∪ {ua, va}` into allowed triangles, the triangles through `v` pair up the
vertices `N_J(v) ∪ {a}` (a perfect matching of the typed link `L_v = ComponentRows.link G lab F v`);
likewise for `J ∪ {ub, vb}` on `N_J(v) ∪ {b}`. By `alt_path` there is a path of `L_v` from `a`
to `b` of EVEN length with all vertices in `support J ∖ {u, v}` and no edge equal to `s(a, b)`.
-/

open Finset Classical

namespace S07V25

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows

variable {V I : Type*} [Fintype V]

/-- the matching of a decomposition at the root `v` -/
def matchRel (v : V) (D : Finset (Finset V)) (x y : V) : Prop := x ≠ y ∧ ({v, x, y} : Finset V) ∈ D

/-- the vertices joined to `v` by `J ∪ W_c` -/
noncomputable def matchSet (v c : V) (J : Finset (Sym2 V)) : Finset V :=
  insert c (univ.filter (fun x => s(v, x) ∈ J))

lemma decomp_pmatch {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {u v c : V}
    {J : Finset (Sym2 V)} {D : Finset (Finset V)} (huv : u ≠ v) (hvc : v ≠ c)
    (hD : IsDecomposition G lab F (J ∪ wedge u v c) D) :
    PMatch (link G lab F v) (matchRel v D) (matchSet v c J) := by
  obtain ⟨hall, hdisj, heq⟩ := hD
  have hvx : ∀ x y, ({v, x, y} : Finset V) ∈ D → v ≠ x ∧ v ≠ y ∧ x ≠ y := fun x y h =>
    distinct_of_card_three (hall _ h).1
  have hsymm : ∀ x y, matchRel v D x y → matchRel v D y x := by
    rintro x y ⟨hxy, hT⟩
    refine ⟨hxy.symm, ?_⟩
    rwa [Finset.pair_comm]
  refine ⟨hsymm, ?_, ?_, ?_, ?_⟩
  · rintro x y y' ⟨hxy, hT⟩ ⟨hxy', hT'⟩
    obtain ⟨hv1, hv2, -⟩ := hvx x y hT
    obtain ⟨-, hv2', -⟩ := hvx x y' hT'
    have hEq : ({v, x, y} : Finset V) = {v, x, y'} := by
      by_contra hne
      have := hdisj hT hT' hne
      exact Finset.disjoint_left.1 this (mem_triEdges.2 ⟨by simp, by simp, hv1⟩)
        (mem_triEdges.2 ⟨by simp, by simp, hv1⟩)
    have : y ∈ ({v, x, y'} : Finset V) := hEq ▸ by simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h | h
    · exact absurd h.symm hv2
    · exact absurd h.symm hxy
    · exact h
  · rintro x y ⟨hxy, hT⟩
    exact ⟨hxy, by convert hall _ hT⟩
  · intro x hx
    have hmem : s(v, x) ∈ J ∪ wedge u v c := by
      simp only [matchSet, mem_insert, mem_filter, mem_univ, true_and] at hx
      rcases hx with rfl | hx
      · simp [wedge]
      · exact mem_union_left _ hx
    rw [← heq] at hmem
    obtain ⟨T, hTD, hvT⟩ := mem_biUnion.1 hmem
    obtain ⟨hv, hxT, hvx'⟩ := mem_triEdges.1 hvT
    obtain ⟨y, hyv, hyx, rfl⟩ := eq_triple_of_mem (hall T hTD).1 hv hxT hvx'
    exact ⟨y, hyx.symm, hTD⟩
  · rintro x - y ⟨hxy, hT⟩
    obtain ⟨-, hvy, -⟩ := hvx x y hT
    have hmem : s(v, y) ∈ J ∪ wedge u v c := by
      rw [← heq]; exact mem_biUnion.2 ⟨_, hT, mem_triEdges.2 ⟨by simp, by simp, hvy⟩⟩
    simp only [matchSet, mem_insert, mem_filter, mem_univ, true_and]
    rcases mem_union.1 hmem with h | h
    · exact Or.inr h
    · simp only [wedge, mem_insert, mem_singleton, Sym2.eq_iff] at h
      rcases h with (⟨h1, -⟩ | ⟨h1, -⟩) | (⟨-, h2⟩ | ⟨h1, -⟩)
      · exact absurd h1.symm huv
      · exact absurd h1 hvc
      · exact Or.inl h2
      · exact absurd h1 hvc

/-- **the even link path inside a hinge** -/
theorem hinge_path {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {u v a b : V}
    {J : Finset (Sym2 V)} (hJ : IsHinge G lab F u v a b J)
    (hd : u ≠ v ∧ u ≠ a ∧ v ≠ a ∧ u ≠ b ∧ v ≠ b ∧ a ≠ b) :
    ∃ p : (link G lab F v).Walk a b, p.IsPath ∧ Even p.length ∧
      (∀ x ∈ p.support, x ∈ support J ∧ x ≠ u ∧ x ≠ v) ∧
      ∀ e ∈ p.edges, e ≠ s(a, b) := by
  obtain ⟨huv, hua, hva, hub, hvb, hab⟩ := hd
  obtain ⟨hJE, hJdisj, ⟨Da, hDa⟩, ⟨Db, hDb⟩⟩ := hJ
  have hA := decomp_pmatch huv hva hDa
  have hB := decomp_pmatch huv hvb hDb
  have hva_J : s(v, a) ∉ J := fun h => Finset.disjoint_left.1 hJdisj h
    (mem_union_left _ (mem_triEdges.2 ⟨by simp, by simp, hva⟩))
  have hvb_J : s(v, b) ∉ J := fun h => Finset.disjoint_left.1 hJdisj h
    (mem_union_right _ (mem_triEdges.2 ⟨by simp, by simp, hvb⟩))
  have hvu_J : s(v, u) ∉ J := fun h => Finset.disjoint_left.1 hJdisj h
    (mem_union_left _ (mem_triEdges.2 ⟨by simp, by simp, huv.symm⟩))
  have hvv_J : s(v, v) ∉ J := fun h => S10V23.hinge_no_diag
    (⟨hJE, hJdisj, ⟨Da, hDa⟩, ⟨Db, hDb⟩⟩ : IsHinge G lab F u v a b J) _ h (Sym2.mk_isDiag_iff.2 rfl)
  have mA : ∀ {x}, x ∈ matchSet v a J ↔ x = a ∨ s(v, x) ∈ J := by
    intro x; simp [matchSet]
  have mB : ∀ {x}, x ∈ matchSet v b J ↔ x = b ∨ s(v, x) ∈ J := by
    intro x; simp [matchSet]
  obtain ⟨p, hp, hpe, hps, hpE⟩ := alt_path (link G lab F v) (matchRel v Da) (matchRel v Db)
    (matchSet v a J).card (matchSet v a J) (matchSet v b J) a b le_rfl hA hB
    (mA.2 (Or.inl rfl)) (by rw [mB]; rintro (h | h); exacts [hab h, hva_J h])
    (mB.2 (Or.inl rfl)) (by rw [mA]; rintro (h | h); exacts [hab h.symm, hvb_J h])
    (by intro z hz hz'; rw [mA] at hz; rw [mB] at hz'; tauto)
    (by intro z hz hz'; rw [mB] at hz; rw [mA] at hz'; tauto)
  have hroots := S10V23.roots_subset_support' (⟨hJE, hJdisj, ⟨Da, hDa⟩, ⟨Db, hDb⟩⟩ :
    IsHinge G lab F u v a b J) huv hua hva hub hvb
  refine ⟨p, hp, hpe, fun x hx => ?_, fun e he hab' => ?_⟩
  · have hx' := hps x hx
    rw [mem_union, mA, mB] at hx'
    refine ⟨?_, ?_, ?_⟩
    · rcases hx' with (rfl | h) | (rfl | h)
      · exact hroots (by simp)
      · exact mem_support_of_mem h (by simp)
      · exact hroots (by simp)
      · exact mem_support_of_mem h (by simp)
    · rintro rfl; rcases hx' with (h | h) | (h | h)
      exacts [hua h, hvu_J h, hub h, hvu_J h]
    · rintro rfl; rcases hx' with (h | h) | (h | h)
      exacts [hva h, hvv_J h, hvb h, hvv_J h]
  · obtain ⟨x, y, rfl, hxy⟩ := hpE e he
    rcases Sym2.eq_iff.1 hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hxy with h | h
      · have := hA.closed _ (mA.2 (Or.inl rfl)) _ h
        rw [mA] at this; rcases this with h' | h'; exacts [hab h'.symm, hvb_J h']
      · have := hB.closed _ (mB.2 (Or.inl rfl)) _ (hB.symm _ _ h)
        rw [mB] at this; rcases this with h' | h'; exacts [hab h', hva_J h']
    · rcases hxy with h | h
      · have := hA.closed _ (mA.2 (Or.inl rfl)) _ (hA.symm _ _ h)
        rw [mA] at this; rcases this with h' | h'; exacts [hab h'.symm, hvb_J h']
      · have := hB.closed _ (mB.2 (Or.inl rfl)) _ h
        rw [mB] at this; rcases this with h' | h'; exacts [hab h', hva_J h']

end S07V25
