/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# V25 — alternating paths between two perfect matchings

Two perfect matchings `Ra` on `Xa` and `Rb` on `Xb` (given as symmetric, functional relations
whose pairs are edges of `K`) with `Xa ∖ Xb = {a}` and `Xb ∖ Xa = {b}` contain an alternating
**path** from `a` to `b` of **even** length, all of whose vertices lie in `Xa ∪ Xb`.

This is the combinatorial core of the hinge argument: the triangles through the root `v`
of the two decompositions of `J ∪ {ua, va}` and `J ∪ {ub, vb}` are two such matchings of the
link `L_v`.
-/

namespace S07V25

open Finset

variable {β : Type*} [DecidableEq β]

/-- perfect matching data on `X` for the relation `R` -/
structure PMatch (K : SimpleGraph β) (R : β → β → Prop) (X : Finset β) : Prop where
  symm : ∀ x y, R x y → R y x
  func : ∀ x y y', R x y → R x y' → y = y'
  adj : ∀ x y, R x y → K.Adj x y
  cover : ∀ x ∈ X, ∃ y, R x y
  closed : ∀ x ∈ X, ∀ y, R x y → y ∈ X

lemma PMatch.erase2 {K : SimpleGraph β} {R : β → β → Prop} {X : Finset β} (h : PMatch K R X)
    {p q : β} (hpq : R p q) : PMatch K R ((X.erase p).erase q) := by
  refine ⟨h.symm, h.func, h.adj, fun x hx => h.cover x (mem_of_mem_erase (mem_of_mem_erase hx)),
    fun x hx y hxy => ?_⟩
  simp only [mem_erase] at hx ⊢
  obtain ⟨hxq, hxp, hxX⟩ := hx
  refine ⟨fun hyq => ?_, fun hyp => ?_, h.closed x hxX y hxy⟩
  · subst hyq
    exact hxp (h.func y x p (h.symm _ _ hxy) (h.symm _ _ hpq))
  · subst hyp
    exact hxq (h.func y x q (h.symm _ _ hxy) hpq)

/-- **alternating path** between the two exposed vertices -/
theorem alt_path (K : SimpleGraph β) (Ra Rb : β → β → Prop) :
    ∀ (m : ℕ) (Xa Xb : Finset β) (a b : β), Xa.card ≤ m → PMatch K Ra Xa → PMatch K Rb Xb →
      a ∈ Xa → a ∉ Xb → b ∈ Xb → b ∉ Xa → (∀ z ∈ Xa, z ∉ Xb → z = a) →
      (∀ z ∈ Xb, z ∉ Xa → z = b) →
      ∃ p : K.Walk a b, p.IsPath ∧ Even p.length ∧ (∀ x ∈ p.support, x ∈ Xa ∪ Xb) ∧
        ∀ e ∈ p.edges, ∃ x y, e = s(x, y) ∧ (Ra x y ∨ Rb x y) := by
  intro m
  induction m with
  | zero =>
    intro Xa Xb a b hc _ _ ha
    have := Finset.card_pos.2 ⟨a, ha⟩; omega
  | succ m ih =>
    intro Xa Xb a b hc hA hB haA haB hbB hbA hAB hBA
    obtain ⟨x1, h1⟩ := hA.cover a haA
    have hx1A : x1 ∈ Xa := hA.closed a haA x1 h1
    have hax1 : a ≠ x1 := (hA.adj _ _ h1).ne
    have hx1B : x1 ∈ Xb := by
      by_contra hx; exact hax1 (hAB x1 hx1A hx).symm
    obtain ⟨x2, h2⟩ := hB.cover x1 hx1B
    have hx2B : x2 ∈ Xb := hB.closed x1 hx1B x2 h2
    have hx12 : x1 ≠ x2 := (hB.adj _ _ h2).ne
    have hbx1 : b ≠ x1 := fun h => hbA (h ▸ hx1A)
    have hab : a ≠ b := fun h => haB (h ▸ hbB)
    by_cases hx2b : x2 = b
    · subst hx2b
      refine ⟨.cons (hA.adj _ _ h1) (.cons (hB.adj _ _ h2) .nil), ?_, ⟨1, rfl⟩, ?_, ?_⟩
      · simp only [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.isPath_iff_eq_nil,
          SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false, not_or]
        exact ⟨⟨trivial, hbx1.symm⟩, hax1, hab⟩
      · intro x hx
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact mem_union_left _ haA
        · exact mem_union_left _ hx1A
        · exact mem_union_right _ hbB
      · intro e he
        simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
          List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact ⟨_, _, rfl, Or.inl h1⟩
        · exact ⟨_, _, rfl, Or.inr h2⟩
    · have hx2A : x2 ∈ Xa := by
        by_contra hx; exact hx2b (hBA x2 hx2B hx)
      have hx2a : x2 ≠ a := fun h => haB (h ▸ hx2B)
      set Xa' := (Xa.erase a).erase x1
      set Xb' := (Xb.erase x1).erase x2
      have hA' : PMatch K Ra Xa' := hA.erase2 h1
      have hB' : PMatch K Rb Xb' := hB.erase2 h2
      have hc' : Xa'.card ≤ m := by
        have h1' : Xa'.card < Xa.card :=
          lt_of_le_of_lt (card_le_card (erase_subset _ _)) (card_erase_lt_of_mem haA)
        omega
      obtain ⟨q, hq, hqe, hqs, hqE⟩ := ih Xa' Xb' x2 b hc' hA' hB'
        (by simp [Xa', hx2A, hx2a, hx12.symm])
        (by simp [Xb'])
        (by simp [Xb', hbB, hbx1, Ne.symm hx2b])
        (by simp [Xa', hbA])
        (by
          intro z hz hzB
          simp only [Xa', Xb', mem_erase] at hz hzB
          by_contra hne
          have : z ∈ Xb := by
            by_contra hzX; exact hz.2.1 (hAB z hz.2.2 hzX)
          exact hzB ⟨hne, hz.1, this⟩)
        (by
          intro z hz hzA
          simp only [Xa', Xb', mem_erase] at hz hzA
          by_contra hne
          have : z ∈ Xa := by
            by_contra hzX; exact hne (hBA z hz.2.2 hzX)
          exact hzA ⟨hz.2.1, fun h => haB (h ▸ hz.2.2), this⟩)
      have ha_q : a ∉ q.support := by
        intro h; have := hqs a h
        simp [Xa', Xb', haB] at this
      have hx1_q : x1 ∉ q.support := by
        intro h; have := hqs x1 h
        simp [Xa', Xb'] at this
      refine ⟨.cons (hA.adj _ _ h1) (.cons (hB.adj _ _ h2) q), ?_, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.cons_isPath_iff]
        refine ⟨⟨hq, hx1_q⟩, ?_⟩
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
        exact ⟨hax1, ha_q⟩
      · simp only [SimpleGraph.Walk.length_cons]
        obtain ⟨r, hr⟩ := hqe; exact ⟨r + 1, by omega⟩
      · intro x hx
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact mem_union_left _ haA
        · exact mem_union_left _ hx1A
        · have := hqs x hx
          simp only [Xa', Xb', mem_union, mem_erase] at this
          rcases this with h | h
          · exact mem_union_left _ h.2.2
          · exact mem_union_right _ h.2.2
      · intro e he
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
        rcases he with rfl | rfl | he
        · exact ⟨_, _, rfl, Or.inl h1⟩
        · exact ⟨_, _, rfl, Or.inr h2⟩
        · exact hqE e he

end S07V25
