/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# From two-sided small-set expansion to every balanced matching mode (Hall)

Generic, deterministic part of the balanced selector.  Left side `A ⊕ PL` (auxiliaries,
left ports), right side `B ⊕ PR`, `|A| = |B|`, a relation `H` (the bipartite edges).
If every left set `X` with `|X| ≤ M` has at least `|X|` auxiliary neighbours in `B`, every
right set `Y` with `|Y| ≤ M` has at least `|Y|` auxiliary neighbours in `A`, and
`|A| + |PL| + 1 ≤ 2M`, then for all `SL, SR` with `|SL| = |SR|` the bipartite graph induced
on `A ∪ B ∪ SL ∪ SR` has a perfect matching.
-/

namespace SelHall

open Finset

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B PL PR : Type*} [Fintype A] [Fintype B] [Fintype PL] [Fintype PR]
  [DecidableEq A] [DecidableEq B] [DecidableEq PL] [DecidableEq PR]

/-- Adjacency of the bipartite graph of a left-to-right relation. -/
def bAdj (H : A ⊕ PL → B ⊕ PR → Prop) : (A ⊕ PL) ⊕ (B ⊕ PR) → (A ⊕ PL) ⊕ (B ⊕ PR) → Prop
  | Sum.inl x, Sum.inr y => H x y
  | Sum.inr y, Sum.inl x => H x y
  | _, _ => False

/-- The bipartite simple graph of `H`. -/
def bipGraph (H : A ⊕ PL → B ⊕ PR → Prop) : SimpleGraph ((A ⊕ PL) ⊕ (B ⊕ PR)) where
  Adj := bAdj H
  symm := by
    constructor
    intro u v h
    rcases u with x | y <;> rcases v with x' | y' <;> simp_all [bAdj]
  loopless := ⟨by intro u h; rcases u with x | y <;> simp [bAdj] at h⟩

/-- Auxiliary neighbours of a left set. -/
def nbB (H : A ⊕ PL → B ⊕ PR → Prop) [∀ x y, Decidable (H x y)] (X : Finset (A ⊕ PL)) :
    Finset B := univ.filter (fun b => ∃ x ∈ X, H x (Sum.inl b))

/-- Auxiliary neighbours of a right set. -/
def nbA (H : A ⊕ PL → B ⊕ PR → Prop) [∀ x y, Decidable (H x y)] (Y : Finset (B ⊕ PR)) :
    Finset A := univ.filter (fun a => ∃ y ∈ Y, H (Sum.inl a) y)

variable (H : A ⊕ PL → B ⊕ PR → Prop) [∀ x y, Decidable (H x y)]

omit [Fintype PR] in
theorem hall_condition (M : ℕ) (hAB : Fintype.card A = Fintype.card B)
    (hM : Fintype.card A + Fintype.card PL + 1 ≤ 2 * M)
    (hexpL : ∀ X : Finset (A ⊕ PL), X.card ≤ M → X.card ≤ (nbB H X).card)
    (hexpR : ∀ Y : Finset (B ⊕ PR), Y.card ≤ M → Y.card ≤ (nbA H Y).card)
    (SL : Finset PL) (SR : Finset PR) (hS : SL.card = SR.card)
    (X : Finset (A ⊕ PL)) (hX : X ⊆ (univ : Finset A).disjSum SL) :
    X.card ≤ (((univ : Finset B).disjSum SR).filter (fun y => ∃ x ∈ X, H x y)).card := by
  set L' := (univ : Finset A).disjSum SL
  set R' := (univ : Finset B).disjSum SR
  set NR := R'.filter (fun y => ∃ x ∈ X, H x y)
  have hL' : L'.card = Fintype.card A + SL.card := by simp [L', card_disjSum]
  have hR' : R'.card = Fintype.card A + SL.card := by simp [R', card_disjSum, hAB, hS]
  have hXL : X.card ≤ L'.card := card_le_card hX
  have hm : SL.card ≤ Fintype.card PL := card_le_univ SL
  by_cases hsmall : X.card ≤ M
  · refine (hexpL X hsmall).trans ?_
    rw [← card_map (Function.Embedding.inl (β := PR))]
    apply card_le_card
    intro y hy
    simp only [mem_map, nbB, mem_filter, mem_univ, true_and, Function.Embedding.inl_apply] at hy
    obtain ⟨b, ⟨x, hx, hxb⟩, rfl⟩ := hy
    simp only [NR, mem_filter, R', inl_mem_disjSum, mem_univ, true_and]
    exact ⟨x, hx, hxb⟩
  · push_neg at hsmall
    by_contra hlt
    push_neg at hlt
    have hNR : NR ⊆ R' := filter_subset _ _
    set Yc := R' \ NR
    have hYc : Yc.card = R'.card - NR.card := card_sdiff_of_subset hNR
    set need := Fintype.card A + SL.card + 1 - X.card
    obtain ⟨Y, hYsub, hYcard⟩ := exists_subset_card_eq (s := Yc) (n := need) (by omega)
    have hYM : Y.card ≤ M := by omega
    have hexp := hexpR Y hYM
    have hsub : (nbA H Y).map (Function.Embedding.inl (β := PL)) ⊆ L' \ X := by
      intro z hz
      simp only [mem_map, nbA, mem_filter, mem_univ, true_and, Function.Embedding.inl_apply] at hz
      obtain ⟨a, ⟨y, hy, hay⟩, rfl⟩ := hz
      rw [mem_sdiff]
      refine ⟨by simp [L'], fun haX => ?_⟩
      have hyc := hYsub hy
      rw [mem_sdiff] at hyc
      exact hyc.2 (mem_filter.mpr ⟨hyc.1, Sum.inl a, haX, hay⟩)
    have h1 := card_le_card hsub
    rw [card_map, card_sdiff_of_subset hX] at h1
    omega

omit [Fintype PR] in
/-- **Hall step.** Two-sided small-set expansion gives a perfect matching of the bipartite
graph induced on `A ∪ B ∪ SL ∪ SR` for every balanced pair `|SL| = |SR|`. -/
theorem balanced_mode_of_expansion (M : ℕ) (hAB : Fintype.card A = Fintype.card B)
    (hM : Fintype.card A + Fintype.card PL + 1 ≤ 2 * M)
    (hexpL : ∀ X : Finset (A ⊕ PL), X.card ≤ M → X.card ≤ (nbB H X).card)
    (hexpR : ∀ Y : Finset (B ⊕ PR), Y.card ≤ M → Y.card ≤ (nbA H Y).card)
    (SL : Finset PL) (SR : Finset PR) (hS : SL.card = SR.card) :
    ∃ Mt : (bipGraph H).Subgraph,
      Mt.verts = ↑(((univ : Finset A).disjSum SL).map Function.Embedding.inl ∪
        ((univ : Finset B).disjSum SR).map Function.Embedding.inr) ∧ Mt.IsMatching := by
  classical
  set L' := (univ : Finset A).disjSum SL
  set R' := (univ : Finset B).disjSum SR
  let t : L' → Finset (B ⊕ PR) := fun x => R'.filter (fun y => H x.1 y)
  have hHall : ∀ s : Finset L', s.card ≤ (s.biUnion t).card := by
    intro s
    have hX : s.map (Function.Embedding.subtype _) ⊆ L' := by
      intro z hz; obtain ⟨x, _, rfl⟩ := mem_map.mp hz; exact x.2
    have h := hall_condition H M hAB hM hexpL hexpR SL SR hS _ hX
    rw [card_map] at h
    refine h.trans (le_of_eq (congrArg card ?_))
    ext y
    simp only [mem_filter, mem_biUnion, t, mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨hy, x, ⟨x', hx', rfl⟩, hxy⟩; exact ⟨x', hx', hy, hxy⟩
    · rintro ⟨x', hx', hy, hxy⟩; exact ⟨hy, x', ⟨x', hx', rfl⟩, hxy⟩
  obtain ⟨f, hfinj, hft⟩ := (all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  have hfR : ∀ x, f x ∈ R' := fun x => (mem_filter.mp (hft x)).1
  have hfH : ∀ x, H x.1 (f x) := fun x => (mem_filter.mp (hft x)).2
  -- `f` is onto `R'`
  have hL' : L'.card = Fintype.card A + SL.card := by simp [L', card_disjSum]
  have hR' : R'.card = Fintype.card A + SL.card := by simp [R', card_disjSum, hAB, hS]
  have himg : univ.image f = R' := by
    apply eq_of_subset_of_card_le
    · intro y hy; obtain ⟨x, _, rfl⟩ := mem_image.mp hy; exact hfR x
    · rw [card_image_of_injective _ hfinj, card_univ, Fintype.card_coe, hL', hR']
  have hsurj : ∀ y ∈ R', ∃ x, f x = y := by
    intro y hy; rw [← himg] at hy; obtain ⟨x, _, hx⟩ := mem_image.mp hy; exact ⟨x, hx⟩
  let MA : (A ⊕ PL) ⊕ (B ⊕ PR) → (A ⊕ PL) ⊕ (B ⊕ PR) → Prop := fun u v =>
    (∃ x : L', u = Sum.inl x.1 ∧ v = Sum.inr (f x)) ∨
    (∃ x : L', v = Sum.inl x.1 ∧ u = Sum.inr (f x))
  refine ⟨{ verts := ↑(L'.map Function.Embedding.inl ∪ R'.map Function.Embedding.inr)
            Adj := MA
            adj_sub := ?_
            edge_vert := ?_
            symm := ?_ }, rfl, ?_⟩
  · rintro u v (⟨x, rfl, rfl⟩ | ⟨x, rfl, rfl⟩)
    · exact hfH x
    · exact hfH x
  · rintro u v (⟨x, rfl, rfl⟩ | ⟨x, rfl, rfl⟩)
    · simp [x.2]
    · simp [hfR x]
  · constructor
    rintro u v (h | h)
    · exact Or.inr h
    · exact Or.inl h
  · intro v hv
    simp only [coe_union, coe_map, Set.mem_union, Set.mem_image, mem_coe,
      Function.Embedding.inl_apply, Function.Embedding.inr_apply] at hv
    rcases hv with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
    · refine ⟨Sum.inr (f ⟨x, hx⟩), Or.inl ⟨⟨x, hx⟩, rfl, rfl⟩, ?_⟩
      rintro w (⟨x', hx1, rfl⟩ | ⟨x', _, hx2⟩)
      · have : x' = ⟨x, hx⟩ := Subtype.ext (Sum.inl_injective hx1).symm
        rw [this]
      · exact absurd hx2 (by simp)
    · obtain ⟨x, rfl⟩ := hsurj y hy
      refine ⟨Sum.inl x.1, Or.inr ⟨x, rfl, rfl⟩, ?_⟩
      rintro w (⟨x', hx1, _⟩ | ⟨x', rfl, hx2⟩)
      · exact absurd hx1 (by simp)
      · have := hfinj (Sum.inr_injective hx2)
        rw [this]

end SelHall
