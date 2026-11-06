/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.L181.Slots

/-!
# L181: groups and the choice of the flipped set

Groups are the connected components of the slot graph.  Main result, `exists_flip_set`:
given a row `j₀` missing `p` with `p` unpaired in its old pairs, there is a set `Z ∋ j₀` of rows,
closed under `p`/`x` edges and links, such that

* the flip keeps `mult p` and `mult x`, or moves two units from `p` to `x` when
  `mult x < mult p` (the high label moves);
* the flip creates at most one new pair `x r` with `x r` previously unused and `p r` old
  (the root-loss bound of L181).
-/

@[expose] public section

namespace CDRBicolour.L181

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]

section Groups

variable (G : SimpleGraph Rw) [DecidableRel G.Adj] (p x : Cl) (χ : Sym2 Rw → Cl)
  (M : Rw → Finset (Sym2 Cl))

/-- A slot has a neighbour in another row. -/
def HasExt (σ : Rw × Bool) : Prop := ∃ ρ, (slotGraph G p x χ M).Adj σ ρ ∧ ρ.1 ≠ σ.1

/-- The group of the row `j`. -/
abbrev grp (j : Rw) : (slotGraph G p x χ M).ConnectedComponent :=
  (slotGraph G p x χ M).connectedComponentMk (j, true)

/-- Rows whose group lies in `𝒞`. -/
noncomputable def rowsIn (𝒞 : Finset (slotGraph G p x χ M).ConnectedComponent) : Finset Rw := by
  classical exact univ.filter fun j => grp G p x χ M j ∈ 𝒞

/-- Rows of `Z` with a free `p`-port. -/
noncomputable def freeP (Z : Finset Rw) : Finset Rw := by
  classical exact Z.filter fun j => ¬ HasExt G p x χ M (j, true)

/-- Rows of `Z` with a free `x`-port. -/
noncomputable def freeX (Z : Finset Rw) : Finset Rw := by
  classical exact Z.filter fun j => ¬ HasExt G p x χ M (j, false)

variable {G p x χ M}

theorem mem_rowsIn {𝒞 : Finset (slotGraph G p x χ M).ConnectedComponent} {j : Rw} :
    j ∈ rowsIn G p x χ M 𝒞 ↔ grp G p x χ M j ∈ 𝒞 := by
  unfold rowsIn; simp

theorem mem_freeP {Z : Finset Rw} {j : Rw} :
    j ∈ freeP G p x χ M Z ↔ j ∈ Z ∧ ¬ HasExt G p x χ M (j, true) := by
  unfold freeP; simp

theorem mem_freeX {Z : Finset Rw} {j : Rw} :
    j ∈ freeX G p x χ M Z ↔ j ∈ Z ∧ ¬ HasExt G p x χ M (j, false) := by
  unfold freeX; simp

theorem grp_false (j : Rw) :
    (slotGraph G p x χ M).connectedComponentMk (j, false) = grp G p x χ M j :=
  SimpleGraph.ConnectedComponent.eq.2 (slot_adj_internal j false).reachable

theorem grp_eq_of_link {j j' : Rw} (h : IsLink p x M j j') :
    grp G p x χ M j' = grp G p x χ M j := by
  rw [← grp_false]
  exact SimpleGraph.ConnectedComponent.eq.2 (slot_adj_link h).symm.reachable

theorem grp_eq_of_colour {j j' : Rw} (h : G.Adj j j') (hc : χ s(j, j') = p ∨ χ s(j, j') = x) :
    grp G p x χ M j' = grp G p x χ M j := by
  rcases hc with hc | hc
  · exact SimpleGraph.ConnectedComponent.eq.2
      (slot_adj_colour (b := true) h (by simpa [slotCol] using hc)).symm.reachable
  · rw [← grp_false, ← grp_false]
    exact SimpleGraph.ConnectedComponent.eq.2
      (slot_adj_colour (b := false) h (by simpa [slotCol] using hc)).symm.reachable

theorem kempeClosed_rowsIn (𝒞 : Finset (slotGraph G p x χ M).ConnectedComponent) :
    KempeClosed G p x (rowsIn G p x χ M 𝒞) χ := by
  intro j j' h hc hj
  rw [mem_rowsIn] at hj ⊢
  rwa [grp_eq_of_colour h hc]

theorem linkClosed_rowsIn (𝒞 : Finset (slotGraph G p x χ M).ConnectedComponent) :
    LinkClosed p x (rowsIn G p x χ M 𝒞) M := by
  intro j j' z hne hp hx
  rw [mem_rowsIn, mem_rowsIn, grp_eq_of_link ⟨hne, z, hp, hx⟩]

/-- Cardinalities over `rowsIn 𝒞` split over the groups of `𝒞`. -/
theorem card_filter_rowsIn (𝒞 : Finset (slotGraph G p x χ M).ConnectedComponent)
    (P : Rw → Prop) [DecidablePred P] :
    ((rowsIn G p x χ M 𝒞).filter P).card =
      ∑ C ∈ 𝒞, ((rowsIn G p x χ M {C}).filter P).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := grp G p x χ M) (t := 𝒞)]
  · refine sum_congr rfl fun C hC => ?_
    congr 1; ext j
    simp only [mem_filter, mem_rowsIn, mem_singleton]
    constructor
    · rintro ⟨⟨_, hP⟩, h⟩; exact ⟨h, hP⟩
    · rintro ⟨h, hP⟩; exact ⟨⟨h ▸ hC, hP⟩, h⟩
  · intro j hj
    simp only [coe_filter, Set.mem_setOf_eq, mem_rowsIn] at hj
    exact hj.1

section Proper

variable (hχ : ProperOn G.edgeFinset χ) (hM : ∀ j, IsPartialPairing (M j) (miss G χ j))
  (hd : PairDisjoint M)
include hχ hM hd

theorem slot_degree_eq (j : Rw) (b : Bool) :
    (slotGraph G p x χ M).degree (j, b) =
      1 + (((slotGraph G p x χ M).neighborFinset (j, b)).filter fun ρ => ¬ ρ.1 = j).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsplit := card_filter_add_card_filter_not (s := (slotGraph G p x χ M).neighborFinset (j, b))
    (fun ρ => ρ.1 = j)
  have hin : ((slotGraph G p x χ M).neighborFinset (j, b)).filter (fun ρ => ρ.1 = j) =
      {(j, !b)} := by
    ext ⟨j', b'⟩
    simp only [mem_filter, SimpleGraph.mem_neighborFinset, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl⟩
      rcases slot_adj_cases h with ⟨-, hb⟩ | ⟨hne, -⟩
      · exact ⟨rfl, hb⟩
      · exact absurd rfl hne
    · rintro ⟨rfl, rfl⟩; exact ⟨slot_adj_internal _ _, rfl⟩
  rw [hin, card_singleton] at hsplit
  rw [← hsplit]

theorem slot_degree_of_ext {j : Rw} {b : Bool} (h : HasExt G p x χ M (j, b)) :
    (slotGraph G p x χ M).degree (j, b) = 2 := by
  classical
  rw [slot_degree_eq hχ hM hd]
  obtain ⟨ρ, hρ, hρne⟩ := h
  have : (((slotGraph G p x χ M).neighborFinset (j, b)).filter fun ρ => ¬ ρ.1 = j) = {ρ} := by
    ext ρ'
    simp only [mem_filter, SimpleGraph.mem_neighborFinset, mem_singleton]
    constructor
    · rintro ⟨h, hne⟩; exact ext_unique hχ hM hd h hρ hne hρne
    · rintro rfl; exact ⟨hρ, hρne⟩
  rw [this, card_singleton]

theorem slot_degree_of_not_ext {j : Rw} {b : Bool} (h : ¬ HasExt G p x χ M (j, b)) :
    (slotGraph G p x χ M).degree (j, b) = 1 := by
  classical
  rw [slot_degree_eq hχ hM hd]
  have : (((slotGraph G p x χ M).neighborFinset (j, b)).filter fun ρ => ¬ ρ.1 = j) = ∅ := by
    ext ρ'
    simp only [mem_filter, SimpleGraph.mem_neighborFinset, notMem_empty, iff_false, not_and]
    intro h' hne; exact h ⟨ρ', h', hne⟩
  rw [this, card_empty]

theorem slot_degree_le (σ : Rw × Bool) : (slotGraph G p x χ M).degree σ ≤ 2 := by
  obtain ⟨j, b⟩ := σ
  by_cases h : HasExt G p x χ M (j, b)
  · rw [slot_degree_of_ext hχ hM hd h]
  · rw [slot_degree_of_not_ext hχ hM hd h]; omega

theorem not_hasExt_true_iff (j : Rw) :
    ¬ HasExt G p x χ M (j, true) ↔ p ∈ miss G χ j ∧ ¬ ∃ j', IsLink p x M j j' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hp
      obtain ⟨j', hadj, hc⟩ := exists_adj_of_not_miss hχ hp
      exact h ⟨(j', true), slot_adj_colour hadj (by simpa [slotCol] using hc),
        (G.ne_of_adj hadj).symm⟩
    · rintro ⟨j', hl⟩
      exact h ⟨(j', false), slot_adj_link hl, Ne.symm hl.1⟩
  · rintro ⟨hp, hl⟩ ⟨⟨j', b'⟩, hadj, hne⟩
    rcases slot_adj_cases hadj with ⟨h, -⟩ | ⟨-, ⟨-, ha, hc⟩ | ⟨-, -, hl'⟩ | ⟨h, -, -⟩⟩
    · exact hne h.symm
    · exact false_of_adj_miss hχ ha hc (by simpa [slotCol] using hp)
    · exact hl ⟨j', hl'⟩
    · exact absurd h (by simp)

theorem not_hasExt_false_iff (j : Rw) :
    ¬ HasExt G p x χ M (j, false) ↔ x ∈ miss G χ j ∧ ¬ ∃ j', IsLink p x M j' j := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hx
      obtain ⟨j', hadj, hc⟩ := exists_adj_of_not_miss hχ hx
      exact h ⟨(j', false), slot_adj_colour hadj (by simpa [slotCol] using hc),
        (G.ne_of_adj hadj).symm⟩
    · rintro ⟨j', hl⟩
      exact h ⟨(j', true), (slot_adj_link hl).symm, hl.1⟩
  · rintro ⟨hx, hl⟩ ⟨⟨j', b'⟩, hadj, hne⟩
    rcases slot_adj_cases hadj with ⟨h, -⟩ | ⟨-, ⟨-, ha, hc⟩ | ⟨h, -, -⟩ | ⟨-, -, hl'⟩⟩
    · exact hne h.symm
    · exact false_of_adj_miss hχ ha hc (by simpa [slotCol] using hx)
    · exact absurd h (by simp)
    · exact hl ⟨j', hl'⟩

/-- **Balance of a group.** `#(missing p) + #(free x-ports) = #(missing x) + #(free p-ports)`. -/
theorem group_balance (C : (slotGraph G p x χ M).ConnectedComponent) :
    ((rowsIn G p x χ M {C}).filter fun j => p ∈ miss G χ j).card +
        (freeX G p x χ M (rowsIn G p x χ M {C})).card =
      ((rowsIn G p x χ M {C}).filter fun j => x ∈ miss G χ j).card +
        (freeP G p x χ M (rowsIn G p x χ M {C})).card := by
  classical
  set R := rowsIn G p x χ M {C} with hR
  set LP := R.filter fun j => ∃ j', IsLink p x M j j'
  set LX := R.filter fun j => ∃ j', IsLink p x M j' j
  have hP : (R.filter fun j => p ∈ miss G χ j) = freeP G p x χ M R ∪ LP := by
    ext j
    simp only [mem_filter, mem_union, mem_freeP, LP, not_hasExt_true_iff hχ hM hd]
    constructor
    · rintro ⟨hj, hp⟩
      by_cases hl : ∃ j', IsLink p x M j j'
      · exact Or.inr ⟨hj, hl⟩
      · exact Or.inl ⟨hj, hp, hl⟩
    · rintro (⟨hj, hp, -⟩ | ⟨hj, j', -, z, hz, -⟩)
      · exact ⟨hj, hp⟩
      · exact ⟨hj, miss_of_pair hχ hM hz⟩
  have hPd : Disjoint (freeP G p x χ M R) LP := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    rw [mem_freeP, not_hasExt_true_iff hχ hM hd] at h1
    exact h1.2.2 (mem_filter.1 h2).2
  have hX : (R.filter fun j => x ∈ miss G χ j) = freeX G p x χ M R ∪ LX := by
    ext j
    simp only [mem_filter, mem_union, mem_freeX, LX, not_hasExt_false_iff hχ hM hd]
    constructor
    · rintro ⟨hj, hx⟩
      by_cases hl : ∃ j', IsLink p x M j' j
      · exact Or.inr ⟨hj, hl⟩
      · exact Or.inl ⟨hj, hx, hl⟩
    · rintro (⟨hj, hx, -⟩ | ⟨hj, j', -, z, -, hz⟩)
      · exact ⟨hj, hx⟩
      · exact ⟨hj, miss_of_pair hχ hM hz⟩
  have hXd : Disjoint (freeX G p x χ M R) LX := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    rw [mem_freeX, not_hasExt_false_iff hχ hM hd] at h1
    exact h1.2.2 (mem_filter.1 h2).2
  have hL : LP.card = LX.card := by
    refine card_eq_of_rel LP LX (IsLink p x M) ?_ ?_ ?_ ?_
    · intro j hj
      obtain ⟨hjR, j', hl⟩ := mem_filter.1 hj
      refine ⟨j', mem_filter.2 ⟨?_, j, hl⟩, hl⟩
      rw [hR, mem_rowsIn] at hjR ⊢
      rwa [grp_eq_of_link hl]
    · intro j' hj'
      obtain ⟨hjR, j, hl⟩ := mem_filter.1 hj'
      refine ⟨j, mem_filter.2 ⟨?_, j', hl⟩, hl⟩
      rw [hR, mem_rowsIn] at hjR ⊢
      rwa [← grp_eq_of_link hl]
    · intro a b b' h h'; exact link_unique_right hχ hM hd h h'
    · intro a a' b h h'; exact link_unique_left hχ hM hd h h'
  rw [hP, hX, card_union_of_disjoint hPd, card_union_of_disjoint hXd, hL]
  omega

/-- **Free ports of a group**: `0` or `2`. -/
theorem group_free (C : (slotGraph G p x χ M).ConnectedComponent) :
    ∃ d, (freeP G p x χ M (rowsIn G p x χ M {C})).card +
      (freeX G p x χ M (rowsIn G p x χ M {C})).card = 2 * d ∧ d ≤ 1 := by
  classical
  obtain ⟨d, hd2, hd1⟩ := component_deficit (slotGraph G p x χ M) (slot_degree_le hχ hM hd) C
  refine ⟨d, ?_, hd1⟩
  rw [← hd2]
  have hcomp : compFinset (slotGraph G p x χ M) C = (rowsIn G p x χ M {C}) ×ˢ univ := by
    ext ⟨j, b⟩
    rw [mem_compFinset, mem_product, mem_rowsIn, mem_singleton]
    simp only [mem_univ, and_true]
    cases b
    · rw [grp_false]
    · rfl
  rw [hcomp, sum_product]
  simp only [Fintype.sum_bool]
  rw [sum_add_distrib]
  have hdef : ∀ σ : Rw × Bool, 2 - (slotGraph G p x χ M).degree σ =
      if HasExt G p x χ M σ then 0 else 1 := by
    rintro ⟨j, b⟩
    split_ifs with h
    · rw [slot_degree_of_ext hχ hM hd h]
    · rw [slot_degree_of_not_ext hχ hM hd h]
  simp only [hdef]
  rw [freeP, freeX, card_filter, card_filter]
  congr 1
  · refine sum_congr rfl fun j _ => ?_
    split_ifs <;> simp_all
  · refine sum_congr rfl fun j _ => ?_
    split_ifs <;> simp_all

end Proper

end Groups

end CDRBicolour.L181
