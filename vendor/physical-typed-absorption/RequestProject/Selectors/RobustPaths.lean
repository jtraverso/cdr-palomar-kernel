/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Selectors.GreedyEmbedding

@[expose] public section

/-!
# The robust short odd path condition from dense neighbourhoods

* `three_path` : if `a` has `≥ B + 2` neighbours in `C1` and every `x ∈ C1 \ {b}` has
  `≥ B + 2` neighbours in `C2` that are also neighbours of `b`, then for every `Z`,
  `|Z| ≤ B`, `a, b ∉ Z`, there is a path `a x y b` of length 3 avoiding `Z`.
* `robust_par` (non-bipartite PAR case): linear degrees and common neighbourhoods inside an
  active set `A` give `RobustOddPaths H (ParAllowed A) 3 B` (odd routes between ANY two
  distinct active vertices).
* `robust_bal` (bipartite BAL case, sides `X`, `Y`): degrees across and same-side common
  neighbourhoods give `RobustOddPaths H (BalAllowed X Y) 3 B` (odd routes between OPPOSITE
  sides only).
* `bipartite_walk_parity` : if every edge of `H` crosses `X`, a walk has even length iff its
  ends are on the same side; so no odd path joins two same-side vertices (the BAL selector
  must respect sides).

The thresholds are explicit: with `B` the forbidden budget of `SelEmbed.greedy_embedding`,
the counts must be `≥ B + 2`; if they are `≥ α n`, the condition is `B + 2 ≤ α n`.
Connectivity alone is NOT used and would not suffice.
-/

namespace SelEmbed

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- A path `a x y b` of length three avoiding a small forbidden set. -/
theorem three_path (C1 C2 : Finset V) {B : ℕ} {Z : Finset V} (hZ : Z.card ≤ B) {a b : V}
    (hab : a ≠ b) (ha : a ∉ Z) (hb : b ∉ Z)
    (h1 : B + 2 ≤ (C1.filter (H.Adj a)).card)
    (h2 : ∀ x ∈ C1, x ≠ b → B + 2 ≤ (C2.filter (fun y => H.Adj x y ∧ H.Adj y b)).card) :
    ∃ w : H.Walk a b, w.IsPath ∧ Odd w.length ∧ w.length ≤ 3 ∧ ∀ z ∈ w.support, z ∉ Z := by
  obtain ⟨x, hx⟩ : (C1.filter (H.Adj a) \ insert b Z).Nonempty := by
    rw [← card_pos]
    have := le_card_sdiff (insert b Z) (C1.filter (H.Adj a))
    have := card_insert_le b Z
    omega
  rw [mem_sdiff, mem_filter, mem_insert, not_or] at hx
  obtain ⟨⟨hxC, hax⟩, hxb, hxZ⟩ := hx
  obtain ⟨y, hy⟩ : ((C2.filter (fun y => H.Adj x y ∧ H.Adj y b)) \ insert a Z).Nonempty := by
    rw [← card_pos]
    have := le_card_sdiff (insert a Z) (C2.filter (fun y => H.Adj x y ∧ H.Adj y b))
    have := card_insert_le a Z
    have := h2 x hxC hxb
    omega
  rw [mem_sdiff, mem_filter, mem_insert, not_or] at hy
  obtain ⟨⟨-, hxy, hyb⟩, hya, hyZ⟩ := hy
  refine ⟨.cons hax (.cons hxy (.cons hyb .nil)), ?_, ?_, by simp, ?_⟩
  · apply Walk.IsPath.mk'
    have hax' := H.ne_of_adj hax
    have hxy' := H.ne_of_adj hxy
    have hyb' := H.ne_of_adj hyb
    simp only [Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or]
    exact ⟨⟨hax', Ne.symm hya, hab⟩, ⟨hxy', hxb⟩, hyb', not_false⟩
  · simp only [Walk.length_cons, Walk.length_nil]; decide
  · intro z hz
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption

/-- PAR: allowed pairs are distinct active vertices. -/
def ParAllowed (A : Finset V) (a b : V) : Prop := a ∈ A ∧ b ∈ A ∧ a ≠ b

/-- **PAR robust odd paths** from linear degree and common neighbourhoods in `A`. -/
theorem robust_par (A : Finset V) (B : ℕ)
    (hdeg : ∀ a ∈ A, B + 2 ≤ (A.filter (H.Adj a)).card)
    (hcom : ∀ x ∈ A, ∀ b ∈ A, x ≠ b →
      B + 2 ≤ (A.filter (fun y => H.Adj x y ∧ H.Adj y b)).card) :
    RobustOddPaths H (ParAllowed A) 3 B := by
  intro Z hZ a b ⟨ha, hb, hab⟩ haZ hbZ
  exact three_path H A A hZ hab haZ hbZ (hdeg a ha) (fun x hx hxb => hcom x hx b hb hxb)

/-- BAL: allowed pairs are on opposite sides. -/
def BalAllowed (X Y : Finset V) (a b : V) : Prop := (a ∈ X ∧ b ∈ Y) ∨ (a ∈ Y ∧ b ∈ X)

/-- **BAL robust odd paths** from degrees across the sides and same-side common
neighbourhoods. -/
theorem robust_bal (X Y : Finset V) (hXY : Disjoint X Y) (B : ℕ)
    (hdegX : ∀ a ∈ X, B + 2 ≤ (Y.filter (H.Adj a)).card)
    (hdegY : ∀ a ∈ Y, B + 2 ≤ (X.filter (H.Adj a)).card)
    (hcomX : ∀ x ∈ X, ∀ b ∈ X, x ≠ b →
      B + 2 ≤ (Y.filter (fun y => H.Adj x y ∧ H.Adj y b)).card)
    (hcomY : ∀ x ∈ Y, ∀ b ∈ Y, x ≠ b →
      B + 2 ≤ (X.filter (fun y => H.Adj x y ∧ H.Adj y b)).card) :
    RobustOddPaths H (BalAllowed X Y) 3 B := by
  intro Z hZ a b hall haZ hbZ
  rcases hall with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hab : a ≠ b := fun h => disjoint_left.mp hXY ha (h ▸ hb)
    exact three_path H Y X hZ hab haZ hbZ (hdegX a ha) (fun x hx hxb => hcomY x hx b hb hxb)
  · have hab : a ≠ b := fun h => disjoint_left.mp hXY hb (h ▸ ha)
    exact three_path H X Y hZ hab haZ hbZ (hdegY a ha) (fun x hx hxb => hcomX x hx b hb hxb)

omit [DecidableEq V] [DecidableRel H.Adj] in
/-- **Bipartite parity obstruction**: if every edge crosses `X`, a walk is even iff its ends
lie on the same side. -/
theorem bipartite_walk_parity (X : Set V) (hbip : ∀ u w, H.Adj u w → (u ∈ X ↔ w ∉ X))
    {a b : V} (p : H.Walk a b) : ((a ∈ X ↔ b ∈ X) ↔ Even p.length) := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.length_cons, Nat.even_add_one, ← ih]
    have := hbip _ _ h
    tauto

omit [DecidableEq V] [DecidableRel H.Adj] in
/-- No odd walk joins two vertices of the same side of a bipartite host. -/
theorem no_odd_walk_same_side (X : Set V) (hbip : ∀ u w, H.Adj u w → (u ∈ X ↔ w ∉ X))
    {a b : V} (hs : a ∈ X ↔ b ∈ X) (p : H.Walk a b) : ¬ Odd p.length := by
  rw [Nat.not_odd_iff_even, ← bipartite_walk_parity H X hbip p]
  exact hs

end SelEmbed
