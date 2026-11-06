/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.StageA
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Hall's condition for the star partners (L182)

Every row has at least `D` candidates, except at most four exceptional rows which have at least
`D - 2`; every candidate is offered to at most `L` rows.  If `L + 1 ≤ D` and `8 ≤ L`, a system of
distinct representatives exists (double counting + Hall's marriage theorem, Mathlib).
-/

@[expose] public section

namespace CDRBicolour.Prefix

open Finset

theorem hall_stars {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
    (T : Rw → Finset Cl) (X : Finset Rw) (D L : ℕ) (hX : X.card ≤ 4)
    (hrow : ∀ j, D ≤ (T j).card + 2 * (if j ∈ X then 1 else 0))
    (hcol : ∀ v, (univ.filter fun j => v ∈ T j).card ≤ L) (hDL : L + 1 ≤ D) (hL : 8 ≤ L) :
    ∃ f : Rw → Cl, Function.Injective f ∧ ∀ j, f j ∈ T j := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective T).1
  intro s
  by_contra hlt
  push_neg at hlt
  set U := s.biUnion T with hU
  -- double counting of incidences `(j, v)`, `j ∈ s`, `v ∈ T j`
  have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := s) (t := U)
    (r := fun j v => v ∈ T j)
  have habove : ∀ j ∈ s, U.bipartiteAbove (fun j v => v ∈ T j) j = T j := by
    intro j hj
    ext v
    simp only [bipartiteAbove, mem_filter, hU, mem_biUnion]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨⟨j, hj, h⟩, h⟩
  rw [sum_congr rfl fun j hj => by rw [habove j hj]] at hdc
  have hbelow : ∀ v ∈ U, (s.bipartiteBelow (fun j v => v ∈ T j) v).card ≤ L := by
    intro v _
    refine le_trans (card_le_card ?_) (hcol v)
    intro j hj
    simp only [bipartiteBelow, mem_filter] at hj
    simp [hj.2]
  have hupper : ∑ j ∈ s, (T j).card ≤ U.card * L := by
    rw [hdc]
    calc ∑ v ∈ U, (s.bipartiteBelow (fun j v => v ∈ T j) v).card ≤ ∑ _v ∈ U, L :=
          sum_le_sum hbelow
      _ = U.card * L := by rw [sum_const, smul_eq_mul]
  have hlower : s.card * D ≤ ∑ j ∈ s, (T j).card + 8 := by
    have h1 : ∑ _j ∈ s, D ≤ ∑ j ∈ s, ((T j).card + 2 * (if j ∈ X then 1 else 0)) :=
      sum_le_sum fun j _ => hrow j
    rw [sum_const, smul_eq_mul, sum_add_distrib, ← mul_sum, sum_boole] at h1
    have h2 : (s.filter fun j => j ∈ X).card ≤ 4 :=
      le_trans (card_le_card fun j hj => (mem_filter.1 hj).2) hX
    simp only [Nat.cast_id] at h1
    omega
  -- `U.card ≤ s.card - 1`
  have hs : 1 ≤ s.card := by omega
  have hU' : U.card + 1 ≤ s.card := hlt
  have h3 : U.card * L + L ≤ s.card * L := by
    have := Nat.mul_le_mul_right L hU'; rw [add_mul, one_mul] at this; exact this
  have h4 : s.card * L + s.card ≤ s.card * D := by
    have := Nat.mul_le_mul_left s.card hDL; rw [mul_add, mul_one] at this; exact this
  omega

end CDRBicolour.Prefix
