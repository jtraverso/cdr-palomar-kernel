/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.Residual
public import LeanPool.Vizing.EquitableDefinitions

/-!
# Counting in a row system

* `card_present` : a proper colouring uses `deg j` distinct colours at row `j`;
* `card_miss` : `|miss j| = |Cl| - deg j`;
* `mult_add_two_mul_class` : `mult v + 2·|class v| = |Rw|` (rows seeing `v` are the endpoints
  of the matching of colour `v`);
* `equitable_sizes` : arithmetic of equitable class sizes.
-/

@[expose] public section

namespace CDRBicolour.Prefix

open Finset LeanPool.Vizing.ColourClasses LeanPool.Vizing.EquitableDefinitions

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  {G : SimpleGraph Rw} [DecidableRel G.Adj] {χ : Sym2 Rw → Cl}

theorem card_present (hχ : ProperOn G.edgeFinset χ) (j : Rw) :
    (present G χ j).card = G.degree j := by
  rw [present, card_image_of_injOn, SimpleGraph.card_incidenceFinset_eq_degree]
  intro e he f hf hef
  by_contra hne
  have he' := mem_coe.1 he
  have hf' := mem_coe.1 hf
  have hd := hχ e (SimpleGraph.incidenceFinset_subset G j he')
    f (SimpleGraph.incidenceFinset_subset G j hf') hne hef
  exact Finset.disjoint_left.1 hd (Sym2.mem_toFinset.2 (SimpleGraph.mem_incidenceFinset.1 he').2)
    (Sym2.mem_toFinset.2 (SimpleGraph.mem_incidenceFinset.1 hf').2)

theorem card_miss (hχ : ProperOn G.edgeFinset χ) (j : Rw) :
    (miss G χ j).card = Fintype.card Cl - G.degree j := by
  rw [miss, card_sdiff_of_subset (subset_univ _), card_univ, card_present hχ]

/-- Rows where `v` is present: endpoints of the class of `v`. -/
theorem card_rows_present (hχ : ProperOn G.edgeFinset χ) (v : Cl) :
    (univ.filter fun j => v ∈ present G χ j).card =
      2 * (colourClass G.edgeFinset χ v).card := by
  have hset : (univ.filter fun j => v ∈ present G χ j) =
      (colourClass G.edgeFinset χ v).biUnion Sym2.toFinset := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_present, mem_biUnion, mem_colourClass,
      Sym2.mem_toFinset, SimpleGraph.incidenceFinset_eq_filter, mem_filter]
    constructor
    · rintro ⟨e, ⟨he, hj⟩, hc⟩; exact ⟨e, ⟨he, hc⟩, hj⟩
    · rintro ⟨e, ⟨he, hc⟩, hj⟩; exact ⟨e, ⟨he, hj⟩, hc⟩
  rw [hset, card_biUnion (colourClass_pairwiseDisjoint_toFinset hχ v)]
  calc ∑ e ∈ colourClass G.edgeFinset χ v, e.toFinset.card
      = ∑ _e ∈ colourClass G.edgeFinset χ v, 2 := by
        refine sum_congr rfl fun e he => ?_
        exact Sym2.card_toFinset_of_not_isDiag e
          (SimpleGraph.not_isDiag_of_mem_edgeFinset (colourClass_subset _ _ _ he))
    _ = 2 * (colourClass G.edgeFinset χ v).card := by rw [sum_const, smul_eq_mul, mul_comm]

theorem mult_add_two_mul_class (hχ : ProperOn G.edgeFinset χ) (v : Cl) :
    mult G χ v + 2 * (colourClass G.edgeFinset χ v).card = Fintype.card Rw := by
  rw [← card_rows_present hχ v, mult]
  have h := card_filter_add_card_filter_not (s := (univ : Finset Rw))
    (fun j => v ∈ present G χ j)
  rw [card_univ] at h
  have hset : (univ.filter fun j => v ∈ miss G χ j) =
      univ.filter fun j => ¬ v ∈ present G χ j := by
    ext j; simp [miss]
  rw [hset]
  omega

/-- **Equitable sizes.** If sizes differ by at most one and sum to `N·q - r` with
`0 < r ≤ N` (`N` the number of colours), then every size is `q` or `q - 1`, and exactly `r` of
them are `q - 1`. -/
theorem equitable_sizes {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    (heq : ∀ x y, s x ≤ s y + 1) (q r : ℕ) (hr : 0 < r) (hrN : r ≤ Fintype.card ι)
    (hq : 1 ≤ q) (hsum : ∑ x, s x + r = Fintype.card ι * q) :
    (∀ x, s x = q ∨ s x + 1 = q) ∧ (univ.filter fun x => s x + 1 = q).card = r := by
  have hN : 0 < Fintype.card ι := lt_of_lt_of_le hr hrN
  have hne : (univ : Finset ι).Nonempty := univ_nonempty_iff.2 (Fintype.card_pos_iff.1 hN)
  have hall : ∀ x, s x = q ∨ s x + 1 = q := by
    intro x
    by_contra hx
    push_neg at hx
    rcases lt_or_gt_of_ne hx.1 with hlt | hgt
    · -- `s x ≤ q - 2`: all sizes `≤ q - 1`
      have hx2 : s x + 2 ≤ q := by omega
      have hle : ∀ y, s y + 1 ≤ q := fun y => by have := heq y x; omega
      have : ∑ y, (s y + 1) ≤ ∑ _y : ι, q := sum_le_sum fun y _ => hle y
      have hstrict : ∑ y, (s y + 1) < ∑ _y : ι, q :=
        sum_lt_sum (fun y _ => hle y) ⟨x, mem_univ _, by omega⟩
      rw [sum_add_distrib, sum_const, sum_const, card_univ, smul_eq_mul, smul_eq_mul,
        mul_one] at hstrict
      omega
    · -- `s x ≥ q + 1`: all sizes `≥ q`
      have hge : ∀ y, q ≤ s y := fun y => by have := heq x y; omega
      have hstrict : ∑ _y : ι, q < ∑ y, s y :=
        sum_lt_sum (fun y _ => hge y) ⟨x, mem_univ _, hgt⟩
      rw [sum_const, card_univ, smul_eq_mul] at hstrict
      omega
  refine ⟨hall, ?_⟩
  -- `∑ (q - s x) = r`, and each term is `0` or `1`
  have hterm : ∀ x, s x + (if s x + 1 = q then 1 else 0) = q := by
    intro x
    rcases hall x with h | h
    · have : ¬ s x + 1 = q := by omega
      simp [this, h]
    · simp [h]
  have hsplit : ∑ x, s x + (univ.filter fun x => s x + 1 = q).card = Fintype.card ι * q := by
    have h1 : ∑ x, (s x + (if s x + 1 = q then 1 else 0)) = ∑ _x : ι, q :=
      sum_congr rfl fun x _ => hterm x
    rw [sum_add_distrib, sum_boole, sum_const, card_univ, smul_eq_mul] at h1
    simpa [mul_comm] using h1
  omega

end CDRBicolour.Prefix
