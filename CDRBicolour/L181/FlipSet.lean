/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.L181.Groups

/-!
# L181: the flipped set (mandatory group plus, if needed, a compensating group)

`exists_flip_set` is the selection step of the port operator of L181:

* the *mandatory* group contains the current row `j₀`, whose `p`-port is free; it has exactly two
  free ports, so its weight is `0` or `+1` (`#missing p - #missing x ∈ {0, 2}`);
* if the weight is `+1` and `mult x ≥ mult p`, the total weight `(mult p - mult x)/2 ≤ 0`
  forces a group of weight `-1` (two free `x`-ports, no free `p`-port); both are flipped;
* in all cases at most one free `p`-port other than that of `j₀` is flipped, which bounds the
  new `x`-pairs into a protected set by one (root loss).
-/

@[expose] public section

namespace CDRBicolour.L181

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
  {G : SimpleGraph Rw} [DecidableRel G.Adj] {p x : Cl} {χ : Sym2 Rw → Cl}
  {M : Rw → Finset (Sym2 Cl)}

theorem card_freeP_rowsIn (𝒞 : Finset (slotGraph G p x χ M).ConnectedComponent) :
    (freeP G p x χ M (rowsIn G p x χ M 𝒞)).card =
      ∑ C ∈ 𝒞, (freeP G p x χ M (rowsIn G p x χ M {C})).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := grp G p x χ M) (t := 𝒞)]
  · refine sum_congr rfl fun C hC => ?_
    congr 1; ext j
    simp only [mem_filter, mem_freeP, mem_rowsIn, mem_singleton]
    constructor
    · rintro ⟨⟨_, h⟩, rfl⟩; exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩; exact ⟨⟨hC, h⟩, rfl⟩
  · intro j hj
    rw [mem_coe, mem_freeP, mem_rowsIn] at hj
    exact hj.1

section Proper

variable (hχ : ProperOn G.edgeFinset χ) (hM : ∀ j, IsPartialPairing (M j) (miss G χ j))
  (hd : PairDisjoint M)
include hχ hM hd

/-- **Root loss.** New `x`-pairs from flipped `p`-pairs come from free `p`-ports. -/
theorem card_root_le {j₀ : Rw} (hj₀c : p ∉ cover (M j₀)) (Z : Finset Rw) :
    (univ.filter fun r => r ≠ p ∧ r ≠ x ∧ (∀ j, s(x, r) ∉ M j) ∧ ∃ j ∈ Z, s(p, r) ∈ M j).card ≤
      ((freeP G p x χ M Z).erase j₀).card := by
  classical
  let f : Rw → Cl := fun j => if h : ∃ r, s(p, r) ∈ M j then Classical.choose h else p
  have hsub : (univ.filter fun r => r ≠ p ∧ r ≠ x ∧ (∀ j, s(x, r) ∉ M j) ∧
      ∃ j ∈ Z, s(p, r) ∈ M j) ⊆ ((freeP G p x χ M Z).erase j₀).image f := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    obtain ⟨-, -, hclean, j, hjZ, hjr⟩ := hr
    refine mem_image.2 ⟨j, mem_erase.2 ⟨?_, mem_freeP.2 ⟨hjZ, ?_⟩⟩, ?_⟩
    · rintro rfl
      exact hj₀c (mem_cover.2 ⟨_, hjr, Sym2.mem_mk_left _ _⟩)
    · rw [not_hasExt_true_iff hχ hM hd]
      refine ⟨miss_of_pair hχ hM hjr, ?_⟩
      rintro ⟨j', -, z, hz, hxz⟩
      rw [pair_unique hχ hM hd hz hjr] at hxz
      exact hclean j' hxz
    · have hex : ∃ r, s(p, r) ∈ M j := ⟨r, hjr⟩
      simp only [f, dif_pos hex]
      exact pair_unique hχ hM hd (Classical.choose_spec hex) hjr
  exact (card_le_card hsub).trans card_image_le

/-- **Selection of the flipped set.** -/
theorem exists_flip_set {j₀ : Rw} (hj₀ : p ∈ miss G χ j₀) (hj₀c : p ∉ cover (M j₀)) :
    ∃ Z : Finset Rw, KempeClosed G p x Z χ ∧ LinkClosed p x Z M ∧ j₀ ∈ Z ∧
      ((Z.filter fun j => p ∈ miss G χ j).card = (Z.filter fun j => x ∈ miss G χ j).card ∨
        ((Z.filter fun j => p ∈ miss G χ j).card =
            (Z.filter fun j => x ∈ miss G χ j).card + 2 ∧ mult G χ x < mult G χ p)) ∧
      (univ.filter fun r => r ≠ p ∧ r ≠ x ∧ (∀ j, s(x, r) ∉ M j) ∧
        ∃ j ∈ Z, s(p, r) ∈ M j).card ≤ 1 := by
  classical
  set C₀ := grp G p x χ M j₀ with hC₀
  have hj₀R : j₀ ∈ rowsIn G p x χ M {C₀} := mem_rowsIn.2 (mem_singleton_self _)
  have hfree₀ : j₀ ∈ freeP G p x χ M (rowsIn G p x χ M {C₀}) := by
    refine mem_freeP.2 ⟨hj₀R, (not_hasExt_true_iff hχ hM hd j₀).2 ⟨hj₀, ?_⟩⟩
    rintro ⟨j', -, z, hz, -⟩
    exact hj₀c (mem_cover.2 ⟨_, hz, Sym2.mem_mk_left _ _⟩)
  obtain ⟨d₀, hd₀, hd₀le⟩ := group_free hχ hM hd C₀
  have hpos : 1 ≤ (freeP G p x χ M (rowsIn G p x χ M {C₀})).card := card_pos.2 ⟨j₀, hfree₀⟩
  have hbal₀ := group_balance hχ hM hd C₀
  have hroot := fun Z => card_root_le hχ hM hd (x := x) hj₀c Z
  by_cases hcase : (freeP G p x χ M (rowsIn G p x χ M {C₀})).card = 1 ∨ mult G χ x < mult G χ p
  · -- the mandatory group alone
    refine ⟨rowsIn G p x χ M {C₀}, kempeClosed_rowsIn _, linkClosed_rowsIn _, hj₀R, ?_, ?_⟩
    · rcases hcase with h | h
      · left; omega
      · by_cases h1 : (freeP G p x χ M (rowsIn G p x χ M {C₀})).card = 1
        · left; omega
        · right; exact ⟨by omega, h⟩
    · refine (hroot _).trans ?_
      rw [card_erase_of_mem hfree₀]; omega
  · -- the mandatory group has weight `+1` and `mult x ≥ mult p`: add a negative group
    push_neg at hcase
    obtain ⟨hFP, hmult⟩ := hcase
    have hFP2 : (freeP G p x χ M (rowsIn G p x χ M {C₀})).card = 2 := by omega
    have hFX0 : (freeX G p x χ M (rowsIn G p x χ M {C₀})).card = 0 := by omega
    set T := univ.image (grp G p x χ M) with hT
    have hall : rowsIn G p x χ M T = univ := by
      ext j
      simp only [mem_rowsIn, mem_univ, iff_true]
      exact mem_image_of_mem _ (mem_univ j)
    have hmp : mult G χ p = ∑ C ∈ T, ((rowsIn G p x χ M {C}).filter fun j => p ∈ miss G χ j).card := by
      rw [← card_filter_rowsIn, hall]; rfl
    have hmx : mult G χ x = ∑ C ∈ T, ((rowsIn G p x χ M {C}).filter fun j => x ∈ miss G χ j).card := by
      rw [← card_filter_rowsIn, hall]; rfl
    have hC₀T : C₀ ∈ T := mem_image_of_mem _ (mem_univ _)
    have hneg : ∃ C ∈ T, ((rowsIn G p x χ M {C}).filter fun j => p ∈ miss G χ j).card <
        ((rowsIn G p x χ M {C}).filter fun j => x ∈ miss G χ j).card := by
      by_contra hno
      push_neg at hno
      have h1 := add_sum_erase T (fun C => ((rowsIn G p x χ M {C}).filter fun j =>
        p ∈ miss G χ j).card) hC₀T
      have h2 := add_sum_erase T (fun C => ((rowsIn G p x χ M {C}).filter fun j =>
        x ∈ miss G χ j).card) hC₀T
      have h3 : ∑ C ∈ T.erase C₀, ((rowsIn G p x χ M {C}).filter fun j => x ∈ miss G χ j).card ≤
          ∑ C ∈ T.erase C₀, ((rowsIn G p x χ M {C}).filter fun j => p ∈ miss G χ j).card :=
        sum_le_sum fun C hC => hno C (mem_of_mem_erase hC)
      omega
    obtain ⟨C₁, hC₁T, hC₁⟩ := hneg
    obtain ⟨d₁, hd₁, hd₁le⟩ := group_free hχ hM hd C₁
    have hbal₁ := group_balance hχ hM hd C₁
    have hFP1 : (freeP G p x χ M (rowsIn G p x χ M {C₁})).card = 0 := by omega
    have hne : C₀ ≠ C₁ := by
      rintro rfl; omega
    refine ⟨rowsIn G p x χ M {C₀, C₁}, kempeClosed_rowsIn _, linkClosed_rowsIn _,
      mem_rowsIn.2 (mem_insert_self _ _), Or.inl ?_, ?_⟩
    · rw [card_filter_rowsIn, card_filter_rowsIn, sum_pair hne, sum_pair hne]
      omega
    · refine (hroot _).trans ?_
      have hmem : j₀ ∈ freeP G p x χ M (rowsIn G p x χ M {C₀, C₁}) := by
        rw [mem_freeP] at hfree₀ ⊢
        exact ⟨mem_rowsIn.2 (mem_insert_self _ _), hfree₀.2⟩
      rw [card_erase_of_mem hmem, card_freeP_rowsIn, sum_pair hne]
      omega

end Proper

end CDRBicolour.L181
