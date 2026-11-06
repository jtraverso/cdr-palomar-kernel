/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Latin.Forbidden
public import Mathlib.Tactic.Ring

/-!
# CDR Lemma 2.3: an `(a,b,c)`-forbidden Latin square exists iff `max ≤ n/2`

`forbidden_core` (with `C` the largest class) assembles the prefix `P` of CDR's proof and calls
`forbidden_of_prefix`; `forbidden_latin` rotates the classes (the forbidden condition
`cl r + cl g + cl s ≠ 2` is invariant under `cl ↦ cl + k`).
-/

@[expose] public section

namespace CDRBicolour.Latin

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem csz_sub (cl : α → Fin 3) (i : Fin 3) :
    (univ.filter fun y : {y : α // cl y ≠ 2} => cl y.1 = i).card =
      if i = 2 then 0 else csz cl i := by
  classical
  split_ifs with hi
  · subst hi; rw [card_eq_zero]; ext y; simp [y.2]
  · rw [csz, ← card_map (Function.Embedding.subtype _)]
    congr 1; ext y
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hy; exact ⟨⟨y, by rw [hy]; exact hi⟩, hy, rfl⟩

theorem card_ne_two (cl : α → Fin 3) :
    Fintype.card {y : α // cl y ≠ 2} = csz cl 0 + csz cl 1 := by
  classical
  rw [Fintype.card_subtype]
  have h := card_filter_add_card_filter_not (s := univ.filter fun y : α => cl y ≠ 2)
    (fun y => cl y = 0)
  rw [filter_filter, filter_filter] at h
  rw [← h, csz, csz]
  congr 2
  · ext y; simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by rw [h]; decide, h⟩
  · ext y; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; revert h1 h2; generalize cl y = i; fin_cases i <;> simp
    · intro h; exact ⟨by rw [h]; decide, by rw [h]; decide⟩

theorem fin3_ne_two {i : Fin 3} (h : i ≠ 2) : i = 0 ∨ i = 1 := by
  revert h; fin_cases i <;> simp

/-- **Lemma 2.3, with `C` the largest class.** -/
theorem forbidden_core (cl : α → Fin 3) (ha : csz cl 0 ≤ csz cl 2) (hb : csz cl 1 ≤ csz cl 2)
    (hab : csz cl 2 ≤ csz cl 0 + csz cl 1) : ∃ L, IsForbidden cl L := by
  classical
  obtain ⟨a, ha'⟩ : ∃ a, csz cl 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb'⟩ : ∃ b, csz cl 1 = b := ⟨_, rfl⟩
  obtain ⟨c, hc'⟩ : ∃ c, csz cl 2 = c := ⟨_, rfl⟩
  simp only [ha', hb', hc'] at ha hb hab
  set x := a + b - c with hx
  let ρ := {y : α // cl y ≠ 2}
  let β := {y : α // cl y = 2} ⊕ Fin x
  have hρ : Fintype.card ρ = a + b := by rw [card_ne_two, ha', hb']
  have hβ : Fintype.card β = Fintype.card ρ := by
    rw [hρ, Fintype.card_sum, Fintype.card_fin, Fintype.card_subtype]
    show csz cl 2 + x = a + b
    rw [hc']; omega
  have hcl : ∀ y : ρ, cl y.1 = 0 ∨ cl y.1 = 1 := fun y => fin3_ne_two y.2
  -- the square `R`
  have hA0 := csz_sub cl 0
  have hB1 := csz_sub cl 1
  simp only [if_neg (by decide : (0 : Fin 3) ≠ 2), if_neg (by decide : (1 : Fin 3) ≠ 2),
    ha', hb'] at hA0 hB1
  let D : Finset ρ := if a ≤ b then univ.filter fun y => cl y.1 = 0
    else univ.filter fun y => cl y.1 = 1
  have hDc : D.card = min a b := by
    simp only [D]; split_ifs with h
    · rw [hA0]; omega
    · rw [hB1]; omega
  have hDmem : ∀ y : ρ, y ∈ D ↔ cl y.1 = if a ≤ b then 0 else 1 := by
    intro y; simp only [D]; split_ifs <;> simp
  obtain ⟨R, hR, hoffX⟩ := exists_offdiag hβ D (by rw [hDc, hρ]; omega)
    (univ.image Sum.inr) (by rw [card_image_of_injective _ Sum.inr_injective, card_univ,
      Fintype.card_fin, hDc]; omega)
  have hoff : ∀ r g : ρ, cl r.1 ≠ cl g.1 → ∃ σ, R r g = Sum.inl σ := by
    intro r g hne
    have hrg : r ∈ D ↔ g ∉ D := by
      rw [hDmem, hDmem]
      rcases hcl r with h1 | h1 <;> rcases hcl g with h2 | h2 <;> rw [h1, h2] at hne ⊢ <;>
        simp_all <;> split_ifs <;> decide
    have := hoffX r g hrg
    cases hR' : R r g with
    | inl σ => exact ⟨σ, rfl⟩
    | inr t => rw [hR'] at this; exact absurd (mem_image.2 ⟨t, mem_univ _, rfl⟩) this
  have hrowR : ∀ r : ρ, Function.Bijective (R r) := fun r =>
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨fun g g' h => hR.1 r (mem_univ _) (mem_coe.2 (mem_univ _)) (mem_coe.2 (mem_univ _)) h,
        hβ.symm⟩
  have hcolR : ∀ g : ρ, Function.Bijective (fun r => R r g) := fun g =>
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨fun r r' h => hR.2 g (mem_univ _) (mem_coe.2 (mem_univ _)) (mem_coe.2 (mem_univ _)) h,
        hβ.symm⟩
  -- the `X`-cells of `B × B`
  let Bρ : Finset ρ := univ.filter fun y => cl y.1 = 1
  let E : ρ → ρ → Prop := fun r g => cl r.1 = 1 ∧ cl g.1 = 1 ∧ (R r g).isRight = true
  have hE : ∀ r g, E r g → r ∈ Bρ ∧ g ∈ Bρ := fun r g h =>
    ⟨mem_filter.2 ⟨mem_univ _, h.1⟩, mem_filter.2 ⟨mem_univ _, h.2.1⟩⟩
  have hBρ : Bρ.card = b := hB1
  have hrow : ∀ r ∈ Bρ, (Bρ.filter fun g => E r g).card = x := by
    intro r hr
    have hr1 : cl r.1 = 1 := (mem_filter.1 hr).2
    let f : Fin x → ρ := fun t => Classical.choose ((hrowR r).2 (Sum.inr t))
    have hf : ∀ t, R r (f t) = Sum.inr t := fun t => Classical.choose_spec ((hrowR r).2 _)
    have heq : (Bρ.filter fun g => E r g) = univ.image f := by
      ext g
      simp only [mem_filter, mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨-, -, -, hg⟩
        cases hRg : R r g with
        | inl σ => rw [hRg] at hg; simp at hg
        | inr t => exact ⟨t, (hrowR r).1 ((hf t).trans hRg.symm)⟩
      · rintro ⟨t, rfl⟩
        have hc : cl (f t).1 = 1 := by
          by_contra hne
          obtain ⟨σ, hσ⟩ := hoff r (f t) (by rw [hr1]; exact Ne.symm hne)
          rw [hf t] at hσ; cases hσ
        exact ⟨mem_filter.2 ⟨mem_univ _, hc⟩, hr1, hc, by rw [hf t]; rfl⟩
    rw [heq, card_image_of_injective, card_univ, Fintype.card_fin]
    intro t t' h
    have := (hf t).symm.trans ((congrArg (R r) h).trans (hf t'))
    exact Sum.inr_injective this
  have hcol : ∀ g ∈ Bρ, (Bρ.filter fun r => E r g).card = x := by
    intro g hg
    have hg1 : cl g.1 = 1 := (mem_filter.1 hg).2
    let f : Fin x → ρ := fun t => Classical.choose ((hcolR g).2 (Sum.inr t))
    have hf : ∀ t, R (f t) g = Sum.inr t := fun t => Classical.choose_spec ((hcolR g).2 _)
    have heq : (Bρ.filter fun r => E r g) = univ.image f := by
      ext r
      simp only [mem_filter, mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨-, -, -, hr⟩
        cases hRr : R r g with
        | inl σ => rw [hRr] at hr; simp at hr
        | inr t => exact ⟨t, (hcolR g).1 ((hf t).trans hRr.symm)⟩
      · rintro ⟨t, rfl⟩
        have hc : cl (f t).1 = 1 := by
          by_contra hne
          obtain ⟨σ, hσ⟩ := hoff (f t) g (by rw [hg1]; exact hne)
          rw [hf t] at hσ; cases hσ
        exact ⟨mem_filter.2 ⟨mem_univ _, hc⟩, hc, hg1, by rw [hf t]; rfl⟩
    rw [heq, card_image_of_injective, card_univ, Fintype.card_fin]
    intro t t' h
    have := (hf t).symm.trans ((congrArg (fun r => R r g) h).trans (hf t'))
    exact Sum.inr_injective this
  obtain ⟨κ, hκT, hκr, hκc, hκcount⟩ := exists_equalized Bρ E hE x hrow hcol
    (by rw [hBρ]; omega) (univ.filter fun y : α => cl y = 1) (by rw [hBρ]; exact hb')
    (fun r => r.1)
  -- the cyclic square on `A`
  let eA : {y : α // cl y = 0} ≃ Fin a := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype]; exact ha')
  let P : α → α → α := fun r g =>
    if h : cl r ≠ 2 ∧ cl g ≠ 2 then
      if h0 : cl r = 0 ∧ cl g = 0 then (eA.symm (eA ⟨r, h0.1⟩ + eA ⟨g, h0.2⟩)).1
      else Sum.elim (fun σ => σ.1) (fun _ => κ ⟨r, h.1⟩ ⟨g, h.2⟩) (R ⟨r, h.1⟩ ⟨g, h.2⟩)
    else r
  -- classification of the cells of `(A ∪ B)²`
  have hcell : ∀ r g (hr : cl r ≠ 2) (hg : cl g ≠ 2),
      (∃ h0 : cl r = 0 ∧ cl g = 0, P r g = (eA.symm (eA ⟨r, h0.1⟩ + eA ⟨g, h0.2⟩)).1) ∨
      (¬ (cl r = 0 ∧ cl g = 0) ∧ ∃ σ, R ⟨r, hr⟩ ⟨g, hg⟩ = Sum.inl σ ∧ P r g = σ.1) ∨
      (E ⟨r, hr⟩ ⟨g, hg⟩ ∧ P r g = κ ⟨r, hr⟩ ⟨g, hg⟩) := by
    intro r g hr hg
    by_cases h0 : cl r = 0 ∧ cl g = 0
    · exact Or.inl ⟨h0, by simp only [P, dif_pos (show cl r ≠ 2 ∧ cl g ≠ 2 from ⟨hr, hg⟩),
        dif_pos h0]⟩
    · right
      cases hRrg : R ⟨r, hr⟩ ⟨g, hg⟩ with
      | inl σ =>
        refine Or.inl ⟨h0, σ, rfl, ?_⟩
        simp only [P, dif_pos (show cl r ≠ 2 ∧ cl g ≠ 2 from ⟨hr, hg⟩), dif_neg h0, hRrg,
          Sum.elim_inl]
      | inr t =>
        refine Or.inr ⟨?_, ?_⟩
        · have hr1 : cl r = 1 := by
            rcases fin3_ne_two hr with h | h
            · rcases fin3_ne_two hg with h' | h'
              · exact absurd ⟨h, h'⟩ h0
              · obtain ⟨σ, hσ⟩ := hoff ⟨r, hr⟩ ⟨g, hg⟩ (by simp only; rw [h, h']; decide)
                rw [hRrg] at hσ; cases hσ
            · exact h
          have hg1 : cl g = 1 := by
            rcases fin3_ne_two hg with h' | h'
            · obtain ⟨σ, hσ⟩ := hoff ⟨r, hr⟩ ⟨g, hg⟩ (by simp only; rw [hr1, h']; decide)
              rw [hRrg] at hσ; cases hσ
            · exact h'
          exact ⟨hr1, hg1, by rw [hRrg]; rfl⟩
        · simp only [P, dif_pos (show cl r ≠ 2 ∧ cl g ≠ 2 from ⟨hr, hg⟩), dif_neg h0, hRrg,
            Sum.elim_inr]
  have hκcl : ∀ r g, E r g → cl (κ r g) = 1 := fun r g h => (mem_filter.1 (hκT r g h)).2
  have hAcl : ∀ (u v : {y : α // cl y = 0}), cl (eA.symm (eA u + eA v)).1 = 0 :=
    fun u v => (eA.symm _).2
  have hne2 : ∀ {y : α}, cl y = 0 ∨ cl y = 1 → cl y ≠ 2 := by
    intro y h; rcases h with h | h <;> rw [h] <;> decide
  refine forbidden_of_prefix cl P (by rw [ha', hb', hc']; exact hab)
    (by rw [ha', hc']; exact ha) (by rw [hb', hc']; exact hb) ⟨?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_
  · -- rows
    intro r hr g hg g' hg' h
    have hr2 : cl r ≠ 2 := (mem_filter.1 hr).2
    have hg2 : cl g ≠ 2 := (mem_filter.1 (mem_coe.1 hg)).2
    have hg2' : cl g' ≠ 2 := (mem_filter.1 (mem_coe.1 hg')).2
    rcases hcell r g hr2 hg2 with ⟨h0, e1⟩ | ⟨h0, σ, hσ, e1⟩ | ⟨hE1, e1⟩ <;>
    rcases hcell r g' hr2 hg2' with ⟨h0', e2⟩ | ⟨h0', σ', hσ', e2⟩ | ⟨hE2, e2⟩ <;>
    rw [e1, e2] at h
    · have := add_left_cancel (eA.symm.injective (Subtype.ext h))
      exact congrArg Subtype.val (eA.injective this)
    · have := σ'.2; rw [← h, hAcl] at this; exact absurd this (by decide)
    · have := hκcl _ _ hE2; rw [← h, hAcl] at this; exact absurd this (by decide)
    · have := σ.2; rw [h, hAcl] at this; exact absurd this (by decide)
    · have hσσ : σ = σ' := Subtype.ext h
      rw [hσσ, ← hσ'] at hσ
      exact congrArg Subtype.val ((hrowR _).1 hσ)
    · have := σ.2; rw [h, hκcl _ _ hE2] at this; exact absurd this (by decide)
    · have := hκcl _ _ hE1; rw [h, hAcl] at this; exact absurd this (by decide)
    · have := σ'.2; rw [← h, hκcl _ _ hE1] at this; exact absurd this (by decide)
    · exact congrArg Subtype.val (hκr _ _ _ hE1 hE2 h)
  · -- columns
    intro g hg r hr r' hr' h
    have hg2 : cl g ≠ 2 := (mem_filter.1 hg).2
    have hr2 : cl r ≠ 2 := (mem_filter.1 (mem_coe.1 hr)).2
    have hr2' : cl r' ≠ 2 := (mem_filter.1 (mem_coe.1 hr')).2
    simp only at h
    rcases hcell r g hr2 hg2 with ⟨h0, e1⟩ | ⟨h0, σ, hσ, e1⟩ | ⟨hE1, e1⟩ <;>
    rcases hcell r' g hr2' hg2 with ⟨h0', e2⟩ | ⟨h0', σ', hσ', e2⟩ | ⟨hE2, e2⟩ <;>
    rw [e1, e2] at h
    · have := add_right_cancel (eA.symm.injective (Subtype.ext h))
      exact congrArg Subtype.val (eA.injective this)
    · have := σ'.2; rw [← h, hAcl] at this; exact absurd this (by decide)
    · have := hκcl _ _ hE2; rw [← h, hAcl] at this; exact absurd this (by decide)
    · have := σ.2; rw [h, hAcl] at this; exact absurd this (by decide)
    · have hσσ : σ = σ' := Subtype.ext h
      rw [hσσ, ← hσ'] at hσ
      exact congrArg Subtype.val ((hcolR _).1 hσ)
    · have := σ.2; rw [h, hκcl _ _ hE2] at this; exact absurd this (by decide)
    · have := hκcl _ _ hE1; rw [h, hAcl] at this; exact absurd this (by decide)
    · have := σ'.2; rw [← h, hκcl _ _ hE1] at this; exact absurd this (by decide)
    · exact congrArg Subtype.val (hκc _ _ _ hE1 hE2 h)
  · -- `A × A`
    intro r g hr hg
    rcases hcell r g (hne2 (Or.inl hr)) (hne2 (Or.inl hg)) with ⟨h0, e⟩ | ⟨h0, -⟩ | ⟨hE1, -⟩
    · rw [e]; exact hAcl _ _
    · exact absurd ⟨hr, hg⟩ h0
    · have := hE1.1; simp only at this; rw [hr] at this; exact absurd this (by decide)
  · -- off-diagonal blocks
    intro r g hr hg hne
    rcases hcell r g hr hg with ⟨h0, -⟩ | ⟨-, σ, -, e⟩ | ⟨hE1, -⟩
    · exact absurd (h0.1.trans h0.2.symm) hne
    · rw [e]; exact σ.2
    · exact absurd (hE1.1.trans hE1.2.1.symm) hne
  · -- `B × B` avoids `A`
    intro r g hr hg
    rcases hcell r g (hne2 (Or.inr hr)) (hne2 (Or.inr hg)) with ⟨h0, -⟩ | ⟨-, σ, -, e⟩ | ⟨hE1, e⟩
    · rw [hr] at h0; exact absurd h0.1 (by decide)
    · rw [e, σ.2]; decide
    · rw [e, hκcl _ _ hE1]; decide
  · -- rows of `B` contain every `C`-symbol
    intro r hr σ hσ
    obtain ⟨g, hg⟩ := (hrowR ⟨r, hne2 (Or.inr hr)⟩).2 (Sum.inl ⟨σ, hσ⟩)
    refine ⟨g.1, g.2, ?_⟩
    rcases hcell r g.1 (hne2 (Or.inr hr)) g.2 with ⟨h0, -⟩ | ⟨-, σ', hσ', e⟩ | ⟨hE1, -⟩
    · rw [hr] at h0; exact absurd h0.1 (by decide)
    · rw [e]
      have : R ⟨r, _⟩ g = Sum.inl σ' := hσ'
      rw [hg] at this
      exact (congrArg Subtype.val (Sum.inl_injective this)).symm
    · have := hE1.2.2
      rw [show (⟨g.1, g.2⟩ : ρ) = g from rfl, hg] at this; simp at this
  · -- columns of `B` contain every `C`-symbol
    intro g hg σ hσ
    obtain ⟨r, hr⟩ := (hcolR ⟨g, hne2 (Or.inr hg)⟩).2 (Sum.inl ⟨σ, hσ⟩)
    refine ⟨r.1, r.2, ?_⟩
    rcases hcell r.1 g r.2 (hne2 (Or.inr hg)) with ⟨h0, -⟩ | ⟨-, σ', hσ', e⟩ | ⟨hE1, -⟩
    · rw [hg] at h0; exact absurd h0.2 (by decide)
    · rw [e]
      have : R r ⟨g, _⟩ = Sum.inl σ' := hσ'
      simp only at hr
      rw [hr] at this
      exact (congrArg Subtype.val (Sum.inl_injective this)).symm
    · have := hE1.2.2
      simp only at hr
      rw [show (⟨r.1, r.2⟩ : ρ) = r from rfl, hr] at this; simp at this
  · -- every `B`-symbol occurs `a + b - c` times in `B × B`
    intro σ hσ
    rw [ha', hb', hc', ← hx]
    have hcount := hκcount σ (mem_filter.2 ⟨mem_univ _, hσ⟩)
    rw [← hcount, ← card_map (Function.Embedding.subtype _)]
    congr 1
    ext r
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coe_subtype, Bρ]
    constructor
    · rintro ⟨hr, g, hg, e⟩
      refine ⟨⟨r, hne2 (Or.inr hr)⟩, ⟨hr, ⟨g, hne2 (Or.inr hg)⟩, ?_⟩, rfl⟩
      rcases hcell r g (hne2 (Or.inr hr)) (hne2 (Or.inr hg)) with
        ⟨h0, -⟩ | ⟨-, σ', -, e'⟩ | ⟨hE1, e'⟩
      · rw [hr] at h0; exact absurd h0.1 (by decide)
      · rw [e'] at e; have := σ'.2; rw [e, hσ] at this; exact absurd this (by decide)
      · exact ⟨hE1, by rw [← e', e]⟩
    · rintro ⟨r', ⟨hr', g, hEg, e⟩, rfl⟩
      refine ⟨hr', g.1, hEg.2.1, ?_⟩
      rcases hcell r'.1 g.1 r'.2 g.2 with ⟨h0, -⟩ | ⟨-, σ', hσ', -⟩ | ⟨-, e'⟩
      · have := hEg.1; rw [h0.1] at this; exact absurd this (by decide)
      · have := hEg.2.2
        rw [show (⟨r'.1, r'.2⟩ : ρ) = r' from rfl, show (⟨g.1, g.2⟩ : ρ) = g from rfl] at hσ'
        rw [hσ'] at this; simp at this
      · rw [e']; exact e

/-- **CDR Lemma 2.3.** If no class exceeds half of the points, a forbidden Latin square exists. -/
theorem forbidden_latin (cl : α → Fin 3) (hmax : ∀ i, 2 * csz cl i ≤ Fintype.card α) :
    ∃ L, IsForbidden cl L := by
  classical
  have h1 := card_ne_two cl
  rw [Fintype.card_subtype] at h1
  have h := card_filter_add_card_filter_not (s := (univ : Finset α)) (fun y => cl y = 2)
  rw [card_univ] at h
  have hn : Fintype.card α = csz cl 0 + csz cl 1 + csz cl 2 := by
    simp only [ne_eq] at h1; simp only [csz] at *; omega
  have hrot : ∀ k : Fin 3, (∃ L, IsForbidden (fun y => cl y + k) L) → ∃ L, IsForbidden cl L := by
    rintro k ⟨L, hL, hf⟩
    refine ⟨L, hL, fun r g hrg => hf r g ?_⟩
    have e : ∀ x y z k : Fin 3, x + k + (y + k) + (z + k) = x + y + z := by decide
    show cl r + k + (cl g + k) + (cl (L r g) + k) = 2
    rw [e, hrg]
  have hsz : ∀ k i : Fin 3, csz (fun y => cl y + k) i = csz cl (i - k) := by
    intro k i; simp only [csz]; congr 1; ext y; simp only [mem_filter, mem_univ, true_and]
    have e : ∀ x k i : Fin 3, x + k = i ↔ x = i - k := by decide
    exact e _ _ _
  have m0 := hmax 0
  have m1 := hmax 1
  have m2 := hmax 2
  have e01 : (0 : Fin 3) - 1 = 2 := by decide
  have e11 : (1 : Fin 3) - 1 = 0 := by decide
  have e21 : (2 : Fin 3) - 1 = 1 := by decide
  have e02 : (0 : Fin 3) - 2 = 1 := by decide
  have e12 : (1 : Fin 3) - 2 = 2 := by decide
  have e22 : (2 : Fin 3) - 2 = 0 := by decide
  by_cases c2 : csz cl 0 ≤ csz cl 2 ∧ csz cl 1 ≤ csz cl 2
  · exact forbidden_core cl c2.1 c2.2 (by omega)
  · by_cases c1 : csz cl 0 ≤ csz cl 1 ∧ csz cl 2 ≤ csz cl 1
    · apply hrot 1
      refine forbidden_core _ ?_ ?_ ?_ <;> simp only [hsz, e01, e11, e21] <;> omega
    · apply hrot 2
      refine forbidden_core _ ?_ ?_ ?_ <;> simp only [hsz, e02, e12, e22] <;> omega

end CDRBicolour.Latin
