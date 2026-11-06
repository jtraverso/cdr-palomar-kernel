/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDR.Forbidden
public import CDR.Cells

/-!
# Good arrays from arrays with placeholder symbols (Colbourn–Dinitz–Rosa, Lemma 2.3)

Following the proof of Lemma 2.3, the array on `(A ∪ B) × (A ∪ B)` is first built with symbols
from `C` and `d = a + b − c` placeholder symbols `X` (`GoodQ`): the cells of `A × B` and `B × A`
hold symbols of `C`, every row and column of `B` contains every symbol of `C` and every
placeholder. Then the block `A × A` is replaced by a latin square on `A`, and the placeholders
(which all lie in `B × B`, `d` per row and column) are replaced by the symbols of `B` using de
Werra's theorem (`deWerra_cells`), each symbol of `B` used exactly `d` times
(`goodArray_of_goodQ`).
-/

@[expose] public section

namespace CDR

open Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/-! ### Cyclic arithmetic on `Fin m` -/

theorem fin_add_left_inj {m : ℕ} (a : Fin m) {x y : Fin m} (h : a + x = a + y) : x = y := by
  cases m with
  | zero => exact a.elim0
  | succ m => exact add_left_cancel h

theorem fin_add_right_inj {m : ℕ} (a : Fin m) {x y : Fin m} (h : x + a = y + a) : x = y := by
  cases m with
  | zero => exact a.elim0
  | succ m => exact add_right_cancel h

theorem fin_exists_add_left {m : ℕ} (a z : Fin m) : ∃ x, a + x = z := by
  cases m with
  | zero => exact a.elim0
  | succ m => exact ⟨z - a, add_sub_cancel a z⟩

theorem fin_exists_add_right {m : ℕ} (a z : Fin m) : ∃ x, x + a = z := by
  cases m with
  | zero => exact a.elim0
  | succ m => exact ⟨z - a, sub_add_cancel z a⟩

/-! ### Class subtypes -/

theorem card_classSubtype (lab : N → Fin 3) (k : Fin 3) :
    Fintype.card {x // lab x = k} = #(cls lab k) := by
  rw [Fintype.card_subtype]
  rfl

/-- An enumeration of a class. -/
noncomputable def classEquiv (lab : N → Fin 3) (k : Fin 3) : {x // lab x = k} ≃ Fin #(cls lab k) :=
  Fintype.equivFinOfCardEq (card_classSubtype lab k)

/-- A latin square on a class, by cyclic addition. -/
noncomputable def classSquare (lab : N → Fin 3) (k : Fin 3) (r g : N) : N :=
  if h : lab r = k ∧ lab g = k then
    ((classEquiv lab k).symm (classEquiv lab k ⟨r, h.1⟩ + classEquiv lab k ⟨g, h.2⟩)).1
  else r

theorem classSquare_lab {lab : N → Fin 3} {k : Fin 3} {r g : N} (hr : lab r = k) (hg : lab g = k) :
    lab (classSquare lab k r g) = k := by
  rw [classSquare, dif_pos ⟨hr, hg⟩]
  exact ((classEquiv lab k).symm _).2

theorem classSquare_row_inj {lab : N → Fin 3} {k : Fin 3} {r g g' : N} (hr : lab r = k)
    (hg : lab g = k) (hg' : lab g' = k) (h : classSquare lab k r g = classSquare lab k r g') :
    g = g' := by
  rw [classSquare, classSquare, dif_pos ⟨hr, hg⟩, dif_pos ⟨hr, hg'⟩] at h
  have := fin_add_left_inj _ ((classEquiv lab k).symm.injective (Subtype.ext h))
  exact congrArg Subtype.val ((classEquiv lab k).injective this)

theorem classSquare_col_inj {lab : N → Fin 3} {k : Fin 3} {r r' g : N} (hr : lab r = k)
    (hr' : lab r' = k) (hg : lab g = k) (h : classSquare lab k r g = classSquare lab k r' g) :
    r = r' := by
  rw [classSquare, classSquare, dif_pos ⟨hr, hg⟩, dif_pos ⟨hr', hg⟩] at h
  have := fin_add_right_inj _ ((classEquiv lab k).symm.injective (Subtype.ext h))
  exact congrArg Subtype.val ((classEquiv lab k).injective this)

theorem classSquare_row_surj {lab : N → Fin 3} {k : Fin 3} {r σ : N} (hr : lab r = k)
    (hσ : lab σ = k) : ∃ g, lab g = k ∧ classSquare lab k r g = σ := by
  obtain ⟨x, hx⟩ := fin_exists_add_left (classEquiv lab k ⟨r, hr⟩) (classEquiv lab k ⟨σ, hσ⟩)
  set g := (classEquiv lab k).symm x
  refine ⟨g.1, g.2, ?_⟩
  rw [classSquare, dif_pos ⟨hr, g.2⟩]
  simp only [g, Subtype.coe_eta, Equiv.apply_symm_apply, hx, Equiv.symm_apply_apply]

theorem classSquare_col_surj {lab : N → Fin 3} {k : Fin 3} {g σ : N} (hg : lab g = k)
    (hσ : lab σ = k) : ∃ r, lab r = k ∧ classSquare lab k r g = σ := by
  obtain ⟨x, hx⟩ := fin_exists_add_right (classEquiv lab k ⟨g, hg⟩) (classEquiv lab k ⟨σ, hσ⟩)
  set r := (classEquiv lab k).symm x
  refine ⟨r.1, r.2, ?_⟩
  rw [classSquare, dif_pos ⟨r.2, hg⟩]
  simp only [r, Subtype.coe_eta, Equiv.apply_symm_apply, hx, Equiv.symm_apply_apply]

/-! ### Arrays with placeholders -/

/-- The array on `(A ∪ B) × (A ∪ B)` with symbols of `C` (`inl`) and `d` placeholders (`inr`). -/
structure GoodQ (lab : N → Fin 3) (d : ℕ) (Q : N → N → N ⊕ Fin d) : Prop where
  rowInj : ∀ r, lab r = 1 → ∀ g g', lab g ≠ 2 → lab g' ≠ 2 → Q r g = Q r g' → g = g'
  rowInjA : ∀ r, lab r = 0 → ∀ g g', lab g = 1 → lab g' = 1 → Q r g = Q r g' → g = g'
  colInj : ∀ g, lab g = 1 → ∀ r r', lab r ≠ 2 → lab r' ≠ 2 → Q r g = Q r' g → r = r'
  colInjA : ∀ g, lab g = 0 → ∀ r r', lab r = 1 → lab r' = 1 → Q r g = Q r' g → r = r'
  ab : ∀ r g, lab r = 0 → lab g = 1 → ∃ σ, lab σ = 2 ∧ Q r g = .inl σ
  ba : ∀ r g, lab r = 1 → lab g = 0 → ∃ σ, lab σ = 2 ∧ Q r g = .inl σ
  bb : ∀ r g σ, lab r = 1 → lab g = 1 → Q r g = .inl σ → lab σ = 2
  bRowC : ∀ r, lab r = 1 → ∀ σ, lab σ = 2 → ∃ g, lab g ≠ 2 ∧ Q r g = .inl σ
  bColC : ∀ g, lab g = 1 → ∀ σ, lab σ = 2 → ∃ r, lab r ≠ 2 ∧ Q r g = .inl σ
  bRowX : ∀ r, lab r = 1 → ∀ x, ∃ g, lab g = 1 ∧ Q r g = .inr x
  bColX : ∀ g, lab g = 1 → ∀ x, ∃ r, lab r = 1 ∧ Q r g = .inr x

/-- The placeholder cells. -/
def PlaceCell (lab : N → Fin 3) {d : ℕ} (Q : N → N → N ⊕ Fin d) (r g : N) : Prop :=
  lab r = 1 ∧ lab g = 1 ∧ ∃ x, Q r g = .inr x

noncomputable instance (lab : N → Fin 3) {d : ℕ} (Q : N → N → N ⊕ Fin d) :
    DecidableRel (PlaceCell lab Q) := Classical.decRel _

theorem GoodQ.inr_lab {lab : N → Fin 3} {d : ℕ} {Q : N → N → N ⊕ Fin d} (hQ : GoodQ lab d Q)
    {r g : N} (hr : lab r ≠ 2) (hg : lab g ≠ 2) (hAA : ¬ (lab r = 0 ∧ lab g = 0)) {x : Fin d}
    (h : Q r g = .inr x) : lab r = 1 ∧ lab g = 1 := by
  rcases fin3_cases (lab r) with hr' | hr' | hr'
  · rcases fin3_cases (lab g) with hg' | hg' | hg'
    · exact absurd ⟨hr', hg'⟩ hAA
    · obtain ⟨σ, -, hσ⟩ := hQ.ab r g hr' hg'
      rw [hσ] at h
      exact absurd h Sum.inl_ne_inr
    · exact absurd hg' hg
  · rcases fin3_cases (lab g) with hg' | hg' | hg'
    · obtain ⟨σ, -, hσ⟩ := hQ.ba r g hr' hg'
      rw [hσ] at h
      exact absurd h Sum.inl_ne_inr
    · exact ⟨hr', hg'⟩
    · exact absurd hg' hg
  · exact absurd hr' hr

theorem GoodQ.inl_lab {lab : N → Fin 3} {d : ℕ} {Q : N → N → N ⊕ Fin d} (hQ : GoodQ lab d Q)
    {r g : N} (hr : lab r ≠ 2) (hg : lab g ≠ 2) (hAA : ¬ (lab r = 0 ∧ lab g = 0)) {σ : N}
    (h : Q r g = .inl σ) : lab σ = 2 := by
  rcases fin3_cases (lab r) with hr' | hr' | hr'
  · rcases fin3_cases (lab g) with hg' | hg' | hg'
    · exact absurd ⟨hr', hg'⟩ hAA
    · obtain ⟨σ', hσ', h'⟩ := hQ.ab r g hr' hg'
      rw [h'] at h
      rwa [← Sum.inl_injective h]
    · exact absurd hg' hg
  · rcases fin3_cases (lab g) with hg' | hg' | hg'
    · obtain ⟨σ', hσ', h'⟩ := hQ.ba r g hr' hg'
      rw [h'] at h
      rwa [← Sum.inl_injective h]
    · exact hQ.bb r g σ hr' hg' h
    · exact absurd hg' hg
  · exact absurd hr' hr

theorem GoodQ.card_row {lab : N → Fin 3} {d : ℕ} {Q : N → N → N ⊕ Fin d} (hQ : GoodQ lab d Q)
    (r : N) : #(univ.filter fun g => PlaceCell lab Q r g) = if lab r = 1 then d else 0 := by
  split_ifs with hr
  · choose col hcol using hQ.bRowX r hr
    suffices h : #(univ : Finset (Fin d)) = #(univ.filter fun g => PlaceCell lab Q r g) by
      rw [← h, card_univ, Fintype.card_fin]
    refine card_bij (fun x _ => col x) (fun x _ => ?_) (fun x _ y _ h => ?_) ?_
    · simp only [mem_filter, mem_univ, true_and]
      exact ⟨hr, (hcol x).1, x, (hcol x).2⟩
    · have := (hcol x).2
      rw [h, (hcol y).2] at this
      exact (Sum.inr_injective this).symm
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg
      obtain ⟨-, hg1, x, hx⟩ := hg
      refine ⟨x, mem_univ _, hQ.rowInj r hr _ _ (by rw [(hcol x).1]; decide)
        (by rw [hg1]; decide) (by rw [(hcol x).2, hx])⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    exact fun g _ h => hr h.1

theorem GoodQ.card_col {lab : N → Fin 3} {d : ℕ} {Q : N → N → N ⊕ Fin d} (hQ : GoodQ lab d Q)
    (g : N) : #(univ.filter fun r => PlaceCell lab Q r g) = if lab g = 1 then d else 0 := by
  split_ifs with hg
  · choose row hrow using hQ.bColX g hg
    suffices h : #(univ : Finset (Fin d)) = #(univ.filter fun r => PlaceCell lab Q r g) by
      rw [← h, card_univ, Fintype.card_fin]
    refine card_bij (fun x _ => row x) (fun x _ => ?_) (fun x _ y _ h => ?_) ?_
    · simp only [mem_filter, mem_univ, true_and]
      exact ⟨(hrow x).1, hg, x, (hrow x).2⟩
    · have := (hrow x).2
      rw [h, (hrow y).2] at this
      exact (Sum.inr_injective this).symm
    · intro r hr
      simp only [mem_filter, mem_univ, true_and] at hr
      obtain ⟨hr1, -, x, hx⟩ := hr
      refine ⟨x, mem_univ _, hQ.colInj g hg _ _ (by rw [(hrow x).1]; decide)
        (by rw [hr1]; decide) (by rw [(hrow x).2, hx])⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    exact fun r _ h => hg h.2.1

/-- The placeholders receive the symbols of `B`, each `d` times, injectively along rows and
columns (de Werra). -/
theorem GoodQ.exists_placeColouring {lab : N → Fin 3} {d : ℕ} {Q : N → N → N ⊕ Fin d}
    (hQ : GoodQ lab d Q) (hd : d ≤ #(cls lab 1)) :
    ∃ β : N → N → N, (∀ r g, PlaceCell lab Q r g → lab (β r g) = 1) ∧
      (∀ r g g', PlaceCell lab Q r g → PlaceCell lab Q r g' → β r g = β r g' → g = g') ∧
      (∀ g r r', PlaceCell lab Q r g → PlaceCell lab Q r' g → β r g = β r' g → r = r') ∧
      ∀ σ, lab σ = 1 →
        #((cells (PlaceCell lab Q)).filter fun p => β p.1 p.2 = σ) = d := by
  rcases Nat.eq_zero_or_pos #(cls lab 1) with hb | hb
  · have hno : ∀ x, lab x ≠ 1 := fun x hx => by
      have : x ∈ cls lab 1 := mem_cls.2 hx
      rw [card_eq_zero.1 hb] at this
      exact absurd this (notMem_empty x)
    exact ⟨fun r _ => r, fun r g h => absurd h.1 (hno r), fun r g _ h => absurd h.1 (hno r),
      fun g r _ h => absurd h.1 (hno r), fun σ hσ => absurd hσ (hno σ)⟩
  · have hrow : ∀ r, #(univ.filter fun g => PlaceCell lab Q r g) ≤ #(cls lab 1) := by
      intro r
      rw [hQ.card_row]
      split_ifs <;> omega
    have hcol : ∀ g, #(univ.filter fun r => PlaceCell lab Q r g) ≤ #(cls lab 1) := by
      intro g
      rw [hQ.card_col]
      split_ifs <;> omega
    have hcard : #(cells (PlaceCell lab Q)) = #(cls lab 1) * d := by
      rw [← sum_rows_eq_card_cells]
      simp only [hQ.card_row, sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul]
      rfl
    obtain ⟨f, hfr, hfc, hfn⟩ := deWerra_cells hb hrow hcol hcard
    let e := classEquiv lab 1
    refine ⟨fun r g => (e.symm (f r g)).1, fun r g _ => (e.symm (f r g)).2, ?_, ?_, ?_⟩
    · intro r g g' h h' hβ
      exact hfr r g g' h h' (e.symm.injective (Subtype.ext hβ))
    · intro g r r' h h' hβ
      exact hfc g r r' h h' (e.symm.injective (Subtype.ext hβ))
    · intro σ hσ
      refine Eq.trans ?_ (hfn (e ⟨σ, hσ⟩))
      congr 1
      ext p
      simp only [mem_filter, and_congr_right_iff]
      intro _
      constructor
      · intro h
        rw [← Equiv.symm_apply_eq]
        exact Subtype.ext h
      · intro h
        rw [h, Equiv.symm_apply_apply]

/-- The assembled array: a latin square on `A` in `A × A`, the symbols of `C` where `Q` has
them, and the colouring `β` on the placeholders. -/
noncomputable def assemble (lab : N → Fin 3) {d : ℕ} (Q : N → N → N ⊕ Fin d) (β : N → N → N)
    (r g : N) : N :=
  if lab r = 0 ∧ lab g = 0 then classSquare lab 0 r g else Sum.elim id (fun _ => β r g) (Q r g)

theorem assemble_cases {lab : N → Fin 3} {d : ℕ} {Q : N → N → N ⊕ Fin d} (hQ : GoodQ lab d Q)
    (β : N → N → N) {r g : N} (hr : lab r ≠ 2) (hg : lab g ≠ 2) :
    (lab r = 0 ∧ lab g = 0 ∧ assemble lab Q β r g = classSquare lab 0 r g) ∨
    (¬ (lab r = 0 ∧ lab g = 0) ∧ ∃ σ, Q r g = .inl σ ∧ assemble lab Q β r g = σ ∧ lab σ = 2) ∨
    (¬ (lab r = 0 ∧ lab g = 0) ∧ PlaceCell lab Q r g ∧ assemble lab Q β r g = β r g) := by
  by_cases hAA : lab r = 0 ∧ lab g = 0
  · exact Or.inl ⟨hAA.1, hAA.2, by rw [assemble, if_pos hAA]⟩
  · rcases hq : Q r g with σ | x
    · exact Or.inr (Or.inl ⟨hAA, σ, rfl, by rw [assemble, if_neg hAA, hq]; rfl,
        hQ.inl_lab hr hg hAA hq⟩)
    · have := hQ.inr_lab hr hg hAA hq
      exact Or.inr (Or.inr ⟨hAA, ⟨this.1, this.2, x, hq⟩,
        by rw [assemble, if_neg hAA, hq]; rfl⟩)


theorem lab_one_of_not_AA {lab : N → Fin 3} {x y : N} (hx : lab x = 0)
    (hAA : ¬ (lab x = 0 ∧ lab y = 0)) (hy : lab y ≠ 2) : lab y = 1 := by
  rcases fin3_cases (lab y) with h | h | h
  · exact absurd ⟨hx, h⟩ hAA
  · exact h
  · exact absurd h hy

theorem lab_one_of_not_AA' {lab : N → Fin 3} {x y : N} (hy : lab y = 0)
    (hAA : ¬ (lab x = 0 ∧ lab y = 0)) (hx : lab x ≠ 2) : lab x = 1 := by
  rcases fin3_cases (lab x) with h | h | h
  · exact absurd ⟨h, hy⟩ hAA
  · exact h
  · exact absurd h hx

/-- **From placeholders to a good array.** -/
theorem goodArray_of_goodQ {lab : N → Fin 3} {d : ℕ} {Q : N → N → N ⊕ Fin d}
    (hQ : GoodQ lab d Q) (hd : d ≤ #(cls lab 1)) : ∃ P : N → N → N, GoodArray lab P d := by
  obtain ⟨β, hβlab, hβrow, hβcol, hβcnt⟩ := hQ.exists_placeColouring hd
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  refine ⟨assemble lab Q β, ⟨⟨fun r hr g hg g' hg' h => ?_, fun g hg r hr r' hr' h => ?_⟩,
    fun r g hr hg => ?_, fun r hr σ hσ => ?_, fun g hg σ hσ => ?_, fun r g hr hg => ?_,
    fun r g hr hg => ?_, fun r g hr hg => ?_, fun r hr σ hσ => ?_, fun g hg σ hσ => ?_,
    fun σ hσ => ?_⟩⟩
  -- rows
  · rw [mem_clsAB] at hr
    rw [mem_coe, mem_clsAB] at hg hg'
    try simp only at h
    rcases assemble_cases hQ β hr hg with ⟨h0r, h0g, he⟩ | ⟨hAA, σ, hq, he, hσ⟩ | ⟨hAA, hpc, he⟩ <;>
      rcases assemble_cases hQ β hr hg' with
        ⟨h0r', h0g', he'⟩ | ⟨hAA', σ', hq', he', hσ'⟩ | ⟨hAA', hpc', he'⟩ <;>
      rw [he, he'] at h
    · exact classSquare_row_inj h0r h0g h0g' h
    · have := classSquare_lab h0r h0g; rw [h, hσ'] at this; exact absurd this h20
    · have := classSquare_lab h0r h0g; rw [h, hβlab _ _ hpc'] at this; exact absurd this h10
    · have := classSquare_lab h0r' h0g'; rw [← h, hσ] at this; exact absurd this h20
    · subst h
      rcases fin3_cases (lab r) with h0 | h1 | h2
      · exact hQ.rowInjA r h0 g g' (lab_one_of_not_AA h0 hAA hg) (lab_one_of_not_AA h0 hAA' hg')
          (by rw [hq, hq'])
      · exact hQ.rowInj r h1 g g' hg hg' (by rw [hq, hq'])
      · exact absurd h2 hr
    · have := hβlab _ _ hpc'; rw [← h, hσ] at this; exact absurd this h21
    · have := classSquare_lab h0r' h0g'; rw [← h, hβlab _ _ hpc] at this; exact absurd this h10
    · have := hβlab _ _ hpc; rw [h, hσ'] at this; exact absurd this h21
    · exact hβrow r g g' hpc hpc' h
  -- columns
  · rw [mem_clsAB] at hg
    rw [mem_coe, mem_clsAB] at hr hr'
    try simp only at h
    rcases assemble_cases hQ β hr hg with ⟨h0r, h0g, he⟩ | ⟨hAA, σ, hq, he, hσ⟩ | ⟨hAA, hpc, he⟩ <;>
      rcases assemble_cases hQ β hr' hg with
        ⟨h0r', h0g', he'⟩ | ⟨hAA', σ', hq', he', hσ'⟩ | ⟨hAA', hpc', he'⟩ <;>
      rw [he, he'] at h
    · exact classSquare_col_inj h0r h0r' h0g h
    · have := classSquare_lab h0r h0g; rw [h, hσ'] at this; exact absurd this h20
    · have := classSquare_lab h0r h0g; rw [h, hβlab _ _ hpc'] at this; exact absurd this h10
    · have := classSquare_lab h0r' h0g'; rw [← h, hσ] at this; exact absurd this h20
    · subst h
      rcases fin3_cases (lab g) with h0 | h1 | h2
      · exact hQ.colInjA g h0 r r' (lab_one_of_not_AA' h0 hAA hr)
          (lab_one_of_not_AA' h0 hAA' hr') (by rw [hq, hq'])
      · exact hQ.colInj g h1 r r' hr hr' (by rw [hq, hq'])
      · exact absurd h2 hg
    · have := hβlab _ _ hpc'; rw [← h, hσ] at this; exact absurd this h21
    · have := classSquare_lab h0r' h0g'; rw [← h, hβlab _ _ hpc] at this; exact absurd this h10
    · have := hβlab _ _ hpc; rw [h, hσ'] at this; exact absurd this h21
    · exact hβcol g r r' hpc hpc' h
  -- aa
  · rw [assemble, if_pos ⟨hr, hg⟩]
    exact classSquare_lab hr hg
  -- aaRow
  · obtain ⟨g, hg, h⟩ := classSquare_row_surj hr hσ
    exact ⟨g, hg, by rw [assemble, if_pos ⟨hr, hg⟩, h]⟩
  -- aaCol
  · obtain ⟨r, hr, h⟩ := classSquare_col_surj hg hσ
    exact ⟨r, hr, by rw [assemble, if_pos ⟨hr, hg⟩, h]⟩
  -- ab
  · obtain ⟨σ, hσ, hq⟩ := hQ.ab r g hr hg
    have hAA : ¬ (lab r = 0 ∧ lab g = 0) := fun h => h10 (hg.symm.trans h.2)
    rw [assemble, if_neg hAA, hq]
    exact hσ
  -- ba
  · obtain ⟨σ, hσ, hq⟩ := hQ.ba r g hr hg
    have hAA : ¬ (lab r = 0 ∧ lab g = 0) := fun h => h10 (hr.symm.trans h.1)
    rw [assemble, if_neg hAA, hq]
    exact hσ
  -- bb
  · rcases assemble_cases hQ β (g := g) (by rw [hr]; decide) (by rw [hg]; decide) with
      ⟨h0, -, -⟩ | ⟨-, σ, -, he, hσ⟩ | ⟨-, hpc, he⟩
    · exact absurd (hr.symm.trans h0) h10
    · rw [he, hσ]; exact h20
    · rw [he, hβlab _ _ hpc]; exact h10
  -- bRowC
  · obtain ⟨g, hg, hq⟩ := hQ.bRowC r hr σ hσ
    have hAA : ¬ (lab r = 0 ∧ lab g = 0) := fun h => h10 (hr.symm.trans h.1)
    exact ⟨g, hg, by rw [assemble, if_neg hAA, hq]; rfl⟩
  -- bColC
  · obtain ⟨r, hr, hq⟩ := hQ.bColC g hg σ hσ
    have hAA : ¬ (lab r = 0 ∧ lab g = 0) := fun h => h10 (hg.symm.trans h.2)
    exact ⟨r, hr, by rw [assemble, if_neg hAA, hq]; rfl⟩
  -- bCount
  · refine Eq.trans (Eq.symm ?_) (hβcnt σ hσ)
    refine card_bij (fun p _ => p.1) (fun p hp => ?_) (fun p hp p' hp' h => ?_) ?_
    · rw [mem_filter, mem_cells] at hp
      obtain ⟨hpc, hpβ⟩ := hp
      obtain ⟨hr, hg, x, hq⟩ := hpc
      have hAA : ¬ (lab p.1 = 0 ∧ lab p.2 = 0) := fun h => h10 (hr.symm.trans h.1)
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨hr, p.2, hg, by rw [assemble, if_neg hAA, hq]; exact hpβ⟩
    · rw [mem_filter, mem_cells] at hp hp'
      have hg := hβrow p.1 p.2 p'.2 hp.1 (h ▸ hp'.1) (by rw [hp.2, ← hp'.2, h])
      exact Prod.ext h hg
    · intro r hr
      simp only [mem_filter, mem_univ, true_and] at hr
      obtain ⟨hr, g, hg, he⟩ := hr
      rcases assemble_cases hQ β (g := g) (by rw [hr]; decide) (by rw [hg]; decide) with
        ⟨h0, -, -⟩ | ⟨-, σ', -, he', hσ'⟩ | ⟨-, hpc, he'⟩
      · exact absurd (hr.symm.trans h0) h10
      · rw [he'] at he
        rw [he, hσ] at hσ'
        exact absurd hσ' h21.symm
      · refine ⟨(r, g), ?_, rfl⟩
        rw [mem_filter, mem_cells]
        exact ⟨hpc, by rw [← he', he]⟩

end CDR
