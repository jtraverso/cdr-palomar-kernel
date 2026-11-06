/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Latin.Ryser

/-!
# Forbidden Latin squares: completion of the prefix (Colbourn–Dinitz–Rosa, Lemma 2.3)

Classes `A = cl⁻¹ 0`, `B = cl⁻¹ 1`, `C = cl⁻¹ 2` of sizes `a, b, c` (`c = max`, `c ≤ a + b`).
A Latin square `L` is *forbidden* if `cl r + cl g + cl (L r g) ≠ 2` in every cell (this is the
nine-line table of CDR Lemma 2.3 with `A, B, C = 0, 1, 2`).

`forbidden_of_prefix`: a partial array `P` on `(A ∪ B) × (A ∪ B)` with
* `A × A` filled by `A`-symbols, `A × B` and `B × A` by `C`-symbols, `B × B` avoiding `A`;
* every row and every column of `B` containing all `C`-symbols;
* every `B`-symbol occurring in exactly `a + b - c` rows of `B` inside `B × B`;

is completed by Ryser's theorem to a forbidden Latin square.  The `C × C` cells avoid `B` by a
counting argument (the `c` rows that place a fixed `B`-symbol outside `A ∪ B` fill all `c`
columns of `C`).
-/

@[expose] public section

namespace CDRBicolour.Latin

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Class sizes. -/
abbrev csz (cl : α → Fin 3) (i : Fin 3) : ℕ := (univ.filter fun x => cl x = i).card

/-- A forbidden Latin square for the class function `cl`. -/
def IsForbidden (cl : α → Fin 3) (L : α → α → α) : Prop :=
  IsLatin L ∧ ∀ r g, cl r + cl g + cl (L r g) ≠ 2

/-- An injective map between finsets of equal size hits everything. -/
theorem surj_of_injOn {s t : Finset α} {f : α → α} (hmap : ∀ x ∈ s, f x ∈ t)
    (hinj : Set.InjOn f s) (hcard : t.card ≤ s.card) : ∀ y ∈ t, ∃ x ∈ s, f x = y := by
  classical
  have hsub : s.image f ⊆ t := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy; exact hmap x hx
  have heq : s.image f = t :=
    eq_of_subset_of_card_le hsub (by rw [card_image_of_injOn hinj]; exact hcard)
  intro y hy
  rw [← heq] at hy
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
  exact ⟨x, hx, rfl⟩

theorem forbidden_of_prefix (cl : α → Fin 3) (P : α → α → α)
    (hab : csz cl 2 ≤ csz cl 0 + csz cl 1) (ha : csz cl 0 ≤ csz cl 2) (hb : csz cl 1 ≤ csz cl 2)
    (hP1 : IsLatinRect (univ.filter fun x => cl x ≠ 2) (univ.filter fun x => cl x ≠ 2) P)
    (hP2 : ∀ r g, cl r = 0 → cl g = 0 → cl (P r g) = 0)
    (hP3 : ∀ r g, cl r ≠ 2 → cl g ≠ 2 → cl r ≠ cl g → cl (P r g) = 2)
    (hP4 : ∀ r g, cl r = 1 → cl g = 1 → cl (P r g) ≠ 0)
    (hP5r : ∀ r, cl r = 1 → ∀ σ, cl σ = 2 → ∃ g, cl g ≠ 2 ∧ P r g = σ)
    (hP5c : ∀ g, cl g = 1 → ∀ σ, cl σ = 2 → ∃ r, cl r ≠ 2 ∧ P r g = σ)
    (hP6 : ∀ σ, cl σ = 1 → ((univ.filter fun r => cl r = 1).filter fun r =>
      ∃ g, cl g = 1 ∧ P r g = σ).card = csz cl 0 + csz cl 1 - csz cl 2) :
    ∃ L, IsForbidden cl L := by
  classical
  obtain ⟨AB, hAB⟩ : ∃ S : Finset α, S = univ.filter fun x => cl x ≠ 2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ S : Finset α, S = univ.filter fun x => cl x = 0 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ S : Finset α, S = univ.filter fun x => cl x = 1 := ⟨_, rfl⟩
  obtain ⟨Cc, hC⟩ : ∃ S : Finset α, S = univ.filter fun x => cl x = 2 := ⟨_, rfl⟩
  rw [← hAB] at hP1
  have hcA : csz cl 0 = A.card := by rw [hA]
  have hcB : csz cl 1 = B.card := by rw [hB]
  have hcC : csz cl 2 = Cc.card := by rw [hC]
  simp only [hcA, hcB, hcC] at hab ha hb
  simp only [hcA, hcB, hcC, ← hB] at hP6
  have hcl3 : ∀ x, cl x = 0 ∨ cl x = 1 ∨ cl x = 2 := by
    intro x; generalize cl x = i; fin_cases i <;> simp
  have hdAB : Disjoint A B := by
    rw [Finset.disjoint_left]; intro x h1 h2
    rw [hA, mem_filter] at h1; rw [hB, mem_filter] at h2; rw [h1.2] at h2; exact absurd h2.2 (by decide)
  have hdABC : Disjoint (A ∪ B) Cc := by
    rw [Finset.disjoint_left]; intro x h1 h2
    rw [hC, mem_filter] at h2
    rcases mem_union.1 h1 with h1 | h1
    · rw [hA, mem_filter] at h1; rw [h1.2] at h2; exact absurd h2.2 (by decide)
    · rw [hB, mem_filter] at h1; rw [h1.2] at h2; exact absurd h2.2 (by decide)
  have hABeq : AB = A ∪ B := by
    ext x
    rw [hAB, hA, hB, mem_union, mem_filter, mem_filter, mem_filter]
    rcases hcl3 x with h | h | h <;> simp [h]
  have hn : Fintype.card α = A.card + B.card + Cc.card := by
    have : (univ : Finset α) = A ∪ B ∪ Cc := by
      ext x
      rw [hA, hB, hC, mem_union, mem_union, mem_filter, mem_filter, mem_filter]
      rcases hcl3 x with h | h | h <;> simp [h]
    rw [← card_univ, this, card_union_of_disjoint hdABC, card_union_of_disjoint hdAB]
  have hABc : AB.card = A.card + B.card := by rw [hABeq, card_union_of_disjoint hdAB]
  -- rows of `A` contain every `A`-symbol inside `A`
  have hrowA : ∀ r, cl r = 0 → ∀ σ, cl σ = 0 → ∃ g, cl g = 0 ∧ P r g = σ := by
    intro r hr σ hσ
    have hrAB : r ∈ AB := by rw [hAB, mem_filter]; exact ⟨mem_univ _, by rw [hr]; decide⟩
    obtain ⟨g, hg, hgσ⟩ := surj_of_injOn (s := A) (t := A) (f := P r)
      (fun g hg => by rw [hA, mem_filter] at hg ⊢; exact ⟨mem_univ _, hP2 r g hr hg.2⟩)
      (fun g hg g' hg' h => hP1.1 r hrAB (by
        rw [mem_coe, hAB, mem_filter]; rw [mem_coe, hA, mem_filter] at hg
        exact ⟨mem_univ _, by rw [hg.2]; decide⟩) (by
        rw [mem_coe, hAB, mem_filter]; rw [mem_coe, hA, mem_filter] at hg'
        exact ⟨mem_univ _, by rw [hg'.2]; decide⟩) h) le_rfl σ
      (by rw [hA, mem_filter]; exact ⟨mem_univ _, hσ⟩)
    rw [hA, mem_filter] at hg
    exact ⟨g, hg.2, hgσ⟩
  have hcolA : ∀ g, cl g = 0 → ∀ σ, cl σ = 0 → ∃ r, cl r = 0 ∧ P r g = σ := by
    intro g hg σ hσ
    have hgAB : g ∈ AB := by rw [hAB, mem_filter]; exact ⟨mem_univ _, by rw [hg]; decide⟩
    obtain ⟨r, hr, hrσ⟩ := surj_of_injOn (s := A) (t := A) (f := fun r => P r g)
      (fun r hr => by rw [hA, mem_filter] at hr ⊢; exact ⟨mem_univ _, hP2 r g hr.2 hg⟩)
      (fun r hr r' hr' h => hP1.2 g hgAB (by
        rw [mem_coe, hAB, mem_filter]; rw [mem_coe, hA, mem_filter] at hr
        exact ⟨mem_univ _, by rw [hr.2]; decide⟩) (by
        rw [mem_coe, hAB, mem_filter]; rw [mem_coe, hA, mem_filter] at hr'
        exact ⟨mem_univ _, by rw [hr'.2]; decide⟩) h) le_rfl σ
      (by rw [hA, mem_filter]; exact ⟨mem_univ _, hσ⟩)
    rw [hA, mem_filter] at hr
    exact ⟨r, hr.2, hrσ⟩
  -- Ryser's condition
  have hcond : RyserCond AB AB P := by
    intro σ
    rw [hABc, hn]
    have hle : ∀ S : Finset α, S ⊆ AB → (∀ r ∈ S, σ ∈ AB.image (P r)) →
        S.card ≤ cnt AB AB P σ := by
      intro S hS h
      exact card_le_card fun r hr => mem_filter.2 ⟨hS hr, h r hr⟩
    have hmem : ∀ r g, cl g ≠ 2 → P r g = σ → σ ∈ AB.image (P r) := fun r g hg h =>
      mem_image.2 ⟨g, by rw [hAB, mem_filter]; exact ⟨mem_univ _, hg⟩, h⟩
    have hAsub : A ⊆ AB := fun x hx => by
      rw [hA, mem_filter] at hx; rw [hAB, mem_filter]; exact ⟨mem_univ _, by rw [hx.2]; decide⟩
    have hBsub : B ⊆ AB := fun x hx => by
      rw [hB, mem_filter] at hx; rw [hAB, mem_filter]; exact ⟨mem_univ _, by rw [hx.2]; decide⟩
    have hσ3 : cl σ = 0 ∨ cl σ = 1 ∨ cl σ = 2 := by
      generalize cl σ = i; fin_cases i <;> simp
    rcases hσ3 with hσ | hσ | hσ
    · have := hle A hAsub fun r hr => by
        rw [hA, mem_filter] at hr
        obtain ⟨g, hg, h⟩ := hrowA r hr.2 σ hσ
        exact hmem r g (by rw [hg]; decide) h
      omega
    · have hsub : (B.filter fun r =>
          ∃ g, cl g = 1 ∧ P r g = σ) ⊆ AB := fun r hr => hBsub (mem_filter.1 hr).1
      have := hle _ hsub fun r hr => by
        obtain ⟨g, hg, h⟩ := (mem_filter.1 hr).2
        exact hmem r g (by rw [hg]; decide) h
      rw [hP6 σ hσ] at this
      omega
    · have := hle B hBsub fun r hr => by
        rw [hB, mem_filter] at hr
        obtain ⟨g, hg, h⟩ := hP5r r hr.2 σ hσ
        exact hmem r g hg h
      omega
  obtain ⟨L, hL, hLP⟩ := ryser rfl hP1 hcond
  have hLP' : ∀ r g, cl r ≠ 2 → cl g ≠ 2 → L r g = P r g := fun r g hr hg =>
    hLP r (by rw [hAB, mem_filter]; exact ⟨mem_univ _, hr⟩) g
      (by rw [hAB, mem_filter]; exact ⟨mem_univ _, hg⟩)
  have hrowinj : ∀ r g g', L r g = L r g' → g = g' := fun r g g' h =>
    hL.1 r (mem_univ _) (mem_coe.2 (mem_univ _)) (mem_coe.2 (mem_univ _)) h
  have hcolinj : ∀ g r r', L r g = L r' g → r = r' := fun g r r' h =>
    hL.2 g (mem_univ _) (mem_coe.2 (mem_univ _)) (mem_coe.2 (mem_univ _)) h
  -- the `C × C` cells avoid `B`
  have hCC : ∀ g, cl g = 2 → ∀ σ, cl σ = 1 → ∃ r, cl r ≠ 2 ∧ L r g = σ := by
    intro g hg σ hσ
    have hrowsurj : ∀ r, ∃ g', L r g' = σ := fun r =>
      ((Fintype.bijective_iff_injective_and_card _).2 ⟨fun g g' h => hrowinj r g g' h, rfl⟩).2 σ
    let pos : α → α := fun r => Classical.choose (hrowsurj r)
    have hpos : ∀ r, L r (pos r) = σ := fun r => Classical.choose_spec (hrowsurj r)
    set D := A ∪ (B.filter fun r =>
      ¬ ∃ g, cl g = 1 ∧ P r g = σ) with hD
    have hDcard : D.card = Cc.card := by
      rw [hD, card_union_of_disjoint]
      · have hsplit := card_filter_add_card_filter_not (s := B)
          (fun r => ∃ g, cl g = 1 ∧ P r g = σ)
        rw [hP6 σ hσ] at hsplit
        omega
      · rw [Finset.disjoint_left]
        intro r hr hr'
        rw [hA, mem_filter] at hr
        rw [mem_filter, hB, mem_filter] at hr'
        rw [hr.2] at hr'; exact absurd hr'.1.2 (by decide)
    obtain ⟨r, hrD, hr⟩ := surj_of_injOn (s := D) (t := Cc) (f := pos) (by
      intro r hr
      rw [hC, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      by_contra hne
      have hpr := hpos r
      rw [hLP' r (pos r) ?_ hne] at hpr
      · rcases mem_union.1 hr with hrA | hrB
        · rw [hA, mem_filter] at hrA
          have hc3 : cl (pos r) = 0 ∨ cl (pos r) = 1 := by
            revert hne; generalize cl (pos r) = i; fin_cases i <;> simp
          rcases hc3 with h0 | h1
          · have := hP2 r (pos r) hrA.2 h0; rw [hpr, hσ] at this; exact absurd this (by decide)
          · have := hP3 r (pos r) (by rw [hrA.2]; decide) hne (by rw [hrA.2, h1]; decide)
            rw [hpr, hσ] at this; exact absurd this (by decide)
        · rw [mem_filter, hB, mem_filter] at hrB
          have hc3 : cl (pos r) = 0 ∨ cl (pos r) = 1 := by
            revert hne; generalize cl (pos r) = i; fin_cases i <;> simp
          rcases hc3 with h0 | h1
          · have := hP3 r (pos r) (by rw [hrB.1.2]; decide) hne (by rw [hrB.1.2, h0]; decide)
            rw [hpr, hσ] at this; exact absurd this (by decide)
          · exact hrB.2 ⟨pos r, h1, hpr⟩
      · rcases mem_union.1 hr with hrA | hrB
        · rw [hA, mem_filter] at hrA; rw [hrA.2]; decide
        · rw [mem_filter, hB, mem_filter] at hrB; rw [hrB.1.2]; decide) (by
      intro r hr r' hr' h
      exact hcolinj (pos r) r r' ((hpos r).trans (h ▸ hpos r').symm)) hDcard.ge g (by rw [hC, mem_filter]; exact ⟨mem_univ _, hg⟩)
    refine ⟨r, ?_, by rw [← hr]; exact hpos r⟩
    rcases mem_union.1 hrD with hrA | hrB
    · rw [hA, mem_filter] at hrA; rw [hrA.2]; decide
    · rw [mem_filter, hB, mem_filter] at hrB; rw [hrB.1.2]; decide
  refine ⟨L, hL, fun r g => ?_⟩
  -- case analysis on the classes of the row and the column
  have hr3 : cl r = 0 ∨ cl r = 1 ∨ cl r = 2 := by generalize cl r = i; fin_cases i <;> simp
  have hg3 : cl g = 0 ∨ cl g = 1 ∨ cl g = 2 := by generalize cl g = i; fin_cases i <;> simp
  rcases hr3 with hr | hr | hr <;> rcases hg3 with hg | hg | hg
  · rw [hLP' r g (by rw [hr]; decide) (by rw [hg]; decide), hr, hg, hP2 r g hr hg]; decide
  · rw [hLP' r g (by rw [hr]; decide) (by rw [hg]; decide), hr, hg,
      hP3 r g (by rw [hr]; decide) (by rw [hg]; decide) (by rw [hr, hg]; decide)]; decide
  · -- `A × C`: not an `A`-symbol
    rw [hr, hg]
    intro h
    have h0 : cl (L r g) = 0 := by
      revert h; generalize cl (L r g) = i; fin_cases i <;> decide
    obtain ⟨g', hg', h'⟩ := hrowA r hr _ h0
    rw [← hLP' r g' (by rw [hr]; decide) (by rw [hg']; decide)] at h'
    have := hrowinj r g' g h'
    rw [this, hg] at hg'; exact absurd hg' (by decide)
  · rw [hLP' r g (by rw [hr]; decide) (by rw [hg]; decide), hr, hg,
      hP3 r g (by rw [hr]; decide) (by rw [hg]; decide) (by rw [hr, hg]; decide)]; decide
  · have h4 := hP4 r g hr hg
    rw [hLP' r g (by rw [hr]; decide) (by rw [hg]; decide), hr, hg]
    revert h4; generalize cl (P r g) = i; fin_cases i <;> decide
  · -- `B × C`: not a `C`-symbol
    rw [hr, hg]
    intro h
    have h2 : cl (L r g) = 2 := by
      revert h; generalize cl (L r g) = i; fin_cases i <;> decide
    obtain ⟨g', hg', h'⟩ := hP5r r hr _ h2
    rw [← hLP' r g' (by rw [hr]; decide) hg'] at h'
    have := hrowinj r g' g h'
    rw [this, hg] at hg'; exact hg' rfl
  · -- `C × A`: not an `A`-symbol
    rw [hr, hg]
    intro h
    have h0 : cl (L r g) = 0 := by
      revert h; generalize cl (L r g) = i; fin_cases i <;> decide
    obtain ⟨r', hr', h'⟩ := hcolA g hg _ h0
    rw [← hLP' r' g (by rw [hr']; decide) (by rw [hg]; decide)] at h'
    have := hcolinj g r' r h'
    rw [this, hr] at hr'; exact absurd hr' (by decide)
  · -- `C × B`: not a `C`-symbol
    rw [hr, hg]
    intro h
    have h2 : cl (L r g) = 2 := by
      revert h; generalize cl (L r g) = i; fin_cases i <;> decide
    obtain ⟨r', hr', h'⟩ := hP5c g hg _ h2
    rw [← hLP' r' g hr' (by rw [hg]; decide)] at h'
    have := hcolinj g r' r h'
    rw [this, hr] at hr'; exact hr' rfl
  · -- `C × C`: not a `B`-symbol
    rw [hr, hg]
    intro h
    have h1 : cl (L r g) = 1 := by
      revert h; generalize cl (L r g) = i; fin_cases i <;> decide
    obtain ⟨r', hr', h'⟩ := hCC g hg _ h1
    have := hcolinj g r' r h'
    rw [this, hr] at hr'; exact hr' rfl

end CDRBicolour.Latin
