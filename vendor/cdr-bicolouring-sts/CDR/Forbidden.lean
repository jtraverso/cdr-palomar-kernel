/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDR.Ryser
public import CDR.DeWerra

/-!
# Forbidden latin squares (Colbourn–Dinitz–Rosa, Lemma 2.3)

Let `N = A ∪ B ∪ C` be split into classes `A, B, C` of sizes `a, b, c`, recorded by a labelling
`lab : N → Fin 3` (`A = 0`, `B = 1`, `C = 2`). A latin square `L` with rows, columns and symbols
indexed by `N` is *`(a, b, c)`-forbidden* if the symbol in cell `(r, g)` avoids the class
`forbiddenClass (lab r) (lab g)` of the table of the paper:

| row \ column | A | B | C |
|---|---|---|---|
| A | not C | not B | not A |
| B | not B | not A | not C |
| C | not A | not C | not B |

**Lemma 2.3** (sufficiency, the direction used in Theorem 2.4): if `c = max(a, b, c)` and
`c ≤ a + b` (that is, `max(a, b, c) ≤ n/2`), an `(a, b, c)`-forbidden latin square exists
(`exists_forbidden_latin`). The paper's "necessity is obvious" holds when the three classes
are nonempty, but not in general: `(a, b, c) = (1, 0, 2)` admits a forbidden latin square of
order `3` although `c > n/2`.
-/

@[expose] public section

namespace CDR

open Finset

/-- The forbidden class of the symbol in a cell, by the classes of its row and column. -/
def forbiddenClass : Fin 3 → Fin 3 → Fin 3 :=
  ![![2, 1, 0], ![1, 0, 2], ![0, 2, 1]]

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- `L` is a forbidden latin square for the class labelling `lab`. -/
def IsForbiddenLatin (lab : N → Fin 3) (L : N → N → N) : Prop :=
  IsLatinSquare L ∧ ∀ r g, lab (L r g) ≠ forbiddenClass (lab r) (lab g)


theorem forbiddenClass_eq (i j : Fin 3) : forbiddenClass i j = -(i + j + 1) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  fin_cases x <;> simp

/-- The class `k` of the labelling as a finset. -/
def cls (lab : N → Fin 3) (k : Fin 3) : Finset N := Finset.univ.filter fun x => lab x = k

/-- The cells of `A ∪ B`: points not in `C`. -/
def clsAB (lab : N → Fin 3) : Finset N := Finset.univ.filter fun x => lab x ≠ 2

theorem card_univ_eq_sum_cls (lab : N → Fin 3) :
    Fintype.card N = #(cls lab 0) + #(cls lab 1) + #(cls lab 2) := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := lab) (t := Finset.univ)
    (fun x _ => Finset.mem_univ _), Fin.sum_univ_three]
  rfl

theorem card_clsAB (lab : N → Fin 3) : #(clsAB lab) = #(cls lab 0) + #(cls lab 1) := by
  classical
  have : clsAB lab = cls lab 0 ∪ cls lab 1 := by
    ext x
    rcases fin3_cases (lab x) with h | h | h <;> simp [clsAB, cls, h]
  rw [this, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [cls, Finset.mem_filter] at hx hx'
  rw [hx.2] at hx'
  exact absurd hx'.2 (by decide)

/-- The properties of the array on `(A ∪ B) × (A ∪ B)` used to complete it (Lemma 2.3). -/
structure GoodArray (lab : N → Fin 3) (P : N → N → N) (d : ℕ) : Prop where
  latin : IsLatinOn (clsAB lab) (clsAB lab) P
  aa : ∀ r g, lab r = 0 → lab g = 0 → lab (P r g) = 0
  aaRow : ∀ r, lab r = 0 → ∀ σ, lab σ = 0 → ∃ g, lab g = 0 ∧ P r g = σ
  aaCol : ∀ g, lab g = 0 → ∀ σ, lab σ = 0 → ∃ r, lab r = 0 ∧ P r g = σ
  ab : ∀ r g, lab r = 0 → lab g = 1 → lab (P r g) = 2
  ba : ∀ r g, lab r = 1 → lab g = 0 → lab (P r g) = 2
  bb : ∀ r g, lab r = 1 → lab g = 1 → lab (P r g) ≠ 0
  bRowC : ∀ r, lab r = 1 → ∀ σ, lab σ = 2 → ∃ g, lab g ≠ 2 ∧ P r g = σ
  bColC : ∀ g, lab g = 1 → ∀ σ, lab σ = 2 → ∃ r, lab r ≠ 2 ∧ P r g = σ
  bCount : ∀ σ, lab σ = 1 →
    #(Finset.univ.filter fun r => lab r = 1 ∧ ∃ g, lab g = 1 ∧ P r g = σ) = d


theorem mem_clsAB {lab : N → Fin 3} {x : N} : x ∈ clsAB lab ↔ lab x ≠ 2 := by
  simp [clsAB]

theorem mem_cls {lab : N → Fin 3} {x : N} {k : Fin 3} : x ∈ cls lab k ↔ lab x = k := by
  simp [cls]

/-- Ryser's condition for a good array. -/
theorem GoodArray.ryserCond {lab : N → Fin 3} {P : N → N → N}
    (hP : GoodArray lab P (#(cls lab 0) + #(cls lab 1) - #(cls lab 2)))
    (ha : #(cls lab 0) ≤ #(cls lab 2)) (hb : #(cls lab 1) ≤ #(cls lab 2)) :
    RyserCond (clsAB lab) (clsAB lab) P := by
  intro σ
  rw [card_clsAB, card_univ_eq_sum_cls lab]
  suffices h : #(cls lab 0) + #(cls lab 1) - #(cls lab 2) ≤
      rowCount (clsAB lab) (clsAB lab) P σ by omega
  rcases fin3_cases (lab σ) with hσ | hσ | hσ
  · refine le_trans (by omega) (card_le_card (s := cls lab 0) ?_)
    intro r hr
    rw [mem_cls] at hr
    obtain ⟨g, hg, hPg⟩ := hP.aaRow r hr σ hσ
    simp only [mem_filter, mem_clsAB]
    refine ⟨by rw [hr]; decide, g, by rw [hg]; decide, hPg⟩
  · rw [← hP.bCount σ hσ]
    apply card_le_card
    intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    obtain ⟨hr, g, hg, hPg⟩ := hr
    simp only [mem_filter, mem_clsAB]
    exact ⟨by rw [hr]; decide, g, by rw [hg]; decide, hPg⟩
  · refine le_trans (by omega) (card_le_card (s := cls lab 1) ?_)
    intro r hr
    rw [mem_cls] at hr
    obtain ⟨g, hg, hPg⟩ := hP.bRowC r hr σ hσ
    simp only [mem_filter, mem_clsAB]
    exact ⟨by rw [hr]; decide, g, hg, hPg⟩

/-- In a latin square, the column of a symbol in each row. -/
theorem exists_col_bijective {L : N → N → N} (hL : IsLatinSquare L) (β : N) :
    ∃ col : N → N, Function.Bijective col ∧ ∀ r, L r (col r) = β := by
  choose col hcol using fun r => (hL.1 r).2 β
  refine ⟨col, ?_, hcol⟩
  have hinj : Function.Injective col := by
    intro r r' h
    apply (hL.2 (col r)).1
    simp only
    rw [hcol r, h, hcol r']
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

/-- **The `(C, C)` block.** In the completion of a good array, no symbol of `B` lies in a cell
with row and column in `C`. -/
theorem not_mem_B_of_CC {lab : N → Fin 3} {P L : N → N → N}
    (hP : GoodArray lab P (#(cls lab 0) + #(cls lab 1) - #(cls lab 2)))
    (ha : #(cls lab 0) ≤ #(cls lab 2)) (hb : #(cls lab 1) ≤ #(cls lab 2))
    (hc : #(cls lab 2) ≤ #(cls lab 0) + #(cls lab 1)) (hL : IsLatinSquare L) (hagree : ∀ r ∈ clsAB lab, ∀ g ∈ clsAB lab, L r g = P r g)
    {r₀ g₀ : N} (hr₀ : lab r₀ = 2) (hg₀ : lab g₀ = 2) : lab (L r₀ g₀) ≠ 1 := by
  intro hβ
  set β := L r₀ g₀
  obtain ⟨col, hbij, hcol⟩ := exists_col_bijective hL β
  have hcol₀ : col r₀ = g₀ := (hL.1 r₀).1 (by rw [hcol r₀])
  have hag : ∀ r g, lab r ≠ 2 → lab g ≠ 2 → L r g = P r g := fun r g hr hg =>
    hagree r (mem_clsAB.2 hr) g (mem_clsAB.2 hg)
  -- the fibres of `lab ∘ col`
  have hcard : ∀ k, #(univ.filter fun r => lab (col r) = k) = #(cls lab k) := by
    intro k
    refine card_bij (fun r _ => col r) (fun r hr => ?_) (fun r _ r' _ h => hbij.1 h) ?_
    · simpa [cls] using hr
    · intro g hg
      obtain ⟨r, rfl⟩ := hbij.2 g
      exact ⟨r, by simpa [cls] using hg, rfl⟩
  -- rows whose `β` lies in a column of `A` are rows of `C`
  have hA : (univ.filter fun r => lab (col r) = 0) =
      univ.filter fun r => lab r = 2 ∧ lab (col r) = 0 := by
    ext r
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    rcases fin3_cases (lab r) with hr | hr | hr
    · have := hP.aa r (col r) hr h
      rw [← hag r (col r) (by rw [hr]; decide) (by rw [h]; decide), hcol] at this
      rw [this] at hβ
      exact absurd hβ (by decide)
    · have := hP.ba r (col r) hr h
      rw [← hag r (col r) (by rw [hr]; decide) (by rw [h]; decide), hcol] at this
      rw [this] at hβ
      exact absurd hβ (by decide)
    · exact hr
  -- rows whose `β` lies in a column of `B` are rows of `B` or `C`
  have hB : #(univ.filter fun r => lab (col r) = 1) =
      #(univ.filter fun r => lab r = 1 ∧ ∃ g, lab g = 1 ∧ P r g = β) +
        #(univ.filter fun r => lab r = 2 ∧ lab (col r) = 1) := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext r
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · intro h
        rcases fin3_cases (lab r) with hr | hr | hr
        · have := hP.ab r (col r) hr h
          rw [← hag r (col r) (by rw [hr]; decide) (by rw [h]; decide), hcol] at this
          rw [this] at hβ
          exact absurd hβ (by decide)
        · exact Or.inl ⟨hr, col r, h, by
            rw [← hag r (col r) (by rw [hr]; decide) (by rw [h]; decide), hcol]⟩
        · exact Or.inr ⟨hr, h⟩
      · rintro (⟨hr, g, hg, hPg⟩ | ⟨-, h⟩)
        · have : col r = g := (hL.1 r).1 (by
            rw [hcol, hag r g (by rw [hr]; decide) (by rw [hg]; decide), hPg])
          rw [this, hg]
        · exact h
    · rw [disjoint_left]
      intro r h h'
      simp only [mem_filter, mem_univ, true_and] at h h'
      rw [h.1] at h'
      exact absurd h'.1 (by decide)
  -- the rows of `C` split by the class of the column of `β`
  have hC : #(cls lab 2) = #(univ.filter fun r => lab r = 2 ∧ lab (col r) = 0) +
      #(univ.filter fun r => lab r = 2 ∧ lab (col r) = 1) +
      #(univ.filter fun r => lab r = 2 ∧ lab (col r) = 2) := by
    rw [card_eq_sum_card_fiberwise (f := fun r => lab (col r)) (t := univ)
      (fun _ _ => mem_univ _), Fin.sum_univ_three]
    simp only [cls, filter_filter]
  rw [hcard 1, hP.bCount β hβ] at hB
  rw [← hA, hcard 0] at hC
  simp only [cls] at hB hC ha hb hc
  have h0 : #(univ.filter fun r => lab r = 2 ∧ lab (col r) = 2) = 0 := by omega
  rw [card_eq_zero, filter_eq_empty_iff] at h0
  exact h0 (mem_univ r₀) ⟨hr₀, by rw [hcol₀, hg₀]⟩

/-- **Completion.** A good array on `(A ∪ B) × (A ∪ B)` completes to an `(a, b, c)`-forbidden
latin square when `a, b ≤ c ≤ a + b`. -/
theorem exists_forbidden_of_goodArray {lab : N → Fin 3} {P : N → N → N}
    (hP : GoodArray lab P (#(cls lab 0) + #(cls lab 1) - #(cls lab 2)))
    (ha : #(cls lab 0) ≤ #(cls lab 2)) (hb : #(cls lab 1) ≤ #(cls lab 2))
    (hc : #(cls lab 2) ≤ #(cls lab 0) + #(cls lab 1)) :
    ∃ L : N → N → N, IsForbiddenLatin lab L := by
  obtain ⟨L, hL, hagree⟩ := ryser rfl hP.latin (hP.ryserCond ha hb)
  refine ⟨L, hL, fun r g => ?_⟩
  have hag : ∀ r g, lab r ≠ 2 → lab g ≠ 2 → L r g = P r g := fun r g hr hg =>
    hagree r (mem_clsAB.2 hr) g (mem_clsAB.2 hg)
  have hrow : ∀ {r g g'}, L r g = L r g' → g = g' := fun h => (hL.1 _).1 h
  have hcolinj : ∀ {r r' g}, L r g = L r' g → r = r' := fun h => (hL.2 _).1 h
  rcases fin3_cases (lab r) with hr | hr | hr <;> rcases fin3_cases (lab g) with hg | hg | hg <;>
    rw [hr, hg]
  -- (A, A)
  · rw [hag r g (by rw [hr]; decide) (by rw [hg]; decide), hP.aa r g hr hg]; decide
  -- (A, B)
  · rw [hag r g (by rw [hr]; decide) (by rw [hg]; decide), hP.ab r g hr hg]; decide
  -- (A, C): the symbols of `A` already lie in the columns of `A`
  · show lab (L r g) ≠ 0
    intro h
    obtain ⟨g', hg', hPg'⟩ := hP.aaRow r hr (L r g) h
    rw [← hag r g' (by rw [hr]; decide) (by rw [hg']; decide)] at hPg'
    have := hrow hPg'
    rw [← this, hg'] at hg
    exact absurd hg (by decide)
  -- (B, A)
  · rw [hag r g (by rw [hr]; decide) (by rw [hg]; decide), hP.ba r g hr hg]; decide
  -- (B, B)
  · rw [hag r g (by rw [hr]; decide) (by rw [hg]; decide)]; exact hP.bb r g hr hg
  -- (B, C): the symbols of `C` already lie in the row within `A ∪ B`
  · show lab (L r g) ≠ 2
    intro h
    obtain ⟨g', hg', hPg'⟩ := hP.bRowC r hr (L r g) h
    rw [← hag r g' (by rw [hr]; decide) hg'] at hPg'
    have := hrow hPg'
    rw [← this] at hg
    exact hg' hg
  -- (C, A)
  · show lab (L r g) ≠ 0
    intro h
    obtain ⟨r', hr', hPr'⟩ := hP.aaCol g hg (L r g) h
    rw [← hag r' g (by rw [hr']; decide) (by rw [hg]; decide)] at hPr'
    have := hcolinj hPr'
    rw [← this, hr'] at hr
    exact absurd hr (by decide)
  -- (C, B)
  · show lab (L r g) ≠ 2
    intro h
    obtain ⟨r', hr', hPr'⟩ := hP.bColC g hg (L r g) h
    rw [← hag r' g hr' (by rw [hg]; decide)] at hPr'
    have := hcolinj hPr'
    rw [← this] at hr
    exact hr' hr
  -- (C, C)
  · exact not_mem_B_of_CC hP ha hb hc hL hagree hr hg

end CDR
