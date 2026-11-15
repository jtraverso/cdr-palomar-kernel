/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Pattern.Hilton

/-!
# k-bicoloured Latin squares from integer tournaments

A *k-bicoloured Latin square* of order `N` with class map `κ : α → Fin k` is a Latin square
`L : α → α → α` such that in every cell the classes `κ x, κ y, κ (L x y)` take exactly two values
(`bic`). Counting monochromatic pairs gives `3 Σ m_P² = N²` for the class sizes `m_P`.

The outline of such a square is determined by an integer *tournament* `x : Fin k → Fin k → ℕ` with
`x P P = 0`, `x P Q + x Q P = m P * m Q` (`P ≠ Q`) and `Σ_Q x P Q = m P ^ 2`:

* cells of row class `P` and column class `P` get symbols of class `R ≠ P`, `x P R` of them;
* cells of row class `P ≠ Q` and column class `Q` get `x P Q` symbols of class `P` and `x Q P` of
  class `Q`.

`kbls_of_tournament` turns such a tournament into the square, through Hilton's amalgamation
theorem (`Hilton.realize`).
-/

@[expose] public section

namespace CDRBicolour.KBicolor.Pattern

open Finset

variable {k : ℕ}

/-- A class triple with exactly two distinct values. -/
def bic (P Q R : Fin k) : Prop := (P = Q ∧ R ≠ P) ∨ (P ≠ Q ∧ (R = P ∨ R = Q))

/-- The outline attached to a tournament (with `x P P = 0` the three terms never overlap). -/
def outline (x : Fin k → Fin k → ℕ) (P Q R : Fin k) : ℕ :=
  (if Q = P then x P R else 0) + (if R = P then x P Q else 0) + (if R = Q then x Q P else 0)

/-- Tournament conditions. -/
structure IsTour (m : Fin k → ℕ) (x : Fin k → Fin k → ℕ) : Prop where
  diag : ∀ P, x P P = 0
  pair : ∀ P Q, P ≠ Q → x P Q + x Q P = m P * m Q
  row : ∀ P, ∑ Q, x P Q = m P * m P

variable {m : Fin k → ℕ} {x : Fin k → Fin k → ℕ}

theorem outline_zero (hx : IsTour m x) (P Q R : Fin k) (h : ¬ bic P Q R) :
    outline x P Q R = 0 := by
  unfold bic at h; unfold outline
  by_cases hPQ : P = Q
  · subst hPQ
    have hR : R = P := by by_contra hR; exact h (Or.inl ⟨rfl, hR⟩)
    subst hR; simp [hx.diag]
  · have h1 : R ≠ P := fun e => h (Or.inr ⟨hPQ, Or.inl e⟩)
    have h2 : R ≠ Q := fun e => h (Or.inr ⟨hPQ, Or.inr e⟩)
    have h3 : Q ≠ P := fun e => hPQ e.symm
    simp [h1, h2, h3]

/-- Cell marginal. -/
theorem outline_cell (hx : IsTour m x) (P Q : Fin k) :
    ∑ R, outline x P Q R = m P * m Q := by
  unfold outline
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hPQ : Q = P
  · subst hPQ; simp [hx.diag, hx.row]
  · simp only [hPQ, if_false, Finset.sum_const_zero, zero_add]
    exact hx.pair P Q (fun e => hPQ e.symm)

/-- Row–symbol marginal. -/
theorem outline_row (hx : IsTour m x) (P R : Fin k) :
    ∑ Q, outline x P Q R = m P * m R := by
  unfold outline
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  by_cases hRP : R = P
  · subst hRP; simp [hx.diag, hx.row]
  · simp only [hRP, if_false, Finset.sum_const_zero, add_zero]
    exact hx.pair P R (fun e => hRP e.symm)

/-- Column–symbol marginal. -/
theorem outline_col (hx : IsTour m x) (Q R : Fin k) :
    ∑ P, outline x P Q R = m Q * m R := by
  unfold outline
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  by_cases hRQ : R = Q
  · subst hRQ; simp [hx.diag, hx.row]
  · simp only [hRQ, if_false, Finset.sum_const_zero, add_zero]
    exact hx.pair Q R (fun e => hRQ e.symm)

/-- **k-bicoloured Latin squares from tournaments.** -/
theorem kbls_of_tournament {α : Type*} [Fintype α] [DecidableEq α] (κ : α → Fin k)
    (hm : ∀ P, Hilton.csize κ P = m P) (hx : IsTour m x) :
    ∃ L : α → α → α, (∀ a, Function.Bijective (L a)) ∧
      (∀ b, Function.Bijective (fun a => L a b)) ∧ ∀ a b, bic (κ a) (κ b) (κ (L a b)) := by
  refine Hilton.realize bic κ κ κ (outline x) (fun P Q => ?_) (fun P R => ?_) (fun Q R => ?_)
    (fun P Q R h => outline_zero hx P Q R h)
  · rw [hm, hm]; exact outline_cell hx P Q
  · rw [hm, hm]; exact outline_row hx P R
  · rw [hm, hm]; exact outline_col hx Q R

end CDRBicolour.KBicolor.Pattern
