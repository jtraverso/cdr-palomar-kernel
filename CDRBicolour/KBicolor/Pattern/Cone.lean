/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Integer points on the cone `3 Σ m² = (Σ m)²`, explicitly

The class sizes `m` of a k-bicoloured Latin square satisfy `3 Σ m_P² = (Σ m_P)²`. With
`Q(x) = 3 Σ x² − (Σ x)²`, a set `E` of three classes (so `Q(1_E) = 0`) and any `c` with
`Q(c) = q ≥ 0`, the second intersection of the line through `1_E` and `c` with the cone is

    m = q · 1_E + 6 σ · c,   σ = Σ_{P ∉ E} c_P.

`cone_point` checks `3 Σ m² = (Σ m)²`, and `cone_point_close` bounds `|m_P/N − c_P/Σc| ≤ q/(2σ Σc)`.
No representation theorem for quadratic forms is needed because the order `N` is free.
-/

@[expose] public section

namespace CDRBicolour.KBicolor.Pattern

open Finset

variable {k : ℕ}

/-- The cone point attached to `c`. -/
def conePt (E : Finset (Fin k)) (c : Fin k → ℕ) (q : ℕ) (P : Fin k) : ℕ :=
  (if P ∈ E then q else 0) + 6 * (∑ Q ∈ univ \ E, c Q) * c P

theorem sum_ind (E : Finset (Fin k)) (f : Fin k → ℤ) :
    ∑ P, (if P ∈ E then f P else 0) = ∑ P ∈ E, f P := by
  rw [← Finset.sum_filter]; congr 1; ext P; simp

theorem sum_split (E : Finset (Fin k)) (f : Fin k → ℤ) :
    ∑ P, f P = ∑ P ∈ E, f P + ∑ P ∈ univ \ E, f P := by
  rw [← Finset.sum_union disjoint_sdiff, union_sdiff_of_subset (subset_univ E)]

/-- **The cone identity.** -/
theorem cone_point (E : Finset (Fin k)) (hE : #E = 3) (c : Fin k → ℕ) (q : ℕ)
    (hq : (q : ℤ) = 3 * ∑ P, (c P : ℤ) ^ 2 - (∑ P, (c P : ℤ)) ^ 2) :
    3 * ∑ P, conePt E c q P ^ 2 = (∑ P, conePt E c q P) ^ 2 := by
  set σ : ℤ := ∑ Q ∈ univ \ E, (c Q : ℤ) with hσ
  set S1 : ℤ := ∑ P, (c P : ℤ) with hS1
  set S2 : ℤ := ∑ P, (c P : ℤ) ^ 2 with hS2
  have hcast : ∀ P, (conePt E c q P : ℤ) = (if P ∈ E then (q : ℤ) else 0) + 6 * σ * c P := by
    intro P; unfold conePt; push_cast; split_ifs <;> simp [hσ]
  have hEc : ∑ P ∈ E, (c P : ℤ) = S1 - σ := by rw [hS1, sum_split E, hσ]; ring
  have hsum : ∑ P, (conePt E c q P : ℤ) = 3 * q + 6 * σ * S1 := by
    simp only [hcast, Finset.sum_add_distrib, sum_ind, Finset.sum_const, hE, ← Finset.mul_sum]
    rw [hS1]; push_cast; ring
  have hsq : ∑ P, (conePt E c q P : ℤ) ^ 2 =
      3 * (q : ℤ) ^ 2 + 12 * q * σ * (S1 - σ) + 36 * σ ^ 2 * S2 := by
    have e : ∀ P, (conePt E c q P : ℤ) ^ 2 = (if P ∈ E then (q : ℤ) ^ 2 + 12 * q * σ * c P else 0)
        + 36 * σ ^ 2 * (c P : ℤ) ^ 2 := by
      intro P; rw [hcast]; split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, sum_ind, Finset.sum_const, hE, ← Finset.mul_sum]
    rw [hEc, hS2]; push_cast; ring
  have key : (3 * ∑ P, conePt E c q P ^ 2 : ℤ) = (∑ P, conePt E c q P : ℤ) ^ 2 := by
    push_cast; rw [hsq, hsum]; linear_combination (-36 * σ ^ 2) * hq
  exact_mod_cast key

/-- **Closeness of the cone point.** -/
theorem cone_point_close (E : Finset (Fin k)) (hE : #E = 3) (c : Fin k → ℕ) (q : ℕ)
    (hσ : 0 < ∑ Q ∈ univ \ E, c Q) (hS : 0 < ∑ P, c P) (P : Fin k) :
    |(conePt E c q P : ℝ) / (∑ Q, conePt E c q Q : ℕ) - (c P : ℝ) / (∑ Q, c Q : ℕ)| ≤
      q / (2 * (∑ Q ∈ univ \ E, c Q : ℕ) * (∑ Q, c Q : ℕ)) := by
  set σ : ℝ := ((∑ Q ∈ univ \ E, c Q : ℕ) : ℝ) with hσr
  set S1 : ℝ := ((∑ Q, c Q : ℕ) : ℝ) with hS1r
  have hσ0 : 0 < σ := by rw [hσr]; exact_mod_cast hσ
  have hS0 : 0 < S1 := by rw [hS1r]; exact_mod_cast hS
  have hcast : ∀ P, (conePt E c q P : ℝ) = (if P ∈ E then (q : ℝ) else 0) + 6 * σ * c P := by
    intro P; unfold conePt; rw [hσr]; push_cast; split_ifs <;> simp
  have hN : ((∑ Q, conePt E c q Q : ℕ) : ℝ) = 3 * q + 6 * σ * S1 := by
    push_cast
    simp only [hcast, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← Finset.sum_filter, show univ.filter (· ∈ E) = E by ext; simp, Finset.sum_const, hE,
      hS1r]
    push_cast; ring
  have hcP : (c P : ℝ) ≤ S1 := by
    rw [hS1r]; exact_mod_cast Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ P)
  have hcP0 : (0 : ℝ) ≤ c P := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hNpos : 0 < 3 * (q : ℝ) + 6 * σ * S1 := by positivity
  rw [hN, hcast P]
  -- m_P S1 − c_P N = q (e_P S1 − 3 c_P)
  have hdiff : ((if P ∈ E then (q : ℝ) else 0) + 6 * σ * c P) / (3 * q + 6 * σ * S1) - c P / S1 =
      q * ((if P ∈ E then S1 else 0) - 3 * c P) / ((3 * q + 6 * σ * S1) * S1) := by
    field_simp; split_ifs <;> ring
  rw [hdiff, abs_div, abs_of_pos (mul_pos hNpos hS0), div_le_div_iff₀ (mul_pos hNpos hS0)
    (by positivity)]
  have habs : |(q : ℝ) * ((if P ∈ E then S1 else 0) - 3 * c P)| ≤ 3 * q * S1 := by
    rw [abs_mul, abs_of_nonneg hq0]
    have hb : |(if P ∈ E then S1 else 0) - 3 * (c P : ℝ)| ≤ 3 * S1 := by
      rw [abs_le]; split_ifs <;> constructor <;> linarith
    calc (q : ℝ) * |(if P ∈ E then S1 else 0) - 3 * (c P : ℝ)| ≤ q * (3 * S1) :=
          mul_le_mul_of_nonneg_left hb hq0
      _ = 3 * q * S1 := by ring
  calc |(q : ℝ) * ((if P ∈ E then S1 else 0) - 3 * c P)| * (2 * σ * S1)
      ≤ 3 * q * S1 * (2 * σ * S1) := mul_le_mul_of_nonneg_right habs (by positivity)
    _ ≤ q * ((3 * q + 6 * σ * S1) * S1) := by nlinarith [mul_nonneg hq0 hq0, mul_pos hσ0 hS0]

end CDRBicolour.KBicolor.Pattern
