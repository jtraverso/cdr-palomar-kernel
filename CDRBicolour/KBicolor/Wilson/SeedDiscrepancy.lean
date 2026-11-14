/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.SeedCorrection

/-!
# Weighted discrepancy estimates for the approximate local seed

Approximation of class proportions controls every type-uniform weighted third-
vertex sum. The group discrepancy is at most `ξ n` per colour; the reserve
discrepancy is at most g times the group discrepancy. These are estimates for
constructing H1, not an assertion that its approximate seed is already assembled.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset

theorem weighted_class_discrepancy {k : ℕ} (x c w : Fin k → ℝ) {s E C : ℝ}
    (hE : 0 ≤ E) (hC : 0 ≤ C) (hx : ∀ i, |x i - s * c i| ≤ E)
    (hw : ∀ i, |w i| ≤ C) :
    |∑ i, x i * w i - s * ∑ i, c i * w i| ≤ (k : ℝ) * E * C := by
  have hid : ∑ i, x i * w i - s * ∑ i, c i * w i = ∑ i, (x i - s * c i) * w i := by
    simp only [sub_mul, sum_sub_distrib, ← mul_sum, mul_assoc]
  rw [hid]
  calc
    _ ≤ ∑ i, |(x i - s * c i) * w i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, E * C := sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul (hx i) (hw i) (abs_nonneg _) hE
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem group_size_discrepancy {k n N t : ℕ} (c m : Fin k → ℕ) {ξ : ℝ}
    (hn : 0 < n) (hN : 0 < N) (hξ : 0 ≤ ξ)
    (hsize : (t : ℝ) * N ≤ n)
    (hclose : ∀ i, |(m i : ℝ) / N - (c i : ℝ) / n| ≤ ξ) :
    ∀ i, |(m i : ℝ) * t - ((t : ℝ) * N / n) * c i| ≤ ξ * n := by
  intro i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hid : (m i : ℝ) * t - ((t : ℝ) * N / n) * c i =
      ((t : ℝ) * N) * ((m i : ℝ) / N - (c i : ℝ) / n) := by field_simp <;> ring
  rw [hid, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) * N)]
  calc
    _ ≤ ((t : ℝ) * N) * ξ := mul_le_mul_of_nonneg_left (hclose i) (by positivity)
    _ ≤ (n : ℝ) * ξ := mul_le_mul_of_nonneg_right hsize hξ
    _ = _ := by ring

theorem reserve_size_discrepancy {k : ℕ} (x c : Fin k → ℝ) {g s E : ℝ}
    (hg : 0 ≤ g) (hx : ∀ i, |x i - s * c i| ≤ E) :
    ∀ i, |(c i - g * x i) - (1 - g * s) * c i| ≤ g * E := by
  intro i
  have hid : (c i - g * x i) - (1 - g * s) * c i = -g * (x i - s * c i) := by ring
  rw [hid, abs_mul, abs_neg, abs_of_nonneg hg]
  exact mul_le_mul_of_nonneg_left (hx i) hg

end CDRBicolour.KBicolor.Wilson
