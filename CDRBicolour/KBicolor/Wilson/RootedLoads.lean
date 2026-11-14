/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.TypeKernel

/-!
# Exact root corrections and improved local load error

Each root exclusion costs at most one kernel bound, not two: for 0<=s,b<=1,
|s-b|<=1. The LP-optimal weights then give a load error (EG+ER)/x, replacing
the older upper-bound estimate 2*(EG+ER)/x.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset

def rootedMass {k : ℕ} (z w : Fin k → ℝ) (i j : Fin k) (bi bj : ℝ) : ℝ :=
  (∑ l, z l * w l) - bi * w i - bj * w j

theorem rooted_mass_error {k : ℕ} (z c w : Fin k → ℝ) (i j : Fin k)
    {s E C bi bj : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hbi : 0 ≤ bi ∧ bi ≤ 1) (hbj : 0 ≤ bj ∧ bj ≤ 1)
    (hz : ∀ l, |z l - s * c l| ≤ E) (hw : ∀ l, |w l| ≤ C)
    (href : (∑ l, c l * w l) - w i - w j = 1) :
    |rootedMass z w i j bi bj - s| ≤ (k : ℝ) * E * C + 2 * C := by
  have hid : rootedMass z w i j bi bj - s =
      ((∑ l, z l * w l) - s * ∑ l, c l * w l) +
        (s - bi) * w i + (s - bj) * w j := by
    unfold rootedMass
    linear_combination s * href
  have hcoeffi : |s - bi| ≤ 1 := abs_le.mpr ⟨by linarith [hbi.2], by linarith [hbi.1]⟩
  have hcoeffj : |s - bj| ≤ 1 := abs_le.mpr ⟨by linarith [hbj.2], by linarith [hbj.1]⟩
  have hri : |(s - bi) * w i| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul hcoeffi (hw i) (abs_nonneg _) (by norm_num)).trans_eq (one_mul C)
  have hrj : |(s - bj) * w j| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul hcoeffj (hw j) (abs_nonneg _) (by norm_num)).trans_eq (one_mul C)
  have hmain := weighted_class_discrepancy z c w hE hC hz hw
  rw [hid]
  have htri1 := abs_add_le ((∑ l, z l * w l) - s * ∑ l, c l * w l) ((s - bi) * w i)
  have htri2 := abs_add_le (((∑ l, z l * w l) - s * ∑ l, c l * w l) +
    (s - bi) * w i) ((s - bj) * w j)
  linarith

def targetLoad (g : ℝ) (j : ℕ) : ℝ := if j = 2 then 1 / g else 1

theorem optimal_load_eq {g x y : ℝ} (hg : 1 ≤ g) (hx : 0 < x) (hy : 0 ≤ y)
    (j : ℕ) (hj : j ≤ 2) :
    x * optimalWeight g x y j + y * optimalWeight g x y (j + 1) = targetLoad g j := by
  interval_cases j
  · simpa [targetLoad] using optimal_eq0 (g := g) (y := y) hx
  · simpa [targetLoad] using optimal_eq1 (g := g) (y := y) hx
  · simpa [targetLoad] using optimal_eq2 (x := x) (y := y) (by linarith) (by linarith)

theorem optimal_load_error {g x y G R EG ER : ℝ} (hg : 1 ≤ g) (hx : 0 < x)
    (hy : 0 ≤ y) (hyx : y ≤ x) (hEG : 0 ≤ EG) (hER : 0 ≤ ER)
    (hG : |G - x| ≤ EG) (hR : |R - y| ≤ ER) (j : ℕ) (hj : j ≤ 2) :
    |G * optimalWeight g x y j + R * optimalWeight g x y (j + 1) - targetLoad g j| ≤
      (EG + ER) / x := by
  obtain ⟨hl0, hu0⟩ := optimalWeight_bounds hg hx hy hyx j
  obtain ⟨hl1, hu1⟩ := optimalWeight_bounds hg hx hy hyx (j + 1)
  have hfloor : 0 < optimalFloor g x y := by unfold optimalFloor; positivity
  have hp0 := hfloor.le.trans hl0
  have hp1 := hfloor.le.trans hl1
  rw [← optimal_load_eq hg hx hy j hj]
  have hid : G * optimalWeight g x y j + R * optimalWeight g x y (j + 1) -
      (x * optimalWeight g x y j + y * optimalWeight g x y (j + 1)) =
      (G - x) * optimalWeight g x y j + (R - y) * optimalWeight g x y (j + 1) := by ring
  rw [hid]
  calc
    _ ≤ |(G - x) * optimalWeight g x y j| +
        |(R - y) * optimalWeight g x y (j + 1)| := abs_add_le _ _
    _ = |G - x| * optimalWeight g x y j + |R - y| * optimalWeight g x y (j + 1) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hp1]
    _ ≤ EG * (1 / x) + ER * (1 / x) :=
      add_le_add (mul_le_mul hG hu0 hp0 hEG) (mul_le_mul hR hu1 hp1 hER)
    _ = _ := by ring

end CDRBicolour.KBicolor.Wilson
