/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.SeedDiscrepancy

/-!
# LP-optimal scalar weights for the local Wilson seed

The edge-load equations are x*w0+y*w1=1, x*w1+y*w2=1 and
x*w2+y*w3=1/g. Maximizing the minimum of the four weights gives
w2=w3=1/(g*(x+y)). The last equation alone is an exact dual certificate.
For g>=1 and 0<=y<=x all four weights lie in [1/(g*(x+y)),1/x].
Unlike the previous weights, these bounds require no condition y>=x/4.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

def optimalFloor (g x y : ℝ) : ℝ := 1 / (g * (x + y))

def optimalW1 (g x y : ℝ) : ℝ := (1 - y * optimalFloor g x y) / x

def optimalW0 (g x y : ℝ) : ℝ := (1 - y * optimalW1 g x y) / x

def optimalWeight (g x y : ℝ) : ℕ → ℝ
  | 0 => optimalW0 g x y
  | 1 => optimalW1 g x y
  | _ => optimalFloor g x y

theorem optimal_eq0 {g x y : ℝ} (hx : 0 < x) :
    x * optimalWeight g x y 0 + y * optimalWeight g x y 1 = 1 := by
  simp only [optimalWeight, optimalW0]
  field_simp
  ring

theorem optimal_eq1 {g x y : ℝ} (hx : 0 < x) :
    x * optimalWeight g x y 1 + y * optimalWeight g x y 2 = 1 := by
  simp only [optimalWeight, optimalW1]
  field_simp
  ring

theorem optimal_eq2 {g x y : ℝ} (hg : 0 < g) (hxy : 0 < x + y) :
    x * optimalWeight g x y 2 + y * optimalWeight g x y 3 = 1 / g := by
  simp only [optimalWeight, optimalFloor]
  field_simp

/-- Exact LP dual certificate: no feasible weights have a larger common lower bound. -/
theorem optimal_dual {g x y m u v : ℝ} (hg : 0 < g) (hx : 0 < x) (hy : 0 ≤ y)
    (hu : m ≤ u) (hv : m ≤ v) (heq : x * u + y * v = 1 / g) :
    m ≤ optimalFloor g x y := by
  have hxy : 0 < x + y := by linarith
  have hsum : (x + y) * m ≤ 1 / g := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hu),
      mul_nonneg hy (sub_nonneg.mpr hv)]
  calc
    m ≤ (1 / g) / (x + y) := (le_div_iff₀ hxy).mpr (by nlinarith)
    _ = optimalFloor g x y := by unfold optimalFloor; field_simp

/-- Universal optimal lower bound and improved upper bound. -/
theorem optimalWeight_bounds {g x y : ℝ} (hg : 1 ≤ g) (hx : 0 < x)
    (hy : 0 ≤ y) (hyx : y ≤ x) (j : ℕ) :
    optimalFloor g x y ≤ optimalWeight g x y j ∧ optimalWeight g x y j ≤ 1 / x := by
  have hg0 : 0 < g := by linarith
  have hxy : 0 < x + y := by linarith
  have hb : 0 < optimalFloor g x y := by unfold optimalFloor; positivity
  have he0 := optimal_eq0 (g := g) (y := y) hx
  have he1 := optimal_eq1 (g := g) (y := y) hx
  have he2 := optimal_eq2 (x := x) (y := y) hg0 hxy
  simp only [optimalWeight] at he0 he1 he2
  have hrec : 1 / g ≤ 1 := (div_le_one hg0).mpr hg
  have h1lo : optimalFloor g x y ≤ optimalW1 g x y := by nlinarith
  have h0lo : optimalFloor g x y ≤ optimalW0 g x y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (sub_nonneg.mpr h1lo)]
  have hbup : optimalFloor g x y ≤ 1 / x := by
    apply (le_div_iff₀ hx).mpr
    nlinarith [mul_nonneg hy hb.le]
  have h1up : optimalW1 g x y ≤ 1 / x := by
    apply (le_div_iff₀ hx).mpr
    nlinarith [mul_nonneg hy hb.le]
  have h0up : optimalW0 g x y ≤ 1 / x := by
    apply (le_div_iff₀ hx).mpr
    nlinarith [mul_nonneg hy (hb.le.trans h1lo)]
  cases j with
  | zero => exact ⟨h0lo, h0up⟩
  | succ j => cases j with
    | zero => exact ⟨h1lo, h1up⟩
    | succ j => exact ⟨le_rfl, hbup⟩

theorem old_floor_le_optimal {g x y : ℝ} (hg : 1 ≤ g) (hx : 0 < x)
    (hy : 0 ≤ y) (hyx : y ≤ x) :
    1 / (2 * g * x) ≤ optimalFloor g x y := by
  have hg0 : 0 < g := by linarith
  unfold optimalFloor
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < g * (x + y))
  nlinarith [mul_le_mul_of_nonneg_left hyx hg0.le]

/-- The minimum improves by 4/3 when the reserve/group mass ratio is 1/2. -/
theorem half_ratio_gain {g x : ℝ} (hg : 0 < g) (hx : 0 < x) :
    optimalFloor g x (x / 2) = (4 / 3) * (1 / (2 * g * x)) := by
  unfold optimalFloor
  field_simp
  ring

/-- Improvement of the certified minimum/maximum ratio, not of the leading count coefficient. -/
theorem half_ratio_conditioning_gain {g x : ℝ} (hg : 0 < g) (hx : 0 < x) :
    optimalFloor g x (x / 2) / (1 / x) =
      (8 / 3) * ((1 / (2 * g * x)) / (2 / x)) := by
  unfold optimalFloor
  field_simp
  ring

theorem optimal_example :
    optimalWeight 103 1 (1/2) 0 = 155/309 ∧
    optimalWeight 103 1 (1/2) 1 = 308/309 ∧
    optimalWeight 103 1 (1/2) 2 = 2/309 ∧
    optimalWeight 103 1 (1/2) 3 = 2/309 := by
  norm_num [optimalWeight, optimalW0, optimalW1, optimalFloor]

end CDRBicolour.KBicolor.Wilson
