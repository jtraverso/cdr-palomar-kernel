/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.Geometry

/-!
# Compatibility of the local seed loads

Write x for the colour sizes in one group and y for the reserve sizes, so the
whole profile is gx+y. If x lies on the quadratic cone and gx+y satisfies the
Steiner pair identity, then the defect of x+y is `(1-1/g)` times the defect of y.
This is the exact cancellation needed when reserve edges receive weight `1/g`
in each of the g local pieces. It is not an approximate balance statement.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Finset

variable {ι : Type*} [Fintype ι]

def coneQuadratic (z : ι → ℝ) : ℝ := 3 * ∑ i, z i ^ 2 - (∑ i, z i) ^ 2

def profileDefect (z : ι → ℝ) : ℝ := coneQuadratic z - 2 * ∑ i, z i

theorem coneQuadratic_smul (r : ℝ) (z : ι → ℝ) :
    coneQuadratic (r • z) = r ^ 2 * coneQuadratic z := by
  simp only [coneQuadratic, Pi.smul_apply, smul_eq_mul, mul_pow, ← mul_sum]
  ring

theorem local_balance_identity (g : ℝ) (x y : ι → ℝ) :
    g * profileDefect (x + y) - (g - 1) * profileDefect y =
      profileDefect (g • x + y) - g * (g - 1) * coneQuadratic x := by
  have hxy : ∑ i, (x i + y i) ^ 2 = ∑ i, x i ^ 2 + 2 * ∑ i, x i * y i + ∑ i, y i ^ 2 := by
    simp_rw [show ∀ i, (x i + y i) ^ 2 = x i ^ 2 + 2 * (x i * y i) + y i ^ 2 by intro i; ring]
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
  have hgxy : ∑ i, (g * x i + y i) ^ 2 =
      g ^ 2 * ∑ i, x i ^ 2 + (2 * g) * ∑ i, x i * y i + ∑ i, y i ^ 2 := by
    simp_rw [show ∀ i, (g * x i + y i) ^ 2 =
      g ^ 2 * x i ^ 2 + (2 * g) * (x i * y i) + y i ^ 2 by intro i; ring]
    simp only [sum_add_distrib, ← mul_sum]
  simp only [profileDefect, coneQuadratic, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    sum_add_distrib, ← mul_sum, hxy, hgxy]
  ring

theorem local_balance_of_cone (g : ℝ) (x y : ι → ℝ)
    (hcone : coneQuadratic x = 0) (hglobal : profileDefect (g • x + y) = 0) :
    g * profileDefect (x + y) = (g - 1) * profileDefect y := by
  have hid := local_balance_identity g x y
  rw [hcone, hglobal] at hid
  linarith

/-- The identity for the actual group and reserve colour counts. -/
theorem local_balance_of_counts {k n : ℕ} (c m : Fin k → ℕ) (g t : ℕ)
    (hsum : ∑ i, c i = n)
    (hglobal : 3 * ∑ i, (c i : ℝ) ^ 2 = (n : ℝ) ^ 2 + 2 * n)
    (hcone : 3 * ∑ i, m i ^ 2 = (∑ i, m i) ^ 2) :
    let x : Fin k → ℝ := fun i => (m i : ℝ) * t
    let y : Fin k → ℝ := fun i => (c i : ℝ) - g * (m i : ℝ) * t
    (g : ℝ) * profileDefect (x + y) = ((g : ℝ) - 1) * profileDefect y := by
  intro x y
  apply local_balance_of_cone
  · have hm : coneQuadratic (fun i => (m i : ℝ)) = 0 := by
      have hc : 3 * ∑ i, (m i : ℝ) ^ 2 = (∑ i, (m i : ℝ)) ^ 2 := by exact_mod_cast hcone
      unfold coneQuadratic
      linarith
    have hx : x = (t : ℝ) • (fun i => (m i : ℝ)) := by ext i; simp [x, mul_comm]
    rw [hx, coneQuadratic_smul, hm, mul_zero]
  · have hc : (g : ℝ) • x + y = fun i => (c i : ℝ) := by ext i; simp [x, y]; ring
    rw [hc]
    have hs : ∑ i, (c i : ℝ) = n := by exact_mod_cast hsum
    simp only [profileDefect, coneQuadratic, hs]
    linarith

end CDRBicolour.KBicolor.Wilson
