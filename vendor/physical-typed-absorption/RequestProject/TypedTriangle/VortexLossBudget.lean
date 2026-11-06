/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ChildNormalizedGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! The geometric loss of nested samples is paid once, by the sum of the
relative losses. This arithmetic does not assert that the samples exist. -/

open Finset

namespace TypedTriangle.Vortex

theorem relative_loss_product_bounds {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (δ : ι → ℝ)
    (hδ : ∀ i ∈ S, 0 ≤ δ i ∧ δ i ≤ 1) :
    1 - ∑ i ∈ S, δ i ≤ ∏ i ∈ S, (1 - δ i) ∧
      ∏ i ∈ S, (1 - δ i) ≤ 1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hdi := hδ i (mem_insert_self i S)
    have hrest : ∀ j ∈ S, 0 ≤ δ j ∧ δ j ≤ 1 := by
      intro j hj
      exact hδ j (mem_insert_of_mem hj)
    obtain ⟨hlo, hhi⟩ := ih hrest
    have hprod0 : 0 ≤ ∏ j ∈ S, (1 - δ j) := by
      apply Finset.prod_nonneg
      intro j hj
      linarith [(hrest j hj).2]
    have hmullo := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 1 - δ i by linarith)
    have hmulhi := mul_le_mul_of_nonneg_left (show 1 - δ i ≤ 1 by linarith) hprod0
    have hmuldelta := mul_le_mul_of_nonneg_right hhi hdi.1
    simp only [sum_insert hi, prod_insert hi]
    constructor <;> nlinarith

theorem relative_loss_at_least_half {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (δ : ι → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hδ : ∀ i ∈ S, 0 ≤ δ i ∧ δ i ≤ 1)
    (hbudget : ∑ i ∈ S, δ i ≤ 1 / 2) :
    α / 2 ≤ α * ∏ i ∈ S, (1 - δ i) := by
  have hprod := (relative_loss_product_bounds S δ hδ).1
  have hp : 1 / 2 ≤ ∏ i ∈ S, (1 - δ i) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hp hα]

/-- A relative sample retaining a `1-η` fraction of each witness family and
having size at most `1+η` times its target loses at most `(h+1)η` in its
normalized geometry constant. -/
theorem one_step_relative_geometry_loss (h : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    1 - ((h : ℝ) + 1) * η ≤ (1 - η) / (1 + η) ^ h := by
  have hp : 0 < 1 + η := by linarith
  induction h with
  | zero => simp
  | succ h ih =>
    have ih' : (1 - ((h : ℝ) + 1) * η) * (1 + η) ^ h ≤ 1 - η :=
      (le_div_iff₀ (pow_pos hp h)).mp ih
    have hcoeff :
        (1 - (((h : ℝ) + 1) + 1) * η) * (1 + η) ≤
          1 - ((h : ℝ) + 1) * η := by
      nlinarith [sq_nonneg η]
    apply (le_div_iff₀ (pow_pos hp (h + 1))).mpr
    rw [pow_succ]
    calc
      (1 - (((h + 1 : ℕ) : ℝ) + 1) * η) * ((1 + η) ^ h * (1 + η))
          = ((1 - (((h : ℝ) + 1) + 1) * η) * (1 + η)) * (1 + η) ^ h := by
              push_cast; ring
      _ ≤ (1 - ((h : ℝ) + 1) * η) * (1 + η) ^ h :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hp.le h)
      _ ≤ 1 - η := ih'

#print axioms relative_loss_product_bounds
#print axioms relative_loss_at_least_half
#print axioms one_step_relative_geometry_loss

end TypedTriangle.Vortex
