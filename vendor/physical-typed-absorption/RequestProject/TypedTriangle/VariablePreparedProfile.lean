/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.VariableFirstEntry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

/-- Profile tolerance chosen *after* the smooth-inverse constant is fixed. -/
def prepTolerance (K C q : ℝ) : ℝ := q / (16 * C ^ 2 * K)

theorem prepTolerance_pos {K C q : ℝ}
    (hK : 0 < K) (hC : 0 < C) (hq : 0 < q) :
    0 < prepTolerance K C q := by
  unfold prepTolerance
  positivity

/-- The variable-radius extraction pays only prior radii. If their sum is
chosen below `prepTolerance`, deletion of the extracted set consumes at most
one sixteenth of the positive exactification budget. -/
theorem variable_entry_deletion_budget {V : Type*} [Fintype V]
    {K C q : ℝ} {b : ℕ → ℕ} {r : ℕ} {A : Finset V}
    (hK : 0 < K) (hC : 0 < C) (hq : 0 < q)
    (hn : 0 < Fintype.card V)
    (hA : A.card ≤ TypedTriangle.priorBudget b r)
    (hprior : (TypedTriangle.priorBudget b r : ℝ) ≤
      prepTolerance K C q * Fintype.card V) :
    K * ((A.card : ℝ) * C / (q * Fintype.card V)) ≤ 1 / (16 * C) := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hAR : (A.card : ℝ) ≤ prepTolerance K C q * Fintype.card V :=
    (by exact_mod_cast hA : (A.card : ℝ) ≤ TypedTriangle.priorBudget b r).trans hprior
  have hCq : 0 < q * (Fintype.card V : ℝ) := mul_pos hq hnR
  have hscale : K * ((A.card : ℝ) * C / (q * Fintype.card V)) ≤
      K * (prepTolerance K C q * Fintype.card V * C / (q * Fintype.card V)) := by
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply div_le_div_of_nonneg_right _ hCq.le
    exact mul_le_mul_of_nonneg_right hAR hC.le
  have heq : K * (prepTolerance K C q * Fintype.card V * C /
      (q * Fintype.card V)) = 1 / (16 * C) := by
    unfold prepTolerance
    field_simp
  exact hscale.trans_eq heq

/-- The raw sampled error, the variable first-entry deletion, and the smooth
inverse can be budgeted in this order, without comparing a radius to its own
preparation loss. -/
theorem variable_entry_exactification_budget {V : Type*} [Fintype V]
    {K C q ξ : ℝ} {b : ℕ → ℕ} {r : ℕ} {A : Finset V}
    (hK : 0 < K) (hC : 0 < C) (hq : 0 < q)
    (hn : 0 < Fintype.card V)
    (hA : A.card ≤ TypedTriangle.priorBudget b r)
    (hprior : (TypedTriangle.priorBudget b r : ℝ) ≤
      prepTolerance K C q * Fintype.card V)
    (hξ : K * ξ ≤ 1 / (8 * C)) :
    K * (ξ + (A.card : ℝ) * C / (q * Fintype.card V)) ≤ 1 / (4 * C) := by
  have hdel := variable_entry_deletion_budget hK hC hq hn hA hprior
  have hineq : (1 : ℝ) / (8*C) + 1 / (16*C) ≤ 1 / (4*C) := by
    have h8 : (1 : ℝ) / (8*C) = 2 / (16*C) := by field_simp <;> ring
    have h4 : (1 : ℝ) / (4*C) = 4 / (16*C) := by field_simp <;> ring
    rw [h8,h4,←add_div]
    exact div_le_div_of_nonneg_right (by norm_num : (2+1:ℝ) ≤ 4)
      (by positivity)
  rw [mul_add]
  exact (add_le_add hξ hdel).trans hineq

#print axioms prepTolerance_pos
#print axioms variable_entry_deletion_budget
#print axioms variable_entry_exactification_budget

end TypedTriangle.Vortex
