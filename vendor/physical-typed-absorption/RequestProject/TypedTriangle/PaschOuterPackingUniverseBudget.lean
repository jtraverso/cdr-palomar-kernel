module
public import RequestProject.TypedTriangle.PaschFinalAssemblyParameters
public import RequestProject.TypedTriangle.PaschBankActivationEstimate
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V]

/-- The actual full outer resource universe and the same partial packing
have a small count increment, from their count, cardinality and mixed tests.
No activation is selected in this estimate. -/
theorem outer_packing_union_count_budget
    (P B : Finset (Finset V)) (C τ ρ : ℝ) (L : ℕ)
    (hC : 0 ≤ C) (hτ : 0 < τ)
    (hCount : (count B : ℝ) ≤ outerMixedCountBudget (τ/4)*(Fintype.card V : ℝ)^2)
    (hSize : (B.card : ℝ) ≤ outerMixedSizeBudget C (τ/4) L*(Fintype.card V : ℝ)^2)
    (hRho : ρ ≤ outerMixedTestBudget C (τ/4) L)
    (hMixed : PatternStatistics.statistic (completionWeight B) 1 P+
      PatternStatistics.statistic (completionWeight B) 2 P+
      PatternStatistics.statistic (completionWeight B) 3 P ≤
      mixedMassBudget C L*B.card+
        ρ*(7*C^3*(Fintype.card V : ℝ)^2+mixedMassBudget C L*B.card)) :
    (count (P∪B) : ℝ) ≤ count P+(τ/4)*(Fintype.card V : ℝ)^2 := by
  obtain ⟨hβ,hδ,_,hr,_,hPay⟩ := outer_mixed_budgets C (τ/4) L hC (by positivity)
  have hTarget : |(count P : ℝ)-(count P : ℝ)| ≤ 0*(Fintype.card V : ℝ)^2 := by simp
  have hError := bank_activation_target_error P B (P∪B) C 0
    (outerMixedCountBudget (τ/4)) (outerMixedSizeBudget C (τ/4) L) ρ
    (outerMixedTestBudget C (τ/4) L) (count P) L hC hβ.le hδ.le hr.le hRho
    subset_union_left (by rfl) hTarget hCount hSize hMixed
  have hPaid := mul_le_mul_of_nonneg_right hPay (sq_nonneg (Fintype.card V : ℝ))
  have hUpper := (abs_le.mp hError).2
  simp only [zero_add] at hUpper
  linarith only [hUpper,hPaid]

/-- After the same stock entry and activation, the universe fits the
initial tracking budget. The final family can retain all stored modes. -/
theorem outer_final_universe_count_budget
    (P B Rnext : Finset (Finset V)) (C τ ρ u : ℝ) (L : ℕ)
    (hC : 0 ≤ C) (hτ : 0 < τ)
    (hCount : (count B : ℝ) ≤ outerMixedCountBudget (τ/4)*(Fintype.card V : ℝ)^2)
    (hSize : (B.card : ℝ) ≤ outerMixedSizeBudget C (τ/4) L*(Fintype.card V : ℝ)^2)
    (hRho : ρ ≤ outerMixedTestBudget C (τ/4) L)
    (hMixed : PatternStatistics.statistic (completionWeight B) 1 P+
      PatternStatistics.statistic (completionWeight B) 2 P+
      PatternStatistics.statistic (completionWeight B) 3 P ≤
      mixedMassBudget C L*B.card+
        ρ*(7*C^3*(Fintype.card V : ℝ)^2+mixedMassBudget C L*B.card))
    (hCover : (count Rnext : ℝ) ≤ count (P∪B)+u*(Fintype.card V : ℝ)^2*(68:ℝ)^3)
    (hu : u*(68:ℝ)^3 ≤ τ/4) :
    (count Rnext : ℝ) ≤ count P+(τ/2)*(Fintype.card V : ℝ)^2 := by
  have hBefore := outer_packing_union_count_budget P B C τ ρ L hC hτ hCount hSize hRho hMixed
  have hPaid := mul_le_mul_of_nonneg_right hu (sq_nonneg (Fintype.card V : ℝ))
  nlinarith only [hBefore,hCover,hPaid]

#print axioms outer_packing_union_count_budget
#print axioms outer_final_universe_count_budget
end TypedTriangle.Pasch
