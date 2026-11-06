module
public import RequestProject.TypedTriangle.PaschMixedBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V]

/-- Activating any of the stored bank modes preserves the approximation
once the actual bank count, actual size and mixed tests have been paid.
The final family may select an arbitrary subset of the stored universe. -/
theorem bank_activation_target_error (P B D : Finset (Finset V))
    (C σ β δ ρ r targetValue : ℝ) (L : ℕ)
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hρr : ρ ≤ r) (hPD : P ⊆ D) (hDPB : D ⊆ P ∪ B)
    (hP : |(count P : ℝ)-targetValue| ≤ σ*(Fintype.card V : ℝ)^2)
    (hB : (count B : ℝ) ≤ β*(Fintype.card V : ℝ)^2)
    (hSize : (B.card : ℝ) ≤ δ*(Fintype.card V : ℝ)^2)
    (hMixed : PatternStatistics.statistic (completionWeight B) 1 P +
      PatternStatistics.statistic (completionWeight B) 2 P +
      PatternStatistics.statistic (completionWeight B) 3 P ≤
      mixedMassBudget C L*B.card +
        ρ*(7*C^3*(Fintype.card V : ℝ)^2 + mixedMassBudget C L*B.card)) :
    |(count D : ℝ)-targetValue| ≤
      (σ+β+mixedMassBudget C L*δ+r*(7*C^3+mixedMassBudget C L*δ))*
        (Fintype.card V : ℝ)^2 := by
  let M := mixedMassBudget C L
  let n := (Fintype.card V : ℝ)
  have hM : 0 ≤ M := by dsimp [M, mixedMassBudget]; positivity
  have hSizeM := mul_le_mul_of_nonneg_left hSize hM
  have hBracket : 7*C^3*n^2 + M*B.card ≤ (7*C^3+M*δ)*n^2 := by
    nlinarith only [hSizeM]
  have hBracket0 : 0 ≤ 7*C^3*n^2 + M*B.card := by positivity
  have hPay := mul_le_mul hρr hBracket hBracket0 hr
  have hMixedPaid : PatternStatistics.statistic (completionWeight B) 1 P +
      PatternStatistics.statistic (completionWeight B) 2 P +
      PatternStatistics.statistic (completionWeight B) 3 P ≤
      (M*δ+r*(7*C^3+M*δ))*n^2 := by
    nlinarith only [hMixed, hSizeM, hPay]
  have hCountP : (count P : ℝ) ≤ count D := by exact_mod_cast count_mono_of_subset hPD
  have hCountD : (count D : ℝ) ≤ count (P ∪ B) := by exact_mod_cast count_mono_of_subset hDPB
  have hUnion := count_union_le_mixed_statistics B P
  have hExtra : 0 ≤ (β+M*δ+r*(7*C^3+M*δ))*n^2 := by positivity
  obtain ⟨hLo, hHi⟩ := abs_le.mp hP
  apply abs_le.mpr
  constructor <;> nlinarith only [hCountP, hCountD, hUnion, hB, hMixedPaid, hExtra, hLo, hHi]

#print axioms bank_activation_target_error
end TypedTriangle.Pasch
