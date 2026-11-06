module
public import RequestProject.TypedTriangle.PaschPaddedMixedWeights
public import RequestProject.TypedTriangle.PaschMixedAssembly
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem completionWeight_empty_of_card_lt_four (S : Finset (Finset V)) (hS : S.card < 4) :
    completionWeight ∅ S = 0 := by
  have hz : completionCount ∅ S = 0 := by
    by_contra hn
    obtain ⟨K, hK, _, hKS⟩ := completionCount_nonzero_subconfiguration ∅ S hn
    simp only [sdiff_empty] at hKS
    have hc := hK.1
    rw [hKS] at hc
    omega
  simp only [completionWeight, hz, Nat.cast_zero]

theorem statistic_padded_sub_baseline (A B P : Finset (Finset V))
    (μ : Finset V → ℝ) (ℓ : ℕ) (hℓ : ℓ ≤ 3) :
    PatternStatistics.statistic (paddedCompletionWeight A B μ) ℓ P -
      PatternStatistics.statistic (paddedCompletionWeight A ∅ μ) ℓ P =
        PatternStatistics.statistic (completionWeight B) ℓ P := by
  unfold PatternStatistics.statistic
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro S hS
  have hc := (mem_powersetCard.mp hS).2
  have hz := completionWeight_empty_of_card_lt_four S (by omega)
  simp only [paddedCompletionWeight, hz]
  ring

/-- Subtracting the two actual EGJ estimates controls the mixed statistic.
The baseline is the same Pasch marginal in both tests. -/
theorem mixed_statistic_error_of_padded_tests (A B P : Finset (Finset V))
    (μ : Finset V → ℝ) (ℓ : ℕ) (hℓ : ℓ ≤ 3) (ρ : ℝ)
    (hBase : |PatternStatistics.statistic (paddedCompletionWeight A ∅ μ) ℓ P -
      (Nat.choose 4 ℓ : ℝ)*target μ A| ≤ ρ*((Nat.choose 4 ℓ : ℝ)*target μ A))
    (hBank : |PatternStatistics.statistic (paddedCompletionWeight A B μ) ℓ P -
      ((Nat.choose 4 ℓ : ℝ)*target μ A + mixedMass A B μ ℓ)| ≤
        ρ*((Nat.choose 4 ℓ : ℝ)*target μ A + mixedMass A B μ ℓ)) :
    |PatternStatistics.statistic (completionWeight B) ℓ P - mixedMass A B μ ℓ| ≤
      ρ*(2*(Nat.choose 4 ℓ : ℝ)*target μ A + mixedMass A B μ ℓ) := by
  have hh := abs_add_le
    (PatternStatistics.statistic (paddedCompletionWeight A B μ) ℓ P -
      ((Nat.choose 4 ℓ : ℝ)*target μ A + mixedMass A B μ ℓ))
    (-(PatternStatistics.statistic (paddedCompletionWeight A ∅ μ) ℓ P -
      (Nat.choose 4 ℓ : ℝ)*target μ A))
  simp only [abs_neg] at hh
  rw [← sub_eq_add_neg] at hh
  have he : (PatternStatistics.statistic (paddedCompletionWeight A B μ) ℓ P -
      ((Nat.choose 4 ℓ : ℝ)*target μ A + mixedMass A B μ ℓ)) -
    (PatternStatistics.statistic (paddedCompletionWeight A ∅ μ) ℓ P -
      (Nat.choose 4 ℓ : ℝ)*target μ A) =
      PatternStatistics.statistic (completionWeight B) ℓ P - mixedMass A B μ ℓ := by
    rw [← statistic_padded_sub_baseline A B P μ ℓ hℓ]
    ring
  rw [he] at hh
  nlinarith only [hh, hBase, hBank]

theorem count_mono_of_subset {D E : Finset (Finset V)} (hDE : D ⊆ E) : count D ≤ count E := by
  apply card_le_card
  intro K hK
  obtain ⟨hKD, hCard, hPasch⟩ := mem_configurations.mp hK
  exact mem_configurations.mpr ⟨hKD.trans hDE, hCard, hPasch⟩

theorem completion_statistic_mono {D E : Finset (Finset V)} (B : Finset (Finset V))
    (ℓ : ℕ) (hDE : D ⊆ E) :
    PatternStatistics.statistic (completionWeight B) ℓ D ≤
      PatternStatistics.statistic (completionWeight B) ℓ E := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro S hS
    obtain ⟨hSD, hCard⟩ := mem_powersetCard.mp hS
    exact mem_powersetCard.mpr ⟨hSD.trans hDE, hCard⟩
  · intro S _ _
    exact completionWeight_nonneg B S

/-- The upper decomposition estimate also holds when the chosen packing
and the fixed universe overlap. No disjointness premise is introduced. -/
theorem count_union_le_mixed_statistics (B D : Finset (Finset V)) :
    (count (D ∪ B) : ℝ) ≤ (count D : ℝ) + count B +
      PatternStatistics.statistic (completionWeight B) 1 D +
      PatternStatistics.statistic (completionWeight B) 2 D +
      PatternStatistics.statistic (completionWeight B) 3 D := by
  have hEq : (D \ B) ∪ B = D ∪ B := sdiff_union_self_eq_union
  have hDis : Disjoint (D \ B) B := by
    apply disjoint_left.mpr
    intro T hT hTB
    exact (mem_sdiff.mp hT).2 hTB
  have hh := count_union_eq_mixed_statistics B (D \ B) hDis
  rw [hEq] at hh
  have hCount : (count (D \ B) : ℝ) ≤ count D := by
    exact_mod_cast (count_mono_of_subset (sdiff_subset : D \ B ⊆ D))
  have h1 := completion_statistic_mono B 1 (sdiff_subset : D \ B ⊆ D)
  have h2 := completion_statistic_mono B 2 (sdiff_subset : D \ B ⊆ D)
  have h3 := completion_statistic_mono B 3 (sdiff_subset : D \ B ⊆ D)
  linarith only [hh, hCount, h1, h2, h3]

#print axioms completionWeight_empty_of_card_lt_four
#print axioms statistic_padded_sub_baseline
#print axioms mixed_statistic_error_of_padded_tests
#print axioms count_mono_of_subset
#print axioms completion_statistic_mono
#print axioms count_union_le_mixed_statistics
end TypedTriangle.Pasch
