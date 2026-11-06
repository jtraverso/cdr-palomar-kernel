module
public import RequestProject.TypedTriangle.PatternStatistics
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.PatternStatistics

/-- Sampling a subfamily cannot increase a nonnegative tuple statistic. -/
theorem statistic_mono_of_nonnegative {A : Type*} (w : Finset A → ℝ) (ℓ : ℕ)
    (D P : Finset A) (hDP : D ⊆ P) (hw : ∀ S, 0 ≤ w S) :
    statistic w ℓ D ≤ statistic w ℓ P := by
  unfold statistic
  apply sum_le_sum_of_subset_of_nonneg
  · intro S hS
    obtain ⟨hSD,hCard⟩ := mem_powersetCard.mp hS
    exact mem_powersetCard.mpr ⟨hSD.trans hDP,hCard⟩
  · intro S _ _
    exact hw S

/-- The actual upper control from the raw tuple engine passes to every
sampled subfamily. This claims no relative approximation after sampling. -/
theorem statistic_upper_on_subfamily {A : Type*} (w : Finset A → ℝ) (ℓ : ℕ)
    (D P : Finset A) (hDP : D ⊆ P) (hw : ∀ S, 0 ≤ w S)
    (mass ρ : ℝ) (hControl : |statistic w ℓ P-mass| ≤ ρ*mass) :
    statistic w ℓ D ≤ (1+ρ)*mass := by
  have hUpper := (abs_le.mp hControl).2
  exact (statistic_mono_of_nonnegative w ℓ D P hDP hw).trans (by linarith only [hUpper])

#print axioms statistic_mono_of_nonnegative
#print axioms statistic_upper_on_subfamily
end TypedTriangle.PatternStatistics
