module
public import RequestProject.TypedTriangle.PaschHostMixedEligibility
public import RequestProject.TypedTriangle.PaschPaddedMixedAssembly
public import RequestProject.TypedTriangle.PaschEnvelopeTuplePacking
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

theorem mixedMass_empty_of_arity_le_three (A : Finset (Finset V))
    (μ : Finset V → ℝ) (ℓ : ℕ) (hℓ : ℓ ≤ 3) : mixedMass A ∅ μ ℓ = 0 := by
  apply sum_eq_zero
  intro S hS
  have hc := (mem_powersetCard.mp hS).2
  rw [completionWeight_empty_of_card_lt_four S (by omega), zero_mul]

/-- Discharge the EGJ test condition using the proved original-host bounds,
then identify its actual normalized clone mass. -/
theorem padded_floor_control_estimate {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {α C : ℝ} (hH1 : IsDiffuseSeed H F C μ)
    (hH3 : CommonNbrCond H F α) (hα : 0 < α) (hC : 1 ≤ C)
    (L : ℕ) (hN : mixedEligibilityOrder α C L ≤ Fintype.card V)
    (B P : Finset (Finset V)) (hL : PairCodegreeBound B L)
    (hB : ∀ T ∈ B, T.card = 3) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ3 : ℓ ≤ 3)
    (hControl : floorTupleTestControl (allowed H F) μ P
      (paddedFloorWeight (allowed H F) B μ (Fintype.card V : ℝ)) ℓ) :
    let A := allowed H F
    let n := (Fintype.card V : ℝ)
    let θ := floorWeights A μ n
    let ρ := (n^2)^(-egj13Epsilon)
    |PatternStatistics.statistic (paddedCompletionWeight A B θ) ℓ P -
      ((Nat.choose 4 ℓ : ℝ)*target θ A + mixedMass A B θ ℓ)| ≤
      ρ*((Nat.choose 4 ℓ : ℝ)*target θ A + mixedMass A B θ ℓ) := by
  have hEligible : ∀ j, 1 ≤ j → j ≤ ℓ → ∀ R : Finset (allowed H F), R.card = j →
      WeightedClone.tupleExtensionMass (indexedPackets (allowed H F))
        (floorCopies (allowed H F) μ (Fintype.card V : ℝ))
        (indexedTupleWeight (allowed H F)
          (paddedFloorWeight (allowed H F) B μ (Fintype.card V : ℝ))) ℓ R *
          ((Fintype.card V : ℝ)^2)^((j : ℝ)+1/4) ≤
      WeightedClone.tupleMass (indexedPackets (allowed H F))
        (floorCopies (allowed H F) μ (Fintype.card V : ℝ))
        (indexedTupleWeight (allowed H F)
          (paddedFloorWeight (allowed H F) B μ (Fintype.card V : ℝ))) ℓ := by
    intro j hj hjℓ R hR
    have hh := host_floor_padded_tuple_eligible hH1 hH3 hα hC L hN B hL hB
      ℓ hℓ1 hℓ3 R (by omega) (by omega)
    simpa only [hR] using hh
  have hh := hControl hEligible
  rw [padded_floor_actual_mass_div] at hh
  exact hh

/-- Two tests on the same packing control the true mixed Pasch statistic.
Their eligibility is derived from H1 and H3, including the empty-host case. -/
theorem mixed_floor_error_of_test_controls {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {α C : ℝ} (hH1 : IsDiffuseSeed H F C μ)
    (hH3 : CommonNbrCond H F α) (hα : 0 < α) (hC : 1 ≤ C)
    (L : ℕ) (hN : mixedEligibilityOrder α C L ≤ Fintype.card V)
    (B P : Finset (Finset V)) (hL : PairCodegreeBound B L)
    (hB : ∀ T ∈ B, T.card = 3) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ3 : ℓ ≤ 3)
    (hBase : floorTupleTestControl (allowed H F) μ P
      (paddedFloorWeight (allowed H F) ∅ μ (Fintype.card V : ℝ)) ℓ)
    (hBank : floorTupleTestControl (allowed H F) μ P
      (paddedFloorWeight (allowed H F) B μ (Fintype.card V : ℝ)) ℓ) :
    let A := allowed H F
    let n := (Fintype.card V : ℝ)
    let θ := floorWeights A μ n
    |PatternStatistics.statistic (completionWeight B) ℓ P - mixedMass A B θ ℓ| ≤
      (n^2)^(-egj13Epsilon)*(2*(Nat.choose 4 ℓ : ℝ)*target θ A + mixedMass A B θ ℓ) := by
  have hEmptyL : PairCodegreeBound (∅ : Finset (Finset V)) L := by
    intro a b hab
    simp
  have hEmptyB : ∀ T ∈ (∅ : Finset (Finset V)), T.card = 3 := by simp
  have hBase' := padded_floor_control_estimate hH1 hH3 hα hC L hN ∅ P hEmptyL hEmptyB
    ℓ hℓ1 hℓ3 hBase
  dsimp only at hBase'
  rw [mixedMass_empty_of_arity_le_three _ _ ℓ hℓ3, add_zero] at hBase'
  have hBank' := padded_floor_control_estimate hH1 hH3 hα hC L hN B P hL hB
    ℓ hℓ1 hℓ3 hBank
  exact mixed_statistic_error_of_padded_tests (allowed H F) B P
    (floorWeights (allowed H F) μ (Fintype.card V : ℝ)) ℓ hℓ3
    (((Fintype.card V : ℝ)^2)^(-egj13Epsilon)) hBase' hBank'

#print axioms mixedMass_empty_of_arity_le_three
#print axioms padded_floor_control_estimate
#print axioms mixed_floor_error_of_test_controls
end TypedTriangle.Pasch
