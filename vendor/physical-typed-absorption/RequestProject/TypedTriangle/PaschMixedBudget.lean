module
public import RequestProject.TypedTriangle.PaschFloorMixedControl
public import RequestProject.TypedTriangle.PaschTargetUpper
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

def mixedMassBudget (C : ℝ) (L : ℕ) : ℝ :=
  27*C*(L : ℝ)^2 + 6*(L : ℝ)*C^2 + C^3

theorem floor_target_le_seed_order_square {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {C : ℝ} (hSeed : IsDiffuseSeed H F C μ)
    (hC : 0 < C) (hn : 0 < Fintype.card V) :
    target (floorWeights (allowed H F) μ (Fintype.card V : ℝ)) (allowed H F) ≤
      C^3*(Fintype.card V : ℝ)^2/4 := by
  let A := allowed H F
  let n := (Fintype.card V : ℝ)
  let θ := floorWeights A μ n
  have hn0 : 0 < n := by dsimp [n]; exact_mod_cast hn
  have hLow : ∀ T ∈ A, 1/(C*n) ≤ μ T :=
    fun T hT => (hSeed.1 T (isAllowed_of_mem_allowed hT)).1
  have hFloor : ∀ T ∈ A, θ T ≤ μ T :=
    fun T hT => (floorWeights_bounds A μ hC hn0 hLow hT).2
  have hMass : (∑ T ∈ A, θ T) ≤ n^2 :=
    (sum_le_sum hFloor).trans (LocalizedCover.seed_total_mass_cap hSeed).2
  have hh := target_le_cube_times_seed_mass A θ hC.le hn
    (fun T hT => (isAllowed_of_mem_allowed hT).1)
    (fun T _ => floorWeights_nonneg A μ n T)
    (fun T hT => (hFloor T hT).trans (hSeed.1 T (isAllowed_of_mem_allowed hT)).2)
  have hm := mul_le_mul_of_nonneg_left hMass (pow_nonneg hC.le 3)
  linarith only [hh, hm]

theorem mixed_mass_total_le (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (C : ℝ) (L : ℕ) (hC : 0 ≤ C) (hn : 0 < Fintype.card V)
    (hL : PairCodegreeBound B L) (hB : ∀ T ∈ B, T.card = 3)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T)
    (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ)) :
    mixedMass A B μ 1 + mixedMass A B μ 2 + mixedMass A B μ 3 ≤
      mixedMassBudget C L * B.card := by
  have h1 := mixedMass_one_le A B μ C L hC hn hL hB hμ0 hμb
  have h2 := mixedMass_two_le A B μ C L hC hn hL hB hμ0 hμb
  have h3 := mixedMass_three_le A B μ C hC hn hB hμ0 hμb
  unfold mixedMassBudget
  nlinarith only [h1, h2, h3]

/-- Aggregate mixed tests have quadratic error, with an explicit coefficient
of the actual bank size. No n times bank-size loss is used. -/
theorem mixed_statistics_total_le (A B P : Finset (Finset V)) (μ : Finset V → ℝ)
    (C ρ : ℝ) (L : ℕ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hn : 0 < Fintype.card V) (hL : PairCodegreeBound B L)
    (hB : ∀ T ∈ B, T.card = 3) (hμ0 : ∀ T ∈ A, 0 ≤ μ T)
    (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ))
    (hTarget : target μ A ≤ C^3*(Fintype.card V : ℝ)^2/4)
    (hErrors : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 3 →
      |PatternStatistics.statistic (completionWeight B) ℓ P - mixedMass A B μ ℓ| ≤
        ρ*(2*(Nat.choose 4 ℓ : ℝ)*target μ A + mixedMass A B μ ℓ)) :
    PatternStatistics.statistic (completionWeight B) 1 P +
      PatternStatistics.statistic (completionWeight B) 2 P +
      PatternStatistics.statistic (completionWeight B) 3 P ≤
      mixedMassBudget C L*B.card +
        ρ*(7*C^3*(Fintype.card V : ℝ)^2 + mixedMassBudget C L*B.card) := by
  have h1 := (abs_le.mp (hErrors 1 (by omega) (by omega))).2
  have h2 := (abs_le.mp (hErrors 2 (by omega) (by omega))).2
  have h3 := (abs_le.mp (hErrors 3 (by omega) (by omega))).2
  norm_num [Nat.choose] at h1 h2 h3
  have hMass := mixed_mass_total_le A B μ C L hC hn hL hB hμ0 hμb
  have hBound : 28*target μ A + mixedMass A B μ 1 + mixedMass A B μ 2 + mixedMass A B μ 3 ≤
      7*C^3*(Fintype.card V : ℝ)^2 + mixedMassBudget C L*B.card := by
    linarith only [hTarget, hMass]
  have hPay := mul_le_mul_of_nonneg_left hBound hρ
  nlinarith only [h1, h2, h3, hMass, hPay]

#print axioms floor_target_le_seed_order_square
#print axioms mixed_mass_total_le
#print axioms mixed_statistics_total_le
end TypedTriangle.Pasch
