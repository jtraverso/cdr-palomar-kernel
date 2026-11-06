module
public import RequestProject.TypedTriangle.PaschExtensionMass
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

/-- Integrating a Pasch marginal counts each configuration once for every
choice of its fixed blocks. No division by a tuple factorial is present. -/
theorem extensionMass_integrated (D : Finset (Finset V)) (μ : Finset V → ℝ) (ℓ : ℕ) :
    (∑ R ∈ D.powersetCard ℓ, extensionMass D μ R * ∏ T ∈ R, μ T) =
      (Nat.choose 4 ℓ : ℝ) * target μ D := by
  calc
    _ = ∑ K ∈ configurations D,
        ∑ R ∈ D.powersetCard ℓ, if R ⊆ K then ∏ T ∈ K, μ T else 0 := by
      simp_rw [extensionMass, sum_mul, sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro K _
      apply sum_congr rfl
      intro R _
      by_cases hRK : R ⊆ K
      · simp only [if_pos hRK]
        exact prod_sdiff hRK
      · simp only [if_neg hRK]
    _ = ∑ K ∈ configurations D, (Nat.choose 4 ℓ : ℝ) * ∏ T ∈ K, μ T := by
      apply sum_congr rfl
      intro K hK
      obtain ⟨hKD, hKcard, _⟩ := mem_configurations.mp hK
      have hfilter : (D.powersetCard ℓ).filter (fun R => R ⊆ K) = K.powersetCard ℓ := by
        ext R
        simp only [mem_filter, mem_powersetCard]
        exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hKD, h.2⟩, h.1⟩⟩
      rw [← sum_filter, hfilter, sum_const, nsmul_eq_mul, card_powersetCard, hKcard]
    _ = _ := by rw [← mul_sum, target, statistic_eq_sum]

theorem extensionMass_nonneg (D : Finset (Finset V)) (μ : Finset V → ℝ)
    (R : Finset (Finset V)) (hμ : ∀ T ∈ D, 0 ≤ μ T) : 0 ≤ extensionMass D μ R := by
  apply sum_nonneg
  intro K hK
  have hKD := (mem_configurations.mp (mem_filter.mp hK).1).1
  exact prod_nonneg (fun T hT => hμ T (hKD (mem_sdiff.mp hT).1))

#print axioms extensionMass_integrated
#print axioms extensionMass_nonneg
end TypedTriangle.Pasch
