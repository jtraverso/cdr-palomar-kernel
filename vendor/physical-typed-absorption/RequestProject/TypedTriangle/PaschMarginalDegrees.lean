module
public import RequestProject.TypedTriangle.PaschMarginals
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

/-- Partial tuple degrees of a Pasch marginal are the original extension
degrees times the number of intermediate subsets. -/
theorem extensionMass_integrated_over_supersets (D : Finset (Finset V))
    (μ : Finset V → ℝ) (A : Finset (Finset V)) (ℓ : ℕ) (hAℓ : A.card ≤ ℓ) :
    (∑ R ∈ (D.powersetCard ℓ).filter (fun R => A ⊆ R),
      extensionMass D μ R * ∏ T ∈ R \ A, μ T) =
      (Nat.choose (4 - A.card) (ℓ - A.card) : ℝ) * extensionMass D μ A := by
  let Z := (D.powersetCard ℓ).filter (fun R => A ⊆ R)
  change (∑ R ∈ Z, _) = _
  calc
    _ = ∑ K ∈ configurations D,
        ∑ R ∈ Z, if R ⊆ K then ∏ T ∈ K \ A, μ T else 0 := by
      simp_rw [extensionMass, sum_mul, sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro K _
      apply sum_congr rfl
      intro R hR
      have hAR : A ⊆ R := (mem_filter.mp hR).2
      by_cases hRK : R ⊆ K
      · simp only [if_pos hRK]
        have hSet : (K \ A) \ (R \ A) = K \ R := by
          ext T
          simp only [mem_sdiff]
          constructor
          · rintro ⟨⟨hTK, hTA⟩, hTR⟩
            exact ⟨hTK, fun h => hTR ⟨h, hTA⟩⟩
          · rintro ⟨hTK, hTR⟩
            exact ⟨⟨hTK, fun h => hTR (hAR h)⟩, fun h => hTR h.1⟩
        have hSub : R \ A ⊆ K \ A := fun T hT =>
          mem_sdiff.mpr ⟨hRK (mem_sdiff.mp hT).1, (mem_sdiff.mp hT).2⟩
        have hp := prod_sdiff (f := μ) hSub
        rw [hSet] at hp
        exact hp
      · simp only [if_neg hRK]
    _ = ∑ K ∈ configurations D,
        if A ⊆ K then (Nat.choose (4 - A.card) (ℓ - A.card) : ℝ) *
          ∏ T ∈ K \ A, μ T else 0 := by
      apply sum_congr rfl
      intro K hK
      obtain ⟨hKD, hKcard, _⟩ := mem_configurations.mp hK
      by_cases hAK : A ⊆ K
      · rw [if_pos hAK]
        have hfilter : Z.filter (fun R => R ⊆ K) =
            (K.powersetCard ℓ).filter (fun R => A ⊆ R) := by
          ext R
          simp only [Z, mem_filter, mem_powersetCard]
          exact ⟨fun h => ⟨⟨h.2, h.1.1.2⟩, h.1.2⟩,
            fun h => ⟨⟨⟨h.1.1.trans hKD, h.1.2⟩, h.2⟩, h.1.1⟩⟩
        rw [← sum_filter, hfilter, sum_const, nsmul_eq_mul,
          card_filter_powersetCard_subset A K ℓ hAK hAℓ, hKcard]
      · rw [if_neg hAK]
        apply sum_eq_zero
        intro R hR
        apply if_neg
        intro hRK
        exact hAK ((mem_filter.mp hR).2.trans hRK)
    _ = _ := by simp only [extensionMass, sum_filter, mul_sum, mul_ite, mul_zero]

#print axioms extensionMass_integrated_over_supersets
end TypedTriangle.Pasch
