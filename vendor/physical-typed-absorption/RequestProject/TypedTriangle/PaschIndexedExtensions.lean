module
public import RequestProject.TypedTriangle.PaschIndexedStatistics
public import RequestProject.TypedTriangle.PaschExtensionMass
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedClone
variable {V : Type*} [Fintype V]

private theorem sdiff_irrel {A : Type*} (s t : Finset A) (d : DecidableEq A) :
    @SDiff.sdiff _ (@Finset.instSDiff _ (Classical.decEq A)) s t =
      @SDiff.sdiff _ (@Finset.instSDiff _ d) s t := by
  cases Subsingleton.elim (Classical.decEq A) d
  rfl

/-- Transport a conditional fractional degree to the finite subtype of
allowed candidates, retaining the weights only on the unfixed blocks. -/
theorem extensionMass_eq_indexed_sum (D : Finset (Finset V)) (μ : Finset V → ℝ) (R : Finset D) :
    extensionMass D μ (indexProjection D R) =
      ∑ S ∈ (univ : Finset D).powersetCard 4 with R ⊆ S,
        indexedWeight D S * ∏ i ∈ S \ R, μ i.val := by
  have hForm : extensionMass D μ (indexProjection D R) =
      ∑ K ∈ D.powersetCard 4,
        if IsPasch K ∧ indexProjection D R ⊆ K then ∏ T ∈ K \ indexProjection D R, μ T else 0 := by
    simp only [extensionMass,configurations,filter_filter,sum_filter]
  have hs := sum_powersetCard_image (Subtype.val : D → Finset V) univ
    (fun _ _ _ _ h => Subtype.ext h) 4
    (fun K => if IsPasch K ∧ indexProjection D R ⊆ K then ∏ T ∈ K \ indexProjection D R, μ T else 0)
  have hUniv : (univ : Finset D).image Subtype.val = D := indexProjection_univ D
  rw [hUniv] at hs
  rw [hForm,hs,sum_filter]
  apply sum_congr rfl
  intro S _
  change (if IsPasch (indexProjection D S) ∧ indexProjection D R ⊆ indexProjection D S
    then ∏ T ∈ indexProjection D S \ indexProjection D R, μ T else 0) = _
  simp only [indexProjection_subset_iff]
  rw [← indexProjection_sdiff,prod_indexProjection]
  by_cases hP : IsPasch (indexProjection D S) <;> by_cases hRS : R ⊆ S <;>
    simp [indexedWeight,hP,hRS]

/-- Actual base conditional mass in the clone theorem, with all fixed
multiplicity factors removed. -/
theorem tupleExtensionMass_indexed_div (D : Finset (Finset V)) (m : D → ℕ) (p : ℝ) (R : Finset D) :
    tupleExtensionMass (indexedPackets D) m (indexedWeight D) 4 R / p^(4-R.card) =
      extensionMass D (normalizedWeights D m p) (indexProjection D R) := by
  rw [extensionMass_eq_indexed_sum]
  unfold tupleExtensionMass
  rw [sum_div]
  simp only [sum_filter,ite_div,zero_div]
  apply sum_congr rfl
  intro S hS
  have hc := (mem_powersetCard.mp hS).2
  by_cases hRS : R ⊆ S
  · by_cases hBM : BaseMatching (indexedPackets D) S
    · simp only [if_pos (And.intro hRS hBM),if_pos hRS]
      simp_rw [normalizedWeights_apply]
      rw [prod_div_distrib,prod_const,card_sdiff_of_subset hRS,hc]
      rw [sdiff_irrel S R inferInstance]
      ring
    · have hz := indexedWeight_zero_of_not_baseMatching hBM
      simp only [hRS,hBM,and_false,if_false,if_true,hz,zero_mul]
  · simp only [hRS,false_and,if_false]

/-- A pointwise multiplicative lower bound scales the four-block Pasch
statistic by the fourth power. Only coefficients on D are used. -/
theorem target_multiplicative_lower (D : Finset (Finset V)) (μ ψ : Finset V → ℝ) (scale : ℝ)
    (hscale : 0 ≤ scale) (hμ : ∀ T ∈ D, 0 ≤ μ T) (hψ : ∀ T ∈ D, scale*μ T ≤ ψ T) :
    scale^4 * target μ D ≤ target ψ D := by
  rw [target,statistic_eq_sum,target,statistic_eq_sum,mul_sum]
  apply sum_le_sum
  intro S hS
  have hSD := (mem_configurations.mp hS).1
  have hCard := (mem_configurations.mp hS).2.1
  have hp := prod_le_prod₀
    (fun T (hT : T ∈ S) => mul_nonneg hscale (hμ T (hSD hT)))
    (fun T (hT : T ∈ S) => hψ T (hSD hT))
  simpa only [prod_mul_distrib,prod_const,hCard] using hp

#print axioms extensionMass_eq_indexed_sum
#print axioms tupleExtensionMass_indexed_div
#print axioms target_multiplicative_lower
end TypedTriangle.Pasch
