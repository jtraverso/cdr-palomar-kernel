module
public import RequestProject.TypedTriangle.PaschIndexedExtensions
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
open WeightedClone
variable {V : Type*} [Fintype V]

def indexedTupleWeight (D : Finset (Finset V)) (X : Finset (Finset V) → ℝ)
    (S : Finset D) : ℝ := X (indexProjection D S)

theorem indexedBaseMatching_iff (D : Finset (Finset V)) (S : Finset D) :
    BaseMatching (indexedPackets D) S ↔ BaseMatching triEdges (indexProjection D S) := by
  constructor
  · intro h A hA B hB hAB
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hA
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hB
    exact h ha hb (fun he => hAB (congrArg Subtype.val he))
  · intro h a ha b hb hab
    exact h (mem_image.mpr ⟨a,ha,rfl⟩) (mem_image.mpr ⟨b,hb,rfl⟩)
      (fun he => hab (Subtype.ext he))

/-- The actual statistic on an extracted matching is preserved by the
injective projection from allowed-candidate indices to triangles. -/
theorem statistic_indexedTupleWeight (D : Finset (Finset V))
    (X : Finset (Finset V) → ℝ) (ℓ : ℕ) (Q : Finset D) :
    PatternStatistics.statistic (indexedTupleWeight D X) ℓ Q =
      PatternStatistics.statistic X ℓ (indexProjection D Q) := by
  unfold PatternStatistics.statistic
  simpa only [indexedTupleWeight,indexProjection] using
    (sum_powersetCard_image (Subtype.val : D → Finset V) Q
      (fun _ _ _ _ he => Subtype.ext he) ℓ X).symm

/-- Exact normalized mass of the clone tuple weight. The gate is the actual
edge-packet matching condition, not an assumed clean-weight provider. -/
theorem tupleMass_general_indexed_div (D : Finset (Finset V)) (m : D → ℕ) (p : ℝ)
    (X : Finset (Finset V) → ℝ) (ℓ : ℕ) :
    tupleMass (indexedPackets D) m (indexedTupleWeight D X) ℓ/p^ℓ =
      ∑ S ∈ D.powersetCard ℓ, if BaseMatching triEdges S then
        X S*(∏ T ∈ S, normalizedWeights D m p T) else 0 := by
  have hs := sum_powersetCard_image (Subtype.val : D → Finset V) univ
    (fun _ _ _ _ he => Subtype.ext he) ℓ
    (fun S => if BaseMatching triEdges S then X S*(∏ T ∈ S, normalizedWeights D m p T) else 0)
  have hUniv : (univ : Finset D).image Subtype.val = D := indexProjection_univ D
  rw [hUniv] at hs
  rw [hs]
  unfold tupleMass
  rw [sum_div,sum_filter]
  apply sum_congr rfl
  intro S hS
  have hCard := (mem_powersetCard.mp hS).2
  change (if BaseMatching (indexedPackets D) S then (indexedTupleWeight D X S*(∏ i ∈ S, (m i:ℝ)))/p^ℓ else 0) =
    if BaseMatching triEdges (indexProjection D S) then
      X (indexProjection D S)*(∏ T ∈ indexProjection D S, normalizedWeights D m p T) else 0
  by_cases hMatch : BaseMatching (indexedPackets D) S
  · have hImage := (indexedBaseMatching_iff D S).mp hMatch
    simp only [if_pos hMatch,if_pos hImage,indexedTupleWeight,prod_indexProjection]
    simp_rw [normalizedWeights_apply]
    rw [prod_div_distrib,prod_const,hCard]
    ring
  · have hImage := mt (indexedBaseMatching_iff D S).mpr hMatch
    simp only [if_neg hMatch,if_neg hImage,zero_div]

private theorem sdiff_irrel {A : Type*} (s t : Finset A) (d : DecidableEq A) :
    @SDiff.sdiff _ (@Finset.instSDiff _ (Classical.decEq A)) s t =
      @SDiff.sdiff _ (@Finset.instSDiff _ d) s t := by
  cases Subsingleton.elim (Classical.decEq A) d
  rfl

/-- Exact conditional mass: fixed base indices contribute no multiplicity
factor. Only the ℓ-|R| unfixed clone choices remain. -/
theorem tupleExtensionMass_general_indexed_div (D : Finset (Finset V)) (m : D → ℕ) (p : ℝ)
    (X : Finset (Finset V) → ℝ) (ℓ : ℕ) (R : Finset D) :
    tupleExtensionMass (indexedPackets D) m (indexedTupleWeight D X) ℓ R/p^(ℓ-R.card) =
      ∑ S ∈ D.powersetCard ℓ with indexProjection D R ⊆ S,
        if BaseMatching triEdges S then
          X S*(∏ T ∈ S\indexProjection D R, normalizedWeights D m p T) else 0 := by
  have hs := sum_powersetCard_image (Subtype.val : D → Finset V) univ
    (fun _ _ _ _ he => Subtype.ext he) ℓ
    (fun S => if indexProjection D R ⊆ S then
      if BaseMatching triEdges S then X S*(∏ T ∈ S\indexProjection D R, normalizedWeights D m p T) else 0 else 0)
  have hUniv : (univ : Finset D).image Subtype.val = D := indexProjection_univ D
  rw [hUniv] at hs
  rw [sum_filter,hs]
  unfold tupleExtensionMass
  rw [sum_div,sum_filter]
  apply sum_congr rfl
  intro S hS
  have hCard := (mem_powersetCard.mp hS).2
  rw [sdiff_irrel S R inferInstance]
  conv_rhs =>
    change if indexProjection D R ⊆ indexProjection D S then
      if BaseMatching triEdges (indexProjection D S) then
        X (indexProjection D S)*(∏ T ∈ indexProjection D S\indexProjection D R, normalizedWeights D m p T) else 0 else 0
  simp only [indexProjection_subset_iff]
  by_cases hRS : R ⊆ S
  · by_cases hMatch : BaseMatching (indexedPackets D) S
    · have hImage := (indexedBaseMatching_iff D S).mp hMatch
      simp only [if_pos (And.intro hRS hMatch),if_pos hRS,if_pos hImage,indexedTupleWeight]
      rw [←indexProjection_sdiff,prod_indexProjection]
      simp_rw [normalizedWeights_apply]
      rw [prod_div_distrib,prod_const,card_sdiff_of_subset hRS,hCard]
      ring
    · have hImage := mt (indexedBaseMatching_iff D S).mpr hMatch
      simp only [hRS,hMatch,hImage,and_false,if_false,if_true,zero_div]
  · simp only [hRS,false_and,if_false,zero_div]

theorem tupleMass_general_indexed_div_of_clean (D : Finset (Finset V)) (m : D → ℕ) (p : ℝ)
    (X : Finset (Finset V) → ℝ) (ℓ : ℕ)
    (hClean : ∀ S ∈ D.powersetCard ℓ, ¬BaseMatching triEdges S → X S = 0) :
    tupleMass (indexedPackets D) m (indexedTupleWeight D X) ℓ/p^ℓ =
      ∑ S ∈ D.powersetCard ℓ, X S*(∏ T ∈ S, normalizedWeights D m p T) := by
  rw [tupleMass_general_indexed_div]
  apply sum_congr rfl
  intro S hS
  by_cases hMatch : BaseMatching triEdges S
  · simp only [if_pos hMatch]
  · simp only [if_neg hMatch,hClean S hS hMatch,zero_mul]

theorem tupleExtensionMass_general_indexed_div_of_clean (D : Finset (Finset V)) (m : D → ℕ) (p : ℝ)
    (X : Finset (Finset V) → ℝ) (ℓ : ℕ) (R : Finset D)
    (hClean : ∀ S ∈ D.powersetCard ℓ, ¬BaseMatching triEdges S → X S = 0) :
    tupleExtensionMass (indexedPackets D) m (indexedTupleWeight D X) ℓ R/p^(ℓ-R.card) =
      ∑ S ∈ D.powersetCard ℓ with indexProjection D R ⊆ S,
        X S*(∏ T ∈ S\indexProjection D R, normalizedWeights D m p T) := by
  rw [tupleExtensionMass_general_indexed_div]
  apply sum_congr rfl
  intro S hS
  have hS' := (mem_filter.mp hS).1
  by_cases hMatch : BaseMatching triEdges S
  · simp only [if_pos hMatch]
  · simp only [if_neg hMatch,hClean S hS' hMatch,zero_mul]

#print axioms indexedBaseMatching_iff
#print axioms statistic_indexedTupleWeight
#print axioms tupleMass_general_indexed_div
#print axioms tupleExtensionMass_general_indexed_div
#print axioms tupleMass_general_indexed_div_of_clean
#print axioms tupleExtensionMass_general_indexed_div_of_clean
end TypedTriangle.Pasch
