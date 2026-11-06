module
public import RequestProject.TypedTriangle.ClonedTupleEGJ
public import RequestProject.TypedTriangle.PaschSupersaturationEndpoint
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

def indexProjection (D : Finset (Finset V)) (R : Finset D) : Finset (Finset V) :=
  R.image Subtype.val

def indexedWeight (D : Finset (Finset V)) (R : Finset D) : ℝ :=
  if IsPasch (indexProjection D R) then 1 else 0

def indexedPackets (D : Finset (Finset V)) (i : D) : Finset (Sym2 V) := triEdges i.val

def normalizedWeights (D : Finset (Finset V)) (m : D → ℕ) (p : ℝ) (T : Finset V) : ℝ :=
  if h : T ∈ D then (m ⟨T,h⟩ : ℝ)/p else 0

theorem normalizedWeights_apply (D : Finset (Finset V)) (m : D → ℕ) (p : ℝ) (i : D) :
    normalizedWeights D m p i.val = (m i : ℝ)/p := by
  simp only [normalizedWeights,dif_pos i.property]

theorem indexProjection_univ (D : Finset (Finset V)) : indexProjection D univ = D := by
  ext T
  simp only [indexProjection,mem_image,mem_univ,true_and]
  exact ⟨fun ⟨i,hi⟩ => hi ▸ i.property,fun h => ⟨⟨T,h⟩,rfl⟩⟩

theorem indexProjection_card (D : Finset (Finset V)) (R : Finset D) :
    (indexProjection D R).card = R.card := card_image_of_injective _ Subtype.val_injective

theorem indexProjection_subset_iff (D : Finset (Finset V)) (R S : Finset D) :
    indexProjection D R ⊆ indexProjection D S ↔ R ⊆ S := image_subset_image_iff Subtype.val_injective

theorem indexProjection_sdiff (D : Finset (Finset V)) (R S : Finset D) :
    indexProjection D (R \ S) = indexProjection D R \ indexProjection D S :=
  image_sdiff R S Subtype.val_injective

theorem prod_indexProjection (D : Finset (Finset V)) (R : Finset D) (μ : Finset V → ℝ) :
    (∏ T ∈ indexProjection D R, μ T) = ∏ i ∈ R, μ i.val := by
  unfold indexProjection
  rw [prod_image]
  intro i _ j _ hij
  exact Subtype.ext hij

theorem indexedWeight_nonneg (D : Finset (Finset V)) (R : Finset D) : 0 ≤ indexedWeight D R := by
  unfold indexedWeight
  split_ifs <;> norm_num

/-- Pasch linearity makes its four edge packets pairwise disjoint. -/
theorem indexedWeight_baseMatching {D : Finset (Finset V)} {R : Finset D}
    (hR : IsPasch (indexProjection D R)) : BaseMatching (indexedPackets D) R := by
  intro i hi j hj hij
  have hi' : i.val ∈ indexProjection D R := mem_image.mpr ⟨i,hi,rfl⟩
  have hj' : j.val ∈ indexProjection D R := mem_image.mpr ⟨j,hj,rfl⟩
  have hlin := hR.2.2.2.2 hi' hj' (fun h => hij (Subtype.ext h))
  apply disjoint_left.mpr
  intro e hei hej
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨hui,hvi,huv⟩ := mem_triEdges.mp hei
    obtain ⟨huj,hvj,_⟩ := mem_triEdges.mp hej
    have hSub : ({u,v} : Finset V) ⊆ i.val ∩ j.val := by
      intro w hw
      rcases mem_insert.mp hw with rfl | hw
      · exact mem_inter.mpr ⟨hui,huj⟩
      · have hwv := mem_singleton.mp hw
        subst w
        exact mem_inter.mpr ⟨hvi,hvj⟩
    have hc := card_le_card hSub
    have hp : ({u,v} : Finset V).card = 2 := by simp [huv]
    omega

theorem indexedWeight_zero_of_not_baseMatching {D : Finset (Finset V)} {R : Finset D}
    (hR : ¬ BaseMatching (indexedPackets D) R) : indexedWeight D R = 0 := by
  unfold indexedWeight
  split_ifs with hp
  · exact (hR (indexedWeight_baseMatching hp)).elim
  · rfl

theorem indexedPackets_uniform (D : Finset (Finset V)) (hD : ∀ T ∈ D, T.card = 3) :
    ∀ i : D, (indexedPackets D i).card = 3 := by
  intro i
  exact card_triEdges_three (hD i.val i.property)

/-- Reindexing on the subtype of allowed triangles preserves the actual
unoriented fractional Pasch target. -/
theorem target_eq_indexed_sum (D : Finset (Finset V)) (μ : Finset V → ℝ) :
    target μ D = ∑ R ∈ (univ : Finset D).powersetCard 4,
      indexedWeight D R * ∏ i ∈ R, μ i.val := by
  have hs := sum_powersetCard_image (Subtype.val : D → Finset V) univ
    (fun _ _ _ _ h => Subtype.ext h) 4 (weight (fun K => ∏ T ∈ K, μ T))
  have hUniv : (univ : Finset D).image Subtype.val = D := indexProjection_univ D
  rw [hUniv] at hs
  unfold target statistic PatternStatistics.statistic
  rw [hs]
  apply sum_congr rfl
  intro R _
  change weight (fun K => ∏ T ∈ K, μ T) (indexProjection D R) =
    indexedWeight D R * ∏ i ∈ R, μ i.val
  by_cases hR : IsPasch (indexProjection D R)
  · simp only [weight,indexedWeight,if_pos hR,one_mul]
    exact prod_indexProjection D R μ
  · simp only [weight,indexedWeight,if_neg hR,zero_mul]

/-- The tuple mass in the clone theorem, divided by p^4, is the actual
Pasch target for the normalized multiplicities. -/
theorem tupleMass_indexed_div (D : Finset (Finset V)) (m : D → ℕ) (p : ℝ) :
    tupleMass (indexedPackets D) m (indexedWeight D) 4 / p^4 = target (normalizedWeights D m p) D := by
  rw [target_eq_indexed_sum]
  unfold tupleMass
  rw [sum_div,sum_filter]
  apply sum_congr rfl
  intro R hR
  have hc := (mem_powersetCard.mp hR).2
  by_cases hBM : BaseMatching (indexedPackets D) R
  · simp only [if_pos hBM]
    simp_rw [normalizedWeights_apply]
    rw [prod_div_distrib,prod_const,hc]
    ring
  · have hz := indexedWeight_zero_of_not_baseMatching hBM
    simp only [if_neg hBM,zero_div,hz,zero_mul]

#print axioms indexProjection_card
#print axioms indexedWeight_baseMatching
#print axioms indexedPackets_uniform
#print axioms target_eq_indexed_sum
#print axioms tupleMass_indexed_div
end TypedTriangle.Pasch
