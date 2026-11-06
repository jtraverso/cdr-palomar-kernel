module
public import RequestProject.TypedTriangle.PaschFloorEligibility
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
variable {V I : Type*} [Fintype V]

theorem indexed_load_eq (D : Finset (Finset V)) (μ : Finset V → ℝ) (e : Sym2 V) :
    (∑ i : D, if e ∈ indexedPackets D i then μ i.val else 0) =
      ∑ T ∈ D.filter (fun T => e ∈ triEdges T), μ T := by
  rw [sum_filter]
  exact sum_coe_sort D (fun T => if e ∈ triEdges T then μ T else 0)

theorem indexed_load_le_of_seed {H : Host V I} {F : Set (Multiset I)} {C : ℝ}
    {μ : Finset V → ℝ} (hH1 : IsDiffuseSeed H F C μ) (e : Sym2 V) :
    (∑ i : allowed H F, if e ∈ indexedPackets (allowed H F) i then μ i.val else 0) ≤ 1 := by
  rw [indexed_load_eq]
  by_cases he : e ∈ H.G.edgeSet
  · exact le_of_eq (hH1.2 e he)
  · have hz : (allowed H F).filter (fun T => e ∈ triEdges T) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro T hT heT
      have heH := triEdges_subset_edges (isAllowed_of_mem_allowed hT) heT
      exact he (mem_filter.mp heH).2
    rw [hz,sum_empty]
    norm_num

theorem indexed_packets_linear (D : Finset (Finset V)) (hD : ∀ T ∈ D, T.card = 3)
    (e f : Sym2 V) (hef : e ≠ f) :
    (univ.filter (fun i : D => e ∈ indexedPackets D i ∧ f ∈ indexedPackets D i)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  apply Subtype.ext
  obtain ⟨hei,hfi⟩ := (mem_filter.mp hi).2
  obtain ⟨hej,hfj⟩ := (mem_filter.mp hj).2
  exact eq_of_two_edges (hD i.val i.property) (hD j.val j.property) hef hei hfi hej hfj

theorem indexed_seed_nonneg {H : Host V I} {F : Set (Multiset I)} {C : ℝ}
    {μ : Finset V → ℝ} (hH1 : IsDiffuseSeed H F C μ) (hC : 0 < C)
    (hn : 0 < Fintype.card V) (i : allowed H F) : 0 ≤ μ i.val := by
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
  exact (by positivity : (0:ℝ) ≤ 1/(C*Fintype.card V)).trans
    (hH1.1 i.val (isAllowed_of_mem_allowed i.property)).1

theorem sym2_card_le_square : Fintype.card (Sym2 V) ≤ (Fintype.card V)^2 := by
  have hh := Fintype.card_le_of_surjective (Sym2.mk (α:=V)).uncurry Sym2.mk_surjective
  simpa only [Fintype.card_prod,pow_two] using hh

theorem indexProjection_subset (D : Finset (Finset V)) (Q : Finset D) : indexProjection D Q ⊆ D := by
  intro T hT
  obtain ⟨i,_,rfl⟩ := mem_image.mp hT
  exact i.property

theorem packing_of_index_matching {H : Host V I} {F : Set (Multiset I)}
    {Q : Finset (allowed H F)} (hQ : BaseMatching (indexedPackets (allowed H F)) Q) :
    IsPacking H F (indexProjection (allowed H F) Q) := by
  refine ⟨?_,?_⟩
  · intro T hT
    exact isAllowed_of_mem_allowed (indexProjection_subset (allowed H F) Q hT)
  · intro A hA B hB hAB
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hB
    exact hQ hi hj (fun h => hAB (congrArg Subtype.val h))

theorem indexed_statistic_eq_count (D : Finset (Finset V)) (Q : Finset D) :
    PatternStatistics.statistic (indexedWeight D) 4 Q = (count (indexProjection D Q) : ℝ) := by
  have hs := sum_powersetCard_image (Subtype.val : D → Finset V) Q
    (fun _ _ _ _ h => Subtype.ext h) 4 (weight (fun _ => (1:ℝ)))
  rw [count_eq_statistic_one]
  change (∑ S ∈ Q.powersetCard 4, indexedWeight D S) =
    ∑ K ∈ (indexProjection D Q).powersetCard 4, weight (fun _ => 1) K
  simpa only [indexProjection,indexedWeight,weight] using hs.symm

#print axioms indexed_load_eq
#print axioms indexed_load_le_of_seed
#print axioms indexed_packets_linear
#print axioms indexed_seed_nonneg
#print axioms sym2_card_le_square
#print axioms packing_of_index_matching
#print axioms indexed_statistic_eq_count
end TypedTriangle.Pasch
