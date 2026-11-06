module
public import RequestProject.TypedTriangle.ClonedTupleFibers
public import RequestProject.TypedTriangle.PatternStatistics
public import RequestProject.PaschEGJ13.TupleDefs
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.WeightedClone
variable {E ι : Type*} [Fintype E] [Fintype ι]

private theorem powersetCard_image_injOn {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β) (C : Finset α)
    (hf : Set.InjOn f (C : Set α)) (ℓ : ℕ) :
    (C.image f).powersetCard ℓ = (C.powersetCard ℓ).image (fun A => A.image f) := by
  ext S
  constructor
  · intro hS
    obtain ⟨hSub,hCard⟩ := mem_powersetCard.mp hS
    have hPow : S ∈ (C.image f).powerset := mem_powerset.mpr hSub
    rw [powerset_image] at hPow
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hPow
    have hAC := mem_powerset.mp hA
    have hInj : Set.InjOn f (A : Set α) := hf.mono hAC
    exact mem_image.mpr ⟨A,mem_powersetCard.mpr ⟨hAC,(card_image_of_injOn hInj).symm.trans hCard⟩,rfl⟩
  · intro hS
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hS
    obtain ⟨hAC,hCard⟩ := mem_powersetCard.mp hA
    exact mem_powersetCard.mpr ⟨image_subset_image hAC,(card_image_of_injOn (hf.mono hAC)).trans hCard⟩

theorem sum_powersetCard_image {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β) (C : Finset α)
    (hf : Set.InjOn f (C : Set α)) (ℓ : ℕ) (w : Finset β → ℝ) :
    (∑ S ∈ (C.image f).powersetCard ℓ, w S) =
      ∑ A ∈ C.powersetCard ℓ, w (A.image f) := by
  rw [powersetCard_image_injOn f C hf ℓ,sum_image]
  intro A hA B hB hAB
  exact image_injOn_powerset_of_injOn hf
    (mem_powerset.mpr (mem_powersetCard.mp hA).1)
    (mem_powerset.mpr (mem_powersetCard.mp hB).1) hAB

def BaseMatching (P : ι → Finset E) (S : Finset ι) : Prop :=
  (S : Set ι).PairwiseDisjoint P

def recoverPackets (P : ι → Finset E) (m : ι → ℕ)
    (U : Finset (Finset (E ⊕ Copy m))) : Finset (Copy m) :=
  univ.filter (fun c => packet P m c ∈ U)

def tupleProjection (P : ι → Finset E) (m : ι → ℕ)
    (U : Finset (Finset (E ⊕ Copy m))) : Finset ι :=
  copyProjection m (recoverPackets P m U)

def tupleCopyWeight (P : ι → Finset E) (m : ι → ℕ)
    (w : Finset ι → ℝ) (C : Finset (Copy m)) : ℝ :=
  if NoRepeatedBase C then if BaseMatching P (copyProjection m C) then w (copyProjection m C) else 0 else 0

/-- A weight on actual finite families of packet hyperedges. It vanishes on
families outside the clone hypergraph and on every non-matching family. -/
def tupleLiftedWeight (P : ι → Finset E) (m : ι → ℕ)
    (w : Finset ι → ℝ) (U : Finset (Finset (E ⊕ Copy m))) : ℝ :=
  if U ⊆ hypergraph P m then tupleCopyWeight P m w (recoverPackets P m U) else 0

theorem recoverPackets_image (P : ι → Finset E) (m : ι → ℕ) (C : Finset (Copy m)) :
    recoverPackets P m (C.image (packet P m)) = C := by
  ext c
  simp only [recoverPackets,mem_filter,mem_univ,true_and]
  constructor
  · intro hc
    obtain ⟨d,hd,hEq⟩ := mem_image.mp hc
    exact (packet_injective P m hEq) ▸ hd
  · intro hc
    exact mem_image.mpr ⟨c,hc,rfl⟩

theorem packets_recover (P : ι → Finset E) (m : ι → ℕ)
    {U : Finset (Finset (E ⊕ Copy m))} (hU : U ⊆ hypergraph P m) :
    (recoverPackets P m U).image (packet P m) = U := by
  ext T
  constructor
  · intro hT
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hT
    exact (mem_filter.mp hc).2
  · intro hT
    obtain ⟨c,_,rfl⟩ := mem_image.mp (hU hT)
    exact mem_image.mpr ⟨c,mem_filter.mpr ⟨mem_univ _,hT⟩,rfl⟩

theorem tupleLiftedWeight_image (P : ι → Finset E) (m : ι → ℕ)
    (w : Finset ι → ℝ) (C : Finset (Copy m)) :
    tupleLiftedWeight P m w (C.image (packet P m)) = tupleCopyWeight P m w C := by
  have hSub : C.image (packet P m) ⊆ hypergraph P m := image_subset_image (subset_univ _)
  simp only [tupleLiftedWeight,if_pos hSub,recoverPackets_image]

theorem matching_packets_iff (P : ι → Finset E) (m : ι → ℕ) (C : Finset (Copy m)) :
    Pseudorandom.IsMatching (C.image (packet P m)) ↔
      (C : Set (Copy m)).PairwiseDisjoint (fun c => P c.1) := by
  constructor
  · intro h c hc d hd hcd
    apply (packet_disjoint P m hcd).mp
    exact h _ (mem_image.mpr ⟨c,hc,rfl⟩) _ (mem_image.mpr ⟨d,hd,rfl⟩)
      (fun he => hcd (packet_injective P m he))
  · intro h U hU W hW hUW
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hU
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hW
    apply (packet_disjoint P m (fun he => hUW (congrArg (packet P m) he))).mpr
    exact h hc hd (fun he => hUW (congrArg (packet P m) he))

theorem copyMatching_of_base (P : ι → Finset E) (m : ι → ℕ) {C : Finset (Copy m)}
    (hNo : NoRepeatedBase C) (hB : BaseMatching P (copyProjection m C)) :
    (C : Set (Copy m)).PairwiseDisjoint (fun c => P c.1) := by
  intro c hc d hd hcd
  exact hB (mem_image.mpr ⟨c,hc,rfl⟩) (mem_image.mpr ⟨d,hd,rfl⟩)
    (fun he => hcd (hNo hc hd he))

theorem noRepeatedBase_of_copyMatching (P : ι → Finset E) (m : ι → ℕ)
    (hP : ∀ i, (P i).Nonempty) {C : Finset (Copy m)}
    (hC : (C : Set (Copy m)).PairwiseDisjoint (fun c => P c.1)) : NoRepeatedBase C := by
  intro c hc d hd hbase
  by_contra hcd
  obtain ⟨e,he⟩ := hP c.1
  have hdE : e ∈ P d.1 := hbase ▸ he
  exact disjoint_left.mp (hC hc hd hcd) he hdE

theorem baseMatching_of_copyMatching (P : ι → Finset E) (m : ι → ℕ)
    {C : Finset (Copy m)} (hC : (C : Set (Copy m)).PairwiseDisjoint (fun c => P c.1)) :
    BaseMatching P (copyProjection m C) := by
  intro i hi j hj hij
  obtain ⟨c,hc,rfl⟩ := mem_image.mp hi
  obtain ⟨d,hd,rfl⟩ := mem_image.mp hj
  exact hC hc hd (fun he => hij (congrArg Sigma.fst he))

theorem tupleLiftedWeight_clean (P : ι → Finset E) (m : ι → ℕ)
    (w : Finset ι → ℝ) (U : Finset (Finset (E ⊕ Copy m)))
    (hU : ¬ Pseudorandom.IsMatching U) : tupleLiftedWeight P m w U = 0 := by
  unfold tupleLiftedWeight
  split_ifs with hSub
  · by_cases hNo : NoRepeatedBase (recoverPackets P m U)
    · by_cases hB : BaseMatching P (tupleProjection P m U)
      · have hM := (matching_packets_iff P m _).mpr (copyMatching_of_base P m hNo hB)
        rw [packets_recover P m hSub] at hM
        exact (hU hM).elim
      · change ¬ BaseMatching P (copyProjection m (recoverPackets P m U)) at hB
        simp only [tupleCopyWeight,if_pos hNo,if_neg hB]
    · simp only [tupleCopyWeight,if_neg hNo]
  · rfl

theorem tupleLiftedWeight_nonneg (P : ι → Finset E) (m : ι → ℕ)
    (w : Finset ι → ℝ) (hw : ∀ S, 0 ≤ w S) (U : Finset (Finset (E ⊕ Copy m))) :
    0 ≤ tupleLiftedWeight P m w U := by
  unfold tupleLiftedWeight tupleCopyWeight
  split_ifs <;> first | exact hw _ | exact le_rfl

/-- The left side is the actual EGJ tuple mass on the clone hypergraph.
The product of multiplicities is obtained by counting injective fibers. -/
theorem tweight_lift_hypergraph (P : ι → Finset E) (m : ι → ℕ)
    (w : Finset ι → ℝ) (ℓ : ℕ) :
    Pseudorandom.tweight ℓ (tupleLiftedWeight P m w) (hypergraph P m) =
      ∑ S ∈ (univ.powersetCard ℓ).filter (BaseMatching P), w S * ∏ i ∈ S, (m i : ℝ) := by
  unfold Pseudorandom.tweight hypergraph
  rw [sum_powersetCard_image (packet P m) univ (fun _ _ _ _ h => packet_injective P m h) ℓ (tupleLiftedWeight P m w)]
  simp_rw [tupleLiftedWeight_image]
  change (∑ C ∈ univ.powersetCard ℓ, if NoRepeatedBase C then
    (if BaseMatching P (copyProjection m C) then w (copyProjection m C) else 0) else 0) = _
  rw [sum_noRepeatedBase_copies m ℓ (fun S => if BaseMatching P S then w S else 0)]
  simp only [sum_filter,ite_mul,zero_mul]

/-- In a matching, nonempty base packets forbid repeated base indices, so
projection preserves the actual unweighted tuple statistic exactly. -/
theorem tweight_lift_matching (P : ι → Finset E) (m : ι → ℕ)
    (hP : ∀ i, (P i).Nonempty) (w : Finset ι → ℝ) (ℓ : ℕ)
    {M : Finset (Finset (E ⊕ Copy m))} (hM : M ⊆ hypergraph P m)
    (hMatch : Pseudorandom.IsMatching M) :
    Pseudorandom.tweight ℓ (tupleLiftedWeight P m w) M =
      PatternStatistics.statistic w ℓ (tupleProjection P m M) := by
  let C := recoverPackets P m M
  have heq : C.image (packet P m) = M := packets_recover P m hM
  obtain ⟨K,hK,hKC,_⟩ := extract_matching P m hM hMatch
  have hKCeq : K = C := by
    dsimp only [C]
    rw [hK,recoverPackets_image]
  have hC : (C : Set (Copy m)).PairwiseDisjoint (fun c => P c.1) := hKCeq ▸ hKC
  have hNo : NoRepeatedBase C := noRepeatedBase_of_copyMatching P m hP hC
  change (∑ U ∈ M.powersetCard ℓ, tupleLiftedWeight P m w U) =
    ∑ S ∈ (copyProjection m C).powersetCard ℓ, w S
  rw [← heq,sum_powersetCard_image (packet P m) C (fun _ _ _ _ h => packet_injective P m h) ℓ (tupleLiftedWeight P m w)]
  change (∑ A ∈ C.powersetCard ℓ, tupleLiftedWeight P m w (A.image (packet P m))) =
    ∑ S ∈ (C.image Sigma.fst).powersetCard ℓ, w S
  rw [sum_powersetCard_image Sigma.fst C hNo ℓ w]
  apply sum_congr rfl
  intro A hA
  rw [tupleLiftedWeight_image]
  have hAC := (mem_powersetCard.mp hA).1
  have hNoA : NoRepeatedBase A := fun c hc d hd he => hNo (hAC hc) (hAC hd) he
  have hCopyA : (A : Set (Copy m)).PairwiseDisjoint (fun c => P c.1) :=
    fun c hc d hd hcd => hC (hAC hc) (hAC hd) hcd
  simp only [tupleCopyWeight,if_pos hNoA,if_pos (baseMatching_of_copyMatching P m hCopyA)]
  rfl

#print axioms sum_powersetCard_image
#print axioms recoverPackets_image
#print axioms packets_recover
#print axioms matching_packets_iff
#print axioms noRepeatedBase_of_copyMatching
#print axioms tupleLiftedWeight_clean
#print axioms tweight_lift_hypergraph
#print axioms tweight_lift_matching
end TypedTriangle.WeightedClone
