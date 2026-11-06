module
public import RequestProject.TypedTriangle.ClonedTupleStatistics
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
variable {ι : Type*} [Fintype ι]

def copyExtensionFiber (m : ι → ℕ) (S : Finset ι) (A : Finset (Copy m)) : Finset (Finset (Copy m)) :=
  (copyFiber m S).filter (fun C => A ⊆ C)

theorem projection_union (m : ι → ℕ) (A B : Finset (Copy m)) :
    copyProjection m (A ∪ B) = copyProjection m A ∪ copyProjection m B := image_union _ _

theorem disjoint_of_disjoint_projection {m : ι → ℕ} {A B : Finset (Copy m)}
    (h : Disjoint (copyProjection m A) (copyProjection m B)) : Disjoint A B := by
  apply disjoint_left.mpr
  intro c hc hd
  exact disjoint_left.mp h (mem_image.mpr ⟨c,hc,rfl⟩) (mem_image.mpr ⟨c,hd,rfl⟩)

theorem noRepeatedBase_union {m : ι → ℕ} {A B : Finset (Copy m)}
    (hA : NoRepeatedBase A) (hB : NoRepeatedBase B)
    (hD : Disjoint (copyProjection m A) (copyProjection m B)) : NoRepeatedBase (A ∪ B) := by
  have hCross {c d : Copy m} (hc : c ∈ A) (hd : d ∈ B) (heq : c.1 = d.1) : False := by
    have hi : c.1 ∈ copyProjection m B := heq.symm ▸ mem_image.mpr ⟨d,hd,rfl⟩
    exact disjoint_left.mp hD (mem_image.mpr ⟨c,hc,rfl⟩) hi
  intro c hc d hd heq
  rcases mem_union.mp hc with hc | hc <;> rcases mem_union.mp hd with hd | hd
  · exact hA hc hd heq
  · exact (hCross hc hd heq).elim
  · exact (hCross hd hc heq.symm).elim
  · exact hB hc hd heq

theorem projection_sdiff {m : ι → ℕ} {C A : Finset (Copy m)}
    (hC : NoRepeatedBase C) (hAC : A ⊆ C) :
    copyProjection m (C \ A) = copyProjection m C \ copyProjection m A := by
  ext i
  constructor
  · intro hi
    obtain ⟨c,hc,hci⟩ := mem_image.mp hi
    obtain ⟨hcC,hcA⟩ := mem_sdiff.mp hc
    refine mem_sdiff.mpr ⟨mem_image.mpr ⟨c,hcC,hci⟩,?_⟩
    intro hiA
    obtain ⟨a,ha,hai⟩ := mem_image.mp hiA
    have heq : c = a := hC hcC (hAC ha) (hci.trans hai.symm)
    exact hcA (by simpa only [heq] using ha)
  · intro hi
    obtain ⟨hiC,hiA⟩ := mem_sdiff.mp hi
    obtain ⟨c,hc,hci⟩ := mem_image.mp hiC
    have hcA : c ∉ A := fun h => hiA (mem_image.mpr ⟨c,h,hci⟩)
    exact mem_image.mpr ⟨c,mem_sdiff.mpr ⟨hc,hcA⟩,hci⟩

theorem mem_copyExtensionFiber {m : ι → ℕ} {S : Finset ι} {A C : Finset (Copy m)} :
    C ∈ copyExtensionFiber m S A ↔ (copyProjection m C = S ∧ NoRepeatedBase C) ∧ A ⊆ C := by
  simp only [copyExtensionFiber,mem_filter,mem_copyFiber]

private theorem extension_disjoint {m : ι → ℕ} {S : Finset ι} {A D : Finset (Copy m)}
    (hD : D ∈ copyFiber m (S \ copyProjection m A)) :
    Disjoint (copyProjection m A) (copyProjection m D) := by
  apply disjoint_left.mpr
  intro i hiA hiD
  rw [(mem_copyFiber.mp hD).1] at hiD
  exact (mem_sdiff.mp hiD).2 hiA

theorem union_mem_copyExtensionFiber {m : ι → ℕ} {S : Finset ι} {A D : Finset (Copy m)}
    (hA : NoRepeatedBase A) (hAS : copyProjection m A ⊆ S)
    (hD : D ∈ copyFiber m (S \ copyProjection m A)) : A ∪ D ∈ copyExtensionFiber m S A := by
  apply mem_copyExtensionFiber.mpr
  refine ⟨⟨?_,noRepeatedBase_union hA (mem_copyFiber.mp hD).2 (extension_disjoint hD)⟩,subset_union_left⟩
  rw [projection_union,(mem_copyFiber.mp hD).1,union_sdiff_of_subset hAS]

/-- Fixing a copy on each already-used base removes its multiplicity factor. -/
theorem card_copyExtensionFiber {m : ι → ℕ} (S : Finset ι) (A : Finset (Copy m))
    (hA : NoRepeatedBase A) (hAS : copyProjection m A ⊆ S) :
    (copyExtensionFiber m S A).card = ∏ i ∈ S \ copyProjection m A, m i := by
  have hc : (copyExtensionFiber m S A).card = (copyFiber m (S \ copyProjection m A)).card := by
    symm
    apply card_bij (fun D _ => A ∪ D)
    · intro D hD
      exact union_mem_copyExtensionFiber hA hAS hD
    · intro D hD E hE hDE
      have hDdis := disjoint_of_disjoint_projection (extension_disjoint hD)
      have hEdis := disjoint_of_disjoint_projection (extension_disjoint hE)
      have hs := congrArg (fun C => C \ A) hDE
      simpa only [union_sdiff_cancel_left hDdis,union_sdiff_cancel_left hEdis] using hs
    · intro C hC
      obtain ⟨⟨hproj,hNo⟩,hAC⟩ := mem_copyExtensionFiber.mp hC
      refine ⟨C \ A,?_,union_sdiff_of_subset hAC⟩
      apply mem_copyFiber.mpr
      refine ⟨?_,fun c hc d hd he => hNo (mem_sdiff.mp hc).1 (mem_sdiff.mp hd).1 he⟩
      rw [projection_sdiff hNo hAC,hproj]
  exact hc.trans (card_copyFiber _ _)

private theorem extension_fiber_fixed_card {m : ι → ℕ} {S : Finset ι} {A : Finset (Copy m)}
    {ℓ : ℕ} (hS : S.card = ℓ) :
    (((univ.powersetCard ℓ).filter (fun C => A ⊆ C)).filter NoRepeatedBase).filter
      (fun C => copyProjection m C = S) = copyExtensionFiber m S A := by
  ext C
  simp only [mem_filter,mem_powersetCard,subset_univ,true_and,mem_copyExtensionFiber]
  constructor
  · rintro ⟨⟨⟨_,hAC⟩,hNo⟩,hproj⟩
    exact ⟨⟨hproj,hNo⟩,hAC⟩
  · rintro ⟨⟨hproj,hNo⟩,hAC⟩
    have hc := projection_card_of_noRepeatedBase hNo
    rw [hproj,hS] at hc
    exact ⟨⟨⟨hc.symm,hAC⟩,hNo⟩,hproj⟩

theorem sum_noRepeatedBase_extensions (m : ι → ℕ) (ℓ : ℕ) (A : Finset (Copy m))
    (hA : NoRepeatedBase A) (w : Finset ι → ℝ) :
    (∑ C ∈ (univ.powersetCard ℓ).filter (fun C => A ⊆ C),
      if NoRepeatedBase C then w (copyProjection m C) else 0) =
      ∑ S ∈ (univ.powersetCard ℓ).filter (fun S => copyProjection m A ⊆ S),
        w S * ∏ i ∈ S \ copyProjection m A, (m i : ℝ) := by
  let B := ((univ.powersetCard ℓ).filter (fun C => A ⊆ C)).filter (NoRepeatedBase (m:=m))
  have hmap : ∀ C ∈ B, copyProjection m C ∈
      ((univ : Finset ι).powersetCard ℓ).filter (fun S => copyProjection m A ⊆ S) := by
    intro C hC
    obtain ⟨hC,hNo⟩ := mem_filter.mp hC
    obtain ⟨hCard,hAC⟩ := mem_filter.mp hC
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,
      (projection_card_of_noRepeatedBase hNo).trans (mem_powersetCard.mp hCard).2⟩,image_subset_image hAC⟩
  rw [← sum_filter]
  change (∑ C ∈ B, w (copyProjection m C)) = _
  rw [← sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro S hS
  obtain ⟨hScard,hAS⟩ := mem_filter.mp hS
  rw [extension_fiber_fixed_card (mem_powersetCard.mp hScard).2]
  have hs : (∑ C ∈ copyExtensionFiber m S A, w (copyProjection m C)) =
      ∑ _C ∈ copyExtensionFiber m S A, w S := by
    apply sum_congr rfl
    intro C hC
    rw [(mem_copyExtensionFiber.mp hC).1.1]
  rw [hs]
  simp only [sum_const,nsmul_eq_mul,card_copyExtensionFiber S A hA hAS,Nat.cast_prod]
  ring

variable {E : Type*} [Fintype E]

theorem tupleProjection_card_of_matching (P : ι → Finset E) (m : ι → ℕ)
    (hP : ∀ i, (P i).Nonempty)
    {T : Finset (Finset (E ⊕ Copy m))} (hT : T ⊆ hypergraph P m)
    (hMatch : Pseudorandom.IsMatching T) : (tupleProjection P m T).card = T.card := by
  obtain ⟨A,hA,hCopy,_⟩ := extract_matching P m hT hMatch
  have hNo := noRepeatedBase_of_copyMatching P m hP hCopy
  have hproj : tupleProjection P m T = copyProjection m A := by
    simp only [tupleProjection,hA,recoverPackets_image]
  rw [hproj,projection_card_of_noRepeatedBase hNo,hA,
    card_image_of_injective _ (packet_injective P m)]

/-- Nonmatching fixed families have zero actual tuple degree for the clean lift. -/
theorem tdeg_lift_of_not_matching (P : ι → Finset E) (m : ι → ℕ)
    (w : Finset ι → ℝ) (ℓ : ℕ) (T : Finset (Finset (E ⊕ Copy m)))
    (hT : ¬ Pseudorandom.IsMatching T) :
    Pseudorandom.tdeg ℓ (tupleLiftedWeight P m w) (hypergraph P m) T = 0 := by
  unfold Pseudorandom.tdeg
  apply sum_eq_zero
  intro U hU
  have hTU := (mem_filter.mp hU).2
  apply tupleLiftedWeight_clean
  intro hMatch
  exact hT (fun A hA B hB hAB => hMatch A (hTU hA) B (hTU hB) hAB)

/-- This is the actual EGJ tuple degree. Fixed base indices contribute no
multiplicity factor; only the freely chosen indices in S\projection(T) do. -/
theorem tdeg_lift_hypergraph (P : ι → Finset E) (m : ι → ℕ)
    (hP : ∀ i, (P i).Nonempty) (w : Finset ι → ℝ) (ℓ : ℕ)
    {T : Finset (Finset (E ⊕ Copy m))} (hT : T ⊆ hypergraph P m)
    (hMatch : Pseudorandom.IsMatching T) :
    Pseudorandom.tdeg ℓ (tupleLiftedWeight P m w) (hypergraph P m) T =
      ∑ S ∈ (univ.powersetCard ℓ).filter (fun S => tupleProjection P m T ⊆ S ∧ BaseMatching P S),
        w S * ∏ i ∈ S \ tupleProjection P m T, (m i : ℝ) := by
  let A := recoverPackets P m T
  have hEq : A.image (packet P m) = T := packets_recover P m hT
  have hACopy : (A : Set (Copy m)).PairwiseDisjoint (fun c => P c.1) :=
    (matching_packets_iff P m A).mp (hEq.symm ▸ hMatch)
  have hNo : NoRepeatedBase A := noRepeatedBase_of_copyMatching P m hP hACopy
  unfold Pseudorandom.tdeg
  rw [sum_filter]
  unfold hypergraph
  rw [sum_powersetCard_image (packet P m) univ
    (fun _ _ _ _ h => packet_injective P m h) ℓ
    (fun U => if T ⊆ U then tupleLiftedWeight P m w U else 0)]
  have hSub (C : Finset (Copy m)) : T ⊆ C.image (packet P m) ↔ A ⊆ C := by
    rw [← hEq]
    exact image_subset_image_iff (packet_injective P m)
  simp_rw [hSub,tupleLiftedWeight_image]
  rw [← sum_filter]
  change (∑ C ∈ (univ.powersetCard ℓ).filter (fun C => A ⊆ C),
    if NoRepeatedBase C then (if BaseMatching P (copyProjection m C) then w (copyProjection m C) else 0) else 0) = _
  rw [sum_noRepeatedBase_extensions m ℓ A hNo (fun S => if BaseMatching P S then w S else 0)]
  simp only [sum_filter,ite_mul,zero_mul,tupleProjection]
  apply sum_congr rfl
  intro S _
  by_cases hAS : copyProjection m (recoverPackets P m T) ⊆ S <;>
    by_cases hBM : BaseMatching P S <;> simp [A,hAS,hBM]

#print axioms projection_union
#print axioms noRepeatedBase_union
#print axioms projection_sdiff
#print axioms card_copyExtensionFiber
#print axioms sum_noRepeatedBase_extensions
#print axioms tupleProjection_card_of_matching
#print axioms tdeg_lift_of_not_matching
#print axioms tdeg_lift_hypergraph
end TypedTriangle.WeightedClone
