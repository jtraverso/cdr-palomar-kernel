module
public import RequestProject.TypedTriangle.PaschFreshModeIncrement
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

theorem seeded_rootedCount_mono {R S : Finset (Finset V)} (hRS : R ⊆ S) (Q : Finset V) :
    rootedCount R Q ≤ rootedCount S Q := by
  apply card_le_card
  intro K hK
  obtain ⟨hK, hQ⟩ := mem_filter.mp hK
  obtain ⟨hKR, hCard, hPasch⟩ := mem_configurations.mp hK
  exact mem_filter.mpr ⟨mem_configurations.mpr ⟨hKR.trans hRS, hCard, hPasch⟩, hQ⟩

/-- Enlarging the fixed previous family can only increase the concrete support
potential. The support set and its local size bound are unchanged. -/
theorem supportIncrementCost_mono_previous {R S : Finset (Finset V)} (hRS : R ⊆ S)
    (U W : Finset V) : supportIncrementCost R U W ≤ supportIncrementCost S U W := by
  apply sum_le_sum
  intro Q _
  exact seeded_rootedCount_mono (insert_subset_insert Q hRS) Q

/-- Repeated blocks are ignored by the external union, rather than requiring
the whole external mode universe to be inserted into the forbidden edge set. -/
theorem fresh_mode_count_increment_le_without_disjoint
    {H : Host V I} {F : Set (Multiset I)} {A P : Finset (Sym2 V)} {U0 U : Finset V}
    (hFresh : Fresh U0 A) (hFree : HasNoAllowedTriangle H F P)
    (hInside : Inside U (A∪P)) (R N : Finset (Finset V)) (L : ℕ)
    (hL : PairCodegreeBound R L)
    (hN : ∀ T ∈ N, IsAllowed H F T ∧ triEdges T ⊆ A∪P) :
    count (N∪R) ≤ count R + supportIncrementCost R U0 U +
      9*L*(N.card.choose 2)+N.card.choose 3+N.card.choose 4 := by
  have hSub : N\R ⊆ N := sdiff_subset
  have hBase := fresh_mode_count_increment_le hFresh hFree hInside R (N\R) L hL
    sdiff_disjoint (fun T hT => hN T (hSub hT))
  have hUnion : (N\R)∪R = N∪R := by
    ext T
    simp only [mem_union, mem_sdiff]
    tauto
  rw [hUnion] at hBase
  have hk := card_le_card hSub
  have h2 := Nat.mul_le_mul_left (9*L) (Nat.choose_le_choose 2 hk)
  have h3 := Nat.choose_le_choose 3 hk
  have h4 := Nat.choose_le_choose 4 hk
  omega

/-- A useful stronger comparison when the new blocks really are disjoint
from the external universe. The seed's own count cancels exactly. -/
theorem fresh_configuration_increment_mono
    (N R S : Finset (Finset V)) (hRS : R ⊆ S) (hNS : Disjoint N S) :
    ((configurations (N∪R))\configurations R).card ≤
      ((configurations (N∪S))\configurations S).card := by
  apply card_le_card
  intro K hK
  obtain ⟨hKR, hNotR⟩ := mem_sdiff.mp hK
  obtain ⟨hSub, hCard, hPasch⟩ := mem_configurations.mp hKR
  have hNotSub : ¬ K ⊆ R := fun hh => hNotR (mem_configurations.mpr ⟨hh, hCard, hPasch⟩)
  obtain ⟨T, hTK, hTR⟩ := Finset.not_subset.mp hNotSub
  have hTN : T ∈ N := (mem_union.mp (hSub hTK)).resolve_right hTR
  refine mem_sdiff.mpr ⟨mem_configurations.mpr
    ⟨hSub.trans (union_subset_union (subset_refl N) hRS), hCard, hPasch⟩, ?_⟩
  intro hKS
  exact disjoint_left.mp hNS hTN ((mem_configurations.mp hKS).1 hTK)

#print axioms seeded_rootedCount_mono
#print axioms supportIncrementCost_mono_previous
#print axioms fresh_mode_count_increment_le_without_disjoint
#print axioms fresh_configuration_increment_mono
end TypedTriangle.Pasch
