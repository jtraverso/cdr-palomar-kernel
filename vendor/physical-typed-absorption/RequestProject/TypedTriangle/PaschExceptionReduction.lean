module
public import RequestProject.TypedTriangle.PaschAmbientChildSupport
public import RequestProject.TypedTriangle.PaschMixedCompletions
public import RequestProject.TypedTriangle.PatternStatistics
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Once two new blocks lie in the child, every old block in their
completion belongs to the actual child exception family. -/
theorem completionCount_childExceptions (P : Finset (Finset V)) (X : Finset V)
    (S : Finset (Finset V)) (hTwo : 2 ≤ S.card)
    (hInside : ∀ T ∈ S, T ⊆ X) :
    completionCount P S = completionCount (childExceptions P X) S := by
  unfold completionCount
  congr 1
  ext K
  simp only [mem_filter, mem_configurations]
  constructor
  · rintro ⟨⟨hKP, hCard, hPasch⟩, hDiff⟩
    have hSK : S ⊆ K := hDiff ▸ sdiff_subset
    have hOld : ∀ T ∈ K, T ∉ S → T ∈ childExceptions P X := by
      intro T hTK hTS
      have hTP : T ∈ P := by
        by_contra hTP
        exact hTS (hDiff ▸ mem_sdiff.mpr ⟨hTK,hTP⟩)
      exact mem_filter.mpr ⟨hTP,old_block_exceptional_of_new_family
        hPasch X S hSK hTwo hInside hTK hTS⟩
    refine ⟨⟨?_,hCard,hPasch⟩,?_⟩
    · intro T hTK
      by_cases hTS : T ∈ S
      · exact mem_union_left _ hTS
      · exact mem_union_right _ (hOld T hTK hTS)
    · ext T
      constructor
      · intro hT
        obtain ⟨hTK,hTB⟩ := mem_sdiff.mp hT
        by_contra hTS
        exact hTB (hOld T hTK hTS)
      · intro hTS
        have hTP : T ∉ P := (mem_sdiff.mp (hDiff.symm ▸ hTS)).2
        exact mem_sdiff.mpr ⟨hSK hTS,fun hTB => hTP (mem_filter.mp hTB).1⟩
  · rintro ⟨⟨hKB,hCard,hPasch⟩,hDiff⟩
    have hSK : S ⊆ K := hDiff ▸ sdiff_subset
    refine ⟨⟨?_,hCard,hPasch⟩,?_⟩
    · exact hKB.trans (union_subset_union (subset_refl S)
        (filter_subset _ _))
    · ext T
      constructor
      · intro hT
        obtain ⟨hTK,hTP⟩ := mem_sdiff.mp hT
        exact hDiff ▸ mem_sdiff.mpr ⟨hTK,fun hTB => hTP (mem_filter.mp hTB).1⟩
      · intro hTS
        have hNotB := (mem_sdiff.mp (hDiff.symm ▸ hTS)).2
        refine mem_sdiff.mpr ⟨hSK hTS,?_⟩
        intro hTP
        apply hNotB
        apply mem_filter.mpr
        refine ⟨hTP,?_⟩
        have hTri := hPasch.2.1 T (hSK hTS)
        rw [inter_eq_left.mpr (hInside T hTS),hTri]
        omega

theorem completion_statistic_childExceptions (P D : Finset (Finset V))
    (X : Finset V) (ℓ : ℕ) (hTwo : 2 ≤ ℓ)
    (hInside : ∀ T ∈ D, T ⊆ X) :
    PatternStatistics.statistic (completionWeight P) ℓ D =
      PatternStatistics.statistic (completionWeight (childExceptions P X)) ℓ D := by
  unfold PatternStatistics.statistic
  apply sum_congr rfl
  intro S hS
  obtain ⟨hSD,hCard⟩ := mem_powersetCard.mp hS
  unfold completionWeight
  rw [completionCount_childExceptions P X S (by omega)
    (fun T hT => hInside T (hSD hT))]

/-- This bound applies to a whole previous mode universe, which need not
be a packing. The exact pair codegree remains visible in the estimate. -/
theorem exception_family_card_le (B : Finset (Finset V)) (X : Finset V)
    (L : ℕ) (hL : PairCodegreeBound B L)
    (hTwo : ∀ T ∈ B, 2 ≤ (T ∩ X).card) : B.card ≤ X.card.choose 2 * L := by
  let fiber := fun Q : Finset V => B.filter (fun T => Q ⊆ T)
  have hCover : B ⊆ (X.powersetCard 2).biUnion fiber := by
    intro T hT
    obtain ⟨Q,hQ,hCard⟩ := exists_subset_card_eq (hTwo T hT)
    have hQT : Q ⊆ T := hQ.trans inter_subset_left
    have hQX : Q ⊆ X := hQ.trans inter_subset_right
    exact mem_biUnion.mpr ⟨Q,mem_powersetCard.mpr ⟨hQX,hCard⟩,
      mem_filter.mpr ⟨hT,hQT⟩⟩
  have hFiber : ∀ Q ∈ X.powersetCard 2, (fiber Q).card ≤ L := by
    intro Q hQ
    obtain ⟨a,b,hab,hEq⟩ := card_eq_two.mp (mem_powersetCard.mp hQ).2
    subst Q
    have hEq : fiber {a,b} = B.filter (fun T => a ∈ T ∧ b ∈ T) := by
      ext T
      simp [fiber,insert_subset_iff,singleton_subset_iff]
    rw [hEq]
    exact hL a b hab
  calc
    B.card ≤ ((X.powersetCard 2).biUnion fiber).card := card_le_card hCover
    _ ≤ ∑ Q ∈ X.powersetCard 2, (fiber Q).card := card_biUnion_le
    _ ≤ ∑ _Q ∈ X.powersetCard 2, L := sum_le_sum hFiber
    _ = X.card.choose 2 * L := by simp

#print axioms completionCount_childExceptions
#print axioms completion_statistic_childExceptions
#print axioms exception_family_card_le
end TypedTriangle.Pasch
