module
public import RequestProject.TypedTriangle.PaschStatistics
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

/-- The completion weight is fixed by the candidate bank B. Its argument S
is exactly the set of blocks of a configuration lying outside B. -/
def completionCount (B S : Finset (Finset V)) : ℕ :=
  ((configurations (S ∪ B)).filter (fun K => K \ B = S)).card

def completionWeight (B S : Finset (Finset V)) : ℝ := completionCount B S

theorem completion_fiber_eq (B D S : Finset (Finset V)) (hSD : S ⊆ D) :
    (configurations (D ∪ B)).filter (fun K => K \ B = S) =
      (configurations (S ∪ B)).filter (fun K => K \ B = S) := by
  ext K
  simp only [mem_filter, mem_configurations]
  constructor
  · rintro ⟨⟨_, hCard, hPasch⟩, hKS⟩
    refine ⟨⟨?_, hCard, hPasch⟩, hKS⟩
    intro T hTK
    by_cases hTB : T ∈ B
    · exact mem_union_right _ hTB
    · exact mem_union_left _ (hKS ▸ mem_sdiff.mpr ⟨hTK, hTB⟩)
  · rintro ⟨⟨hKSB, hCard, hPasch⟩, hKS⟩
    refine ⟨⟨?_, hCard, hPasch⟩, hKS⟩
    exact hKSB.trans (union_subset_union hSD (subset_refl B))

/-- Exact fiber counting, before any estimates on the mixed configurations. -/
theorem count_union_eq_completion_sum (B D : Finset (Finset V)) :
    count (D ∪ B) = ∑ S ∈ D.powerset, completionCount B S := by
  have hMap : (configurations (D ∪ B) : Set (Finset (Finset V))).MapsTo
      (fun K => K \ B) D.powerset := by
    intro K hK
    apply mem_powerset.mpr
    intro T hT
    obtain ⟨hTK, hTB⟩ := mem_sdiff.mp hT
    have hTU := (mem_configurations.mp hK).1 hTK
    exact (mem_union.mp hTU).resolve_right hTB
  calc
    _ = ∑ S ∈ D.powerset, ((configurations (D ∪ B)).filter (fun K => K \ B = S)).card :=
      card_eq_sum_card_fiberwise hMap
    _ = _ := sum_congr rfl (fun S hS => congrArg Finset.card
      (completion_fiber_eq B D S (mem_powerset.mp hS)))

theorem completionWeight_nonneg (B S : Finset (Finset V)) : 0 ≤ completionWeight B S :=
  Nat.cast_nonneg _

theorem completionCount_empty (B : Finset (Finset V)) : completionCount B ∅ = count B := by
  unfold completionCount
  rw [empty_union]
  have hFilter : (configurations B).filter (fun K => K \ B = ∅) = configurations B := by
    apply filter_eq_self.mpr
    intro K hK
    exact sdiff_eq_empty_iff_subset.mpr (mem_configurations.mp hK).1
  rw [hFilter]
  rfl

theorem completionCount_nonzero_subconfiguration (B S : Finset (Finset V))
    (hS : completionCount B S ≠ 0) : ∃ K, IsPasch K ∧ S ⊆ K ∧ K \ B = S := by
  obtain ⟨K, hK⟩ := card_pos.mp (Nat.pos_of_ne_zero hS)
  obtain ⟨hConf, hKS⟩ := mem_filter.mp hK
  refine ⟨K, (mem_configurations.mp hConf).2.2, ?_, hKS⟩
  rw [← hKS]
  exact sdiff_subset

theorem completionCount_zero_of_large (B S : Finset (Finset V)) (hS : 4 < S.card) :
    completionCount B S = 0 := by
  by_contra hn
  obtain ⟨K, hK, hSK, _⟩ := completionCount_nonzero_subconfiguration B S hn
  have hh := card_le_card hSK
  rw [hK.1] at hh
  omega

theorem completionCount_four (B S : Finset (Finset V)) (hS : S.card = 4)
    (hSB : Disjoint S B) : completionCount B S = if IsPasch S then 1 else 0 := by
  have hDiff : S \ B = S := sdiff_eq_left.mpr hSB
  have hOnly : ∀ K ∈ (configurations (S ∪ B)).filter (fun K => K \ B = S), K = S := by
    intro K hK
    obtain ⟨hConf, hKS⟩ := mem_filter.mp hK
    have hSK : S ⊆ K := hKS ▸ sdiff_subset
    exact (eq_of_subset_of_card_le hSK (by rw [(mem_configurations.mp hConf).2.1, hS])).symm
  unfold completionCount
  by_cases hPasch : IsPasch S
  · rw [if_pos hPasch]
    have hFilter : (configurations (S ∪ B)).filter (fun K => K \ B = S) = {S} := by
      ext K
      constructor
      · intro hK
        exact mem_singleton.mpr (hOnly K hK)
      · intro hK
        have heq := mem_singleton.mp hK
        subst K
        exact mem_filter.mpr ⟨mem_configurations.mpr ⟨subset_union_left, hS, hPasch⟩, hDiff⟩
    rw [hFilter, card_singleton]
  · rw [if_neg hPasch]
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro K hK hKS
    have heq := hOnly K (mem_filter.mpr ⟨hK, hKS⟩)
    exact hPasch (heq ▸ (mem_configurations.mp hK).2.2)

#print axioms completion_fiber_eq
#print axioms count_union_eq_completion_sum
#print axioms completionCount_nonzero_subconfiguration
#print axioms completionCount_zero_of_large
#print axioms completionCount_empty
#print axioms completionCount_four
end TypedTriangle.Pasch
