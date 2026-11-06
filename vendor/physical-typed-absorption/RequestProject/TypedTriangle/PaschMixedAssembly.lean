module
public import RequestProject.TypedTriangle.PaschMixedCompletions
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

theorem outside_card_fiber_eq_completion_sum (B D : Finset (Finset V)) (ℓ : ℕ) :
    ((configurations (D ∪ B)).filter (fun K => (K \ B).card = ℓ)).card =
      ∑ S ∈ D.powersetCard ℓ, completionCount B S := by
  let X := (configurations (D ∪ B)).filter (fun K => (K \ B).card = ℓ)
  have hMap : (X : Set (Finset (Finset V))).MapsTo (fun K => K \ B) (D.powersetCard ℓ) := by
    intro K hK
    obtain ⟨hConf, hCard⟩ := mem_filter.mp hK
    apply mem_powersetCard.mpr
    refine ⟨?_, hCard⟩
    intro T hT
    obtain ⟨hTK, hTB⟩ := mem_sdiff.mp hT
    exact (mem_union.mp ((mem_configurations.mp hConf).1 hTK)).resolve_right hTB
  calc
    _ = ∑ S ∈ D.powersetCard ℓ, (X.filter (fun K => K \ B = S)).card :=
      card_eq_sum_card_fiberwise hMap
    _ = _ := by
      apply sum_congr rfl
      intro S hS
      have hCard := (mem_powersetCard.mp hS).2
      have hFilter : X.filter (fun K => K \ B = S) =
          (configurations (D ∪ B)).filter (fun K => K \ B = S) := by
        ext K
        simp only [X, mem_filter]
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · intro h
          exact ⟨⟨h.1, h.2.symm ▸ hCard⟩, h.2⟩
      rw [hFilter, completion_fiber_eq B D S (mem_powersetCard.mp hS).1]
      rfl

/-- Exact separation into configurations wholly inside either packing and
the three possible numbers of blocks outside the fixed bank. -/
theorem count_union_eq_internal_and_mixed (B D : Finset (Finset V)) (hDB : Disjoint D B) :
    count (D ∪ B) = count D + count B +
      (∑ S ∈ D.powersetCard 1, completionCount B S) +
      (∑ S ∈ D.powersetCard 2, completionCount B S) +
      (∑ S ∈ D.powersetCard 3, completionCount B S) := by
  have hMap : (configurations (D ∪ B) : Set (Finset (Finset V))).MapsTo
      (fun K => (K \ B).card) (range 5) := by
    intro K hK
    apply mem_range.mpr
    change (K \ B).card < 5
    have hSub : K \ B ⊆ K := sdiff_subset
    have hCard := card_le_card hSub
    rw [(mem_configurations.mp hK).2.1] at hCard
    omega
  have hPartition := card_eq_sum_card_fiberwise hMap
  have hSum : count (D ∪ B) =
      ∑ ℓ ∈ range 5, ∑ S ∈ D.powersetCard ℓ, completionCount B S := by
    refine hPartition.trans (sum_congr rfl ?_)
    intro ℓ _
    exact outside_card_fiber_eq_completion_sum B D ℓ
  have hZero : (∑ S ∈ D.powersetCard 0, completionCount B S) = count B := by
    simp only [powersetCard_zero, sum_singleton, completionCount_empty]
  have hFour : (∑ S ∈ D.powersetCard 4, completionCount B S) = count D := by
    calc
      _ = ∑ S ∈ D.powersetCard 4, if IsPasch S then 1 else 0 := by
        apply sum_congr rfl
        intro S hS
        exact completionCount_four B S (mem_powersetCard.mp hS).2
          (hDB.mono_left (mem_powersetCard.mp hS).1)
      _ = _ := by simp only [count, configurations, card_eq_sum_ones, sum_filter]
  norm_num only [sum_range_succ, sum_range_zero] at hSum
  rw [hZero, hFour] at hSum
  omega

theorem count_union_eq_mixed_statistics (B D : Finset (Finset V)) (hDB : Disjoint D B) :
    (count (D ∪ B) : ℝ) = (count D : ℝ) + count B +
      PatternStatistics.statistic (completionWeight B) 1 D +
      PatternStatistics.statistic (completionWeight B) 2 D +
      PatternStatistics.statistic (completionWeight B) 3 D := by
  have hh := congrArg (fun n : ℕ => (n : ℝ)) (count_union_eq_internal_and_mixed B D hDB)
  simpa only [Nat.cast_add, Nat.cast_sum, PatternStatistics.statistic, completionWeight] using hh

#print axioms outside_card_fiber_eq_completion_sum
#print axioms count_union_eq_internal_and_mixed
#print axioms count_union_eq_mixed_statistics
end TypedTriangle.Pasch
