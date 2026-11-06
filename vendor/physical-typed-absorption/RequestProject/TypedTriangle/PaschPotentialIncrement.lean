module
public import RequestProject.TypedTriangle.PaschTwoNewCompletions
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V]

theorem completionCount_singleton_le (R : Finset (Finset V)) (T : Finset V) :
    completionCount R {T} ≤ rootedCount (insert T R) T := by
  unfold completionCount rootedCount
  simp only [singleton_union]
  apply card_le_card
  intro K hK
  obtain ⟨hConf,hDiff⟩ := mem_filter.mp hK
  exact mem_filter.mpr ⟨hConf,sdiff_subset (hDiff.symm ▸ mem_singleton_self T)⟩

/-- The one-new-block costs are the only terms needing averaging. Every
multi-new term has a uniform finite bound from pair-codegree and fourth-block
uniqueness. All old-family data stay fixed while choosing the new gadget. -/
theorem count_union_le_potential_increment {R : Finset (Finset V)} {L : ℕ}
    (hL : PairCodegreeBound R L) (New : Finset (Finset V)) (hNew : Disjoint New R) :
    count (New ∪ R) ≤ count R +
      (∑ T ∈ New, rootedCount (insert T R) T) +
      9*L*(New.card.choose 2) + New.card.choose 3 + New.card.choose 4 := by
  have hEq := count_union_eq_internal_and_mixed R New hNew
  have hOne : (∑ S ∈ New.powersetCard 1, completionCount R S) ≤
      ∑ T ∈ New, rootedCount (insert T R) T := by
    rw [powersetCard_one]
    simp only [sum_map,Function.Embedding.coeFn_mk]
    exact sum_le_sum (fun T _ => completionCount_singleton_le R T)
  have hTwo : (∑ S ∈ New.powersetCard 2, completionCount R S) ≤
      9*L*(New.card.choose 2) := by
    calc
      _ ≤ ∑ _S ∈ New.powersetCard 2, 9*L := by
        apply sum_le_sum
        intro S hS
        exact completionCount_two_le hL S (mem_powersetCard.mp hS).2
      _ = _ := by simp only [sum_const_nat,card_powersetCard]; ring
  have hThree : (∑ S ∈ New.powersetCard 3, completionCount R S) ≤ New.card.choose 3 := by
    calc
      _ ≤ ∑ _S ∈ New.powersetCard 3, 1 := by
        apply sum_le_sum
        intro S hS
        exact completionCount_three_le R S (mem_powersetCard.mp hS).2
      _ = _ := by simp only [sum_const_nat,card_powersetCard,Nat.mul_one]
  have hInternal : count New ≤ New.card.choose 4 := by
    calc
      count New ≤ (New.powersetCard 4).card := card_filter_le _ _
      _ = _ := card_powersetCard _ _
  omega

end TypedTriangle.Pasch

#print axioms TypedTriangle.Pasch.completionCount_singleton_le
#print axioms TypedTriangle.Pasch.count_union_le_potential_increment
