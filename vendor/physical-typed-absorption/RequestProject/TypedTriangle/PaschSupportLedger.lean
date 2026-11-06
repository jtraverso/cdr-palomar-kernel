module
public import RequestProject.TypedTriangle.PaschWeightedHinge
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V]

theorem supportIncrementCost_self (R : Finset (Finset V)) (U : Finset V) :
    supportIncrementCost R U U = 0 := by
  unfold supportIncrementCost
  apply sum_eq_zero
  intro Q hQ
  obtain ⟨hQ, hNew⟩ := mem_filter.mp hQ
  have hSub := (mem_powersetCard.mp hQ).1
  exact (hNew (by simpa only [union_self] using hSub)).elim

/-- The previous family R is unchanged throughout the support construction.
Each new triple is charged at the first stage where all its vertices appear. -/
theorem supportIncrementCost_union (R : Finset (Finset V)) (U W1 W2 : Finset V) :
    supportIncrementCost R U (W1 ∪ W2) =
      supportIncrementCost R U W1 + supportIncrementCost R (U ∪ W1) W2 := by
  let X := ((U ∪ (W1 ∪ W2)).powersetCard 3).filter (fun Q => ¬ Q ⊆ U)
  let X1 := ((U ∪ W1).powersetCard 3).filter (fun Q => ¬ Q ⊆ U)
  let X2 := (((U ∪ W1) ∪ W2).powersetCard 3).filter (fun Q => ¬ Q ⊆ U ∪ W1)
  have hUnion : X = X1 ∪ X2 := by
    ext Q
    simp only [X, X1, X2, mem_filter, mem_powersetCard, mem_union]
    constructor
    · rintro ⟨⟨hSub, hCard⟩, hNew⟩
      by_cases hFirst : Q ⊆ U ∪ W1
      · exact Or.inl ⟨⟨hFirst, hCard⟩, hNew⟩
      · exact Or.inr ⟨⟨by simpa only [union_assoc] using hSub, hCard⟩, hFirst⟩
    · rintro (hFirst | hSecond)
      · exact ⟨⟨hFirst.1.1.trans (union_subset_union (subset_refl U) subset_union_left),
          hFirst.1.2⟩, hFirst.2⟩
      · exact ⟨⟨by simpa only [union_assoc] using hSecond.1.1, hSecond.1.2⟩,
          fun h => hSecond.2 (h.trans subset_union_left)⟩
  have hDis : Disjoint X1 X2 := by
    apply disjoint_left.mpr
    intro Q h1 h2
    exact (mem_filter.mp h2).2 (mem_powersetCard.mp (mem_filter.mp h1).1).1
  change (∑ Q ∈ X, rootedCount (insert Q R) Q) =
    (∑ Q ∈ X1, rootedCount (insert Q R) Q) + ∑ Q ∈ X2, rootedCount (insert Q R) Q
  rw [hUnion, sum_union hDis]

theorem supportIncrementCost_mono (R : Finset (Finset V)) (U : Finset V)
    {W W' : Finset V} (hW : W ⊆ W') :
    supportIncrementCost R U W ≤ supportIncrementCost R U W' := by
  apply sum_le_sum_of_subset
  intro Q hQ
  obtain ⟨hQ, hNew⟩ := mem_filter.mp hQ
  obtain ⟨hSub, hCard⟩ := mem_powersetCard.mp hQ
  exact mem_filter.mpr ⟨mem_powersetCard.mpr
    ⟨hSub.trans (union_subset_union (subset_refl U) hW), hCard⟩, hNew⟩

#print axioms supportIncrementCost_self
#print axioms supportIncrementCost_union
#print axioms supportIncrementCost_mono
end TypedTriangle.Pasch
