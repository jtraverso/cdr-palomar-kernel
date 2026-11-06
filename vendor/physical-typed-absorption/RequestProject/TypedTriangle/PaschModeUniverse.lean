module
public import RequestProject.TypedTriangle.PaschEdgeSelection
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V : Type*} [DecidableEq V] [Fintype V]

theorem pairCodegreeBound_of_linear {R : Finset (Finset V)}
    (hR : (R : Set (Finset V)).Pairwise (fun A B => (A ∩ B).card ≤ 1)) :
    PairCodegreeBound R 1 := by
  intro a b hab
  apply card_le_one.mpr
  intro A hA B hB
  obtain ⟨hAR,haA,hbA⟩ := mem_filter.mp hA
  obtain ⟨hBR,haB,hbB⟩ := mem_filter.mp hB
  exact eq_of_common_pair hR hAR hBR hab haA hbA haB hbB

theorem PairCodegreeBound.union {R S : Finset (Finset V)} {L K : ℕ}
    (hR : PairCodegreeBound R L) (hS : PairCodegreeBound S K) :
    PairCodegreeBound (R ∪ S) (L+K) := by
  intro a b hab
  rw [filter_union]
  exact (card_union_le _ _).trans (Nat.add_le_add (hR a b hab) (hS a b hab))

/-- Two actual fixed modes give a candidate universe with pair codegree two.
No condition on the number of possible absorptions is asserted here. -/
theorem pairCodegreeBound_two_modes {I : Type*} {H : Host V I}
    {F : Set (Multiset I)} {off on : Finset (Finset V)}
    (hOff : IsPacking H F off) (hOn : IsPacking H F on) :
    PairCodegreeBound (off ∪ on) 2 :=
  (pairCodegreeBound_of_linear (packing_linear hOff)).union
    (pairCodegreeBound_of_linear (packing_linear hOn))

theorem pairCodegreeBound_two_modes_and_packing {I : Type*} {H : Host V I}
    {F : Set (Multiset I)} {off on P : Finset (Finset V)}
    (hOff : IsPacking H F off) (hOn : IsPacking H F on) (hP : IsPacking H F P) :
    PairCodegreeBound ((off ∪ on) ∪ P) 3 :=
  (pairCodegreeBound_two_modes hOff hOn).union
    (pairCodegreeBound_of_linear (packing_linear hP))

theorem exists_low_cost_two_modes_and_packing {I : Type*} {H : Host V I}
    {F : Set (Multiset I)} {off on P : Finset (Finset V)}
    (hOff : IsPacking H F off) (hOn : IsPacking H F on) (hP : IsPacking H F P)
    (a b : V) (hab : a ≠ b) (W : Finset V) (κ : ℝ)
    (hκ : 0 < κ) (hn : 0 < (Fintype.card V:ℝ)) (hW : κ*(Fintype.card V:ℝ) ≤ W.card) :
    ∃ c ∈ W, (rootedCount (insert {a,b,c} ((off ∪ on) ∪ P)) {a,b,c}:ℝ) ≤ 27/κ := by
  have h := exists_rooted_completion_bounded
    ((off ∪ on) ∪ P) 3 (pairCodegreeBound_two_modes_and_packing hOff hOn hP) a b hab W κ hκ hn hW
  norm_num at h
  simpa only [union_assoc] using h

#print axioms pairCodegreeBound_of_linear
#print axioms PairCodegreeBound.union
#print axioms pairCodegreeBound_two_modes
#print axioms pairCodegreeBound_two_modes_and_packing
#print axioms exists_low_cost_two_modes_and_packing
end TypedTriangle.Pasch
