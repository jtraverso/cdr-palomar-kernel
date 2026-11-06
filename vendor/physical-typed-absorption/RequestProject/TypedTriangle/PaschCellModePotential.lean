module
public import RequestProject.TypedTriangle.PaschFreshModeIncrement
public import RequestProject.TypedTriangle.PaschModeUniverse
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

/-! Choose the two actual decompositions of one cell after its support has
been selected. The support potential bounds their entire fixed union, so
later activation requires no new local mode choice. -/

theorem cell_decompositions_with_potential_bound
    {H : Host V I} {F : Set (Multiset I)} {A P B : Finset (Sym2 V)}
    (hA : IsAbsorber H F A P) {U0 U : Finset V}
    (hFresh : Fresh U0 A) (hFree : HasNoAllowedTriangle H F P)
    (hInside : Inside U (A ∪ P)) (hAvoid : Disjoint (A ∪ P) B)
    (R : Finset (Finset V)) (L : ℕ) (hL : PairCodegreeBound R L)
    (hRB : ∀ T ∈ R, triEdges T ⊆ B) (pay : ℝ)
    (hPay : (supportIncrementCost R U0 U : ℝ) ≤ pay) :
    ∃ Doff Don : Finset (Finset V),
      IsDecomposition H F A Doff ∧ IsDecomposition H F (A ∪ P) Don ∧
      PairCodegreeBound (Doff ∪ Don) 2 ∧ Disjoint (Doff ∪ Don) R ∧
      (Doff ∪ Don).card ≤ U.card.choose 3 ∧
      (count ((Doff ∪ Don) ∪ R) : ℝ) ≤ (count R : ℝ) + pay +
        (9*L*((Doff ∪ Don).card.choose 2) : ℕ) +
        ((Doff ∪ Don).card.choose 3 : ℕ) + ((Doff ∪ Don).card.choose 4 : ℕ) := by
  obtain ⟨Doff, hOff⟩ := hA.2.1
  obtain ⟨Don, hOn⟩ := hA.2.2
  have hN : ∀ T ∈ Doff ∪ Don, IsAllowed H F T ∧ triEdges T ⊆ A ∪ P := by
    intro T hT
    rcases mem_union.mp hT with hT | hT
    · refine ⟨hOff.1 T hT, ?_⟩
      have hs : triEdges T ⊆ A := by
        rw [← hOff.2.2]
        exact subset_biUnion_of_mem triEdges hT
      exact hs.trans subset_union_left
    · refine ⟨hOn.1 T hT, ?_⟩
      rw [← hOn.2.2]
      exact subset_biUnion_of_mem triEdges hT
  have hNR : Disjoint (Doff ∪ Don) R := by
    rw [disjoint_left]
    intro T hT hTR
    have hCard : (triEdges T).card = 3 := card_triEdges_three (hN T hT).1.1
    have hNonempty : (triEdges T).Nonempty := card_pos.mp (by omega)
    obtain ⟨e, he⟩ := hNonempty
    exact disjoint_left.mp hAvoid ((hN T hT).2 he) (hRB T hTR he)
  have hSub : Doff ∪ Don ⊆ U.powersetCard 3 := by
    intro T hT
    exact mem_powersetCard.mpr
      ⟨triangle_subset_of_inside_edges (hN T hT).1 (hN T hT).2 hInside, (hN T hT).1.1⟩
  have hCard : (Doff ∪ Don).card ≤ U.card.choose 3 := by
    simpa only [card_powersetCard] using card_le_card hSub
  have hCount := fresh_mode_count_increment_le hFresh hFree hInside R (Doff ∪ Don) L hL hNR hN
  have hCountR : (count ((Doff ∪ Don) ∪ R) : ℝ) ≤ (count R : ℝ) +
      (supportIncrementCost R U0 U : ℝ) + (9*L*((Doff ∪ Don).card.choose 2) : ℕ) +
      ((Doff ∪ Don).card.choose 3 : ℕ) + ((Doff ∪ Don).card.choose 4 : ℕ) := by
    exact_mod_cast hCount
  refine ⟨Doff, Don, hOff, hOn,
    pairCodegreeBound_two_modes ⟨hOff.1, hOff.2.1⟩ ⟨hOn.1, hOn.2.1⟩,
    hNR, hCard, ?_⟩
  linarith only [hCountR, hPay]

#print axioms cell_decompositions_with_potential_bound
end TypedTriangle.Pasch
