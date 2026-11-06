module
public import RequestProject.TypedTriangle.PaschCellModePotential
public import RequestProject.TypedTriangle.PaschSeededPotential
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

def cellUnionPolynomial (L k : ℕ) : ℕ := 9*L*k.choose 2+k.choose 3+k.choose 4

theorem cellUnionPolynomial_mono {L L' k k' : ℕ} (hL : L ≤ L') (hk : k ≤ k') :
    cellUnionPolynomial L k ≤ cellUnionPolynomial L' k' := by
  exact Nat.add_le_add (Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul_left 9 hL) (Nat.choose_le_choose 2 hk))
    (Nat.choose_le_choose 3 hk)) (Nat.choose_le_choose 4 hk)

/-- One support selection against the external union pays both increments.
Only the LOCAL old modes are required to lie in the forbidden edge set. -/
theorem cell_decompositions_with_seeded_potential
    {H : Host V I} {F : Set (Multiset I)} {A P B : Finset (Sym2 V)}
    (hA : IsAbsorber H F A P) {U0 U : Finset V} (Ub : ℕ) (hU : U.card ≤ Ub)
    (hFresh : Fresh U0 A) (hFree : HasNoAllowedTriangle H F P)
    (hInside : Inside U (A∪P)) (hAvoid : Disjoint (A∪P) B)
    (R0 R : Finset (Finset V)) (L0 : ℕ) (hR0 : PairCodegreeBound R0 L0)
    (hR : PairCodegreeBound R 2) (hRB : ∀ T ∈ R, triEdges T ⊆ B) (pay : ℝ)
    (hPhi : (supportIncrementCost (R0∪R) U0 U:ℝ) ≤ pay) :
    ∃ Doff Don, IsDecomposition H F A Doff ∧ IsDecomposition H F (A∪P) Don ∧
      PairCodegreeBound (Doff∪Don) 2 ∧ Disjoint (Doff∪Don) R ∧
      (Doff∪Don).card ≤ Ub.choose 3 ∧
      (count ((Doff∪Don)∪R):ℝ) ≤ count R+pay+(cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ) ∧
      (count ((Doff∪Don)∪(R0∪R)):ℝ) ≤ count (R0∪R)+pay+
        (cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ) := by
  have hPhiLocal : (supportIncrementCost R U0 U:ℝ) ≤ pay :=
    (show (supportIncrementCost R U0 U:ℝ) ≤ supportIncrementCost (R0∪R) U0 U by
      exact_mod_cast supportIncrementCost_mono_previous (subset_union_right : R ⊆ R0∪R) U0 U).trans hPhi
  obtain ⟨Doff, Don, hOff, hOn, hModesL, hModesR, hCard, hLocal⟩ :=
    cell_decompositions_with_potential_bound hA hFresh hFree hInside hAvoid R 2 hR hRB pay hPhiLocal
  have hCardUb : (Doff∪Don).card ≤ Ub.choose 3 :=
    hCard.trans (Nat.choose_le_choose 3 hU)
  have hN : ∀ T ∈ Doff∪Don, IsAllowed H F T ∧ triEdges T ⊆ A∪P := by
    intro T hT
    rcases mem_union.mp hT with hT | hT
    · exact ⟨hOff.1 T hT, (hOff.subset hT).trans subset_union_left⟩
    · exact ⟨hOn.1 T hT, hOn.subset hT⟩
  have hExternal := fresh_mode_count_increment_le_without_disjoint hFresh hFree hInside
    (R0∪R) (Doff∪Don) (L0+2) (hR0.union hR) hN
  have hLocalPoly : (cellUnionPolynomial 2 (Doff∪Don).card:ℝ) ≤
      (cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ) := by
    exact_mod_cast cellUnionPolynomial_mono (by omega : 2 ≤ L0+2) hCardUb
  have hExternalPoly : (cellUnionPolynomial (L0+2) (Doff∪Don).card:ℝ) ≤
      (cellUnionPolynomial (L0+2) (Ub.choose 3):ℝ) := by
    exact_mod_cast cellUnionPolynomial_mono le_rfl hCardUb
  have hExternalR : (count ((Doff∪Don)∪(R0∪R)):ℝ) ≤ (count (R0∪R):ℝ)+
      (supportIncrementCost (R0∪R) U0 U:ℝ)+(cellUnionPolynomial (L0+2) (Doff∪Don).card:ℝ) := by
    have hh : (count ((Doff∪Don)∪(R0∪R)):ℝ) ≤
        ((count (R0∪R)+supportIncrementCost (R0∪R) U0 U+
          9*(L0+2)*((Doff∪Don).card.choose 2)+(Doff∪Don).card.choose 3+(Doff∪Don).card.choose 4:ℕ):ℝ) := by
      exact_mod_cast hExternal
    simpa only [cellUnionPolynomial, Nat.cast_add, add_assoc] using hh
  refine ⟨Doff, Don, hOff, hOn, hModesL, hModesR, hCardUb, ?_, ?_⟩
  · dsimp only [cellUnionPolynomial] at hLocalPoly ⊢
    push_cast at hLocal hLocalPoly ⊢
    linarith only [hLocal, hLocalPoly]
  · linarith only [hExternalR, hPhi, hExternalPoly]

#print axioms cellUnionPolynomial_mono
#print axioms cell_decompositions_with_seeded_potential
end TypedTriangle.Pasch
