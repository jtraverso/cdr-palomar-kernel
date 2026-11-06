module
public import RequestProject.TypedTriangle.PaschLocalMixedDegrees
public import RequestProject.TypedTriangle.PaschMixedEligibility
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V] [DecidableEq V]

def localMixedDegreeScale (C : ℝ) (L : ℕ) : ℝ := mixedDegreeScale C L + 9*(L : ℝ)

/-- Partial mixed degrees are linear in the child order, with a coefficient
independent of the ambient order and the parent/child ratio. -/
theorem mixedDegree_le_local_scale_mul_child_order (A B : Finset (Finset V))
    (μ : Finset V → ℝ) (X : Finset V) (C : ℝ) (L : ℕ) (hC : 0 ≤ C)
    (hX : 0 < X.card) (hA : ∀ Q ∈ A, Q.card = 3) (hAX : ∀ Q ∈ A, Q ⊆ X)
    (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3)
    (hBX : ∀ Q ∈ B, 2 ≤ (Q ∩ X).card)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(X.card : ℝ))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ3 : ℓ ≤ 3)
    (R : Finset (Finset V)) (hRA : R ⊆ A)
    (hR1 : 1 ≤ R.card) (hRℓ : R.card ≤ ℓ) :
    mixedDegree A B μ ℓ R ≤ localMixedDegreeScale C L*(X.card : ℝ) := by
  have hX1 : (1 : ℝ) ≤ X.card := by exact_mod_cast hX
  obtain ⟨hG1,hG2,hG3,hG4,hG5⟩ := mixedDegreeScale_bounds C L hC
  have hGL : mixedDegreeScale C L ≤ localMixedDegreeScale C L := by
    unfold localMixedDegreeScale
    exact le_add_of_nonneg_right (by positivity)
  have hG0 : 0 ≤ localMixedDegreeScale C L := by linarith
  have hGn : localMixedDegreeScale C L ≤ localMixedDegreeScale C L*(X.card : ℝ) :=
    le_mul_of_one_le_right hG0 hX1
  have hNine : 9*(L : ℝ) ≤ localMixedDegreeScale C L := by
    unfold localMixedDegreeScale
    linarith
  rcases (show R.card = 1 ∨ R.card = 2 ∨ R.card = 3 by omega) with hR | hR | hR
  · obtain ⟨Q,rfl⟩ := card_eq_one.mp hR
    by_cases hQB : Q ∈ B
    · rw [mixedDegree_eq_mixedConfigurations,
        mixedConfigurations_empty_of_bank_member (mem_singleton_self Q) hQB]
      simpa only [sum_empty] using mul_nonneg hG0 (show (0 : ℝ) ≤ X.card by positivity)
    · have hQ : Q.card = 3 := hA Q (hRA (mem_singleton_self Q))
      rcases (show ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 by omega) with rfl | rfl | rfl
      · have hMul := mul_le_mul_of_nonneg_right (hG1.trans hGL)
          (show (0 : ℝ) ≤ X.card by positivity)
        exact (mixedDegree_one_root_le_on_child A B μ X C L hC hX hL hB hBX hμ0 hμb Q hQ hQB).trans
          (by nlinarith only [hMul])
      · exact (mixedDegree_two_root_le_on_child A B μ X C L hC hX hL hB hBX hμ0 hμb Q hQ hQB).trans
          ((hG2.trans hGL).trans hGn)
      · exact (mixedDegree_three_root_le_on_child A B μ X C L hC hX hL hAX hBX hμ0 hμb Q hQ hQB).trans
          ((hG3.trans hGL).trans hGn)
  · rcases (show ℓ = 2 ∨ ℓ = 3 by omega) with rfl | rfl
    · exact (mixedDegree_two_pair_le_codegree A B μ L hL R hRA hR).trans (hNine.trans hGn)
    · exact (mixedDegree_three_pair_le_on_child A B μ X C hC hX hAX hμ0 hμb R hR).trans
        ((hG4.trans hGL).trans hGn)
  · have hℓ : ℓ = 3 := by omega
    subst ℓ
    exact (mixedDegree_three_triple_le_one A B μ R hRA hR).trans
      ((show (1 : ℝ) ≤ localMixedDegreeScale C L by linarith).trans hGn)

#print axioms mixedDegree_le_local_scale_mul_child_order
end TypedTriangle.Pasch
