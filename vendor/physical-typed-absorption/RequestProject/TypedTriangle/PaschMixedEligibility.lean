module
public import RequestProject.TypedTriangle.PaschMixedBounds
public import RequestProject.TypedTriangle.PaschEGJEligibility
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch

/-- The clone eligibility calculation works at each tuple arity. -/
theorem tuple_eligibility_of_gamma_sqrt_at_arity {n gamma target degree mass : ℝ}
    {j ℓ : ℕ} (hn : 0 < n) (hj : j ≤ ℓ)
    (hDegree : degree ≤ (n^2)^(ℓ-j)*gamma)
    (hMass : (n^2)^ℓ*target ≤ mass)
    (hGamma : gamma*Real.sqrt n ≤ target) :
    degree * (n^2)^((j : ℝ)+(1/4 : ℝ)) ≤ mass := by
  have hn2 : 0 < n^2 := pow_pos hn 2
  have hFactor : (n^2)^((j : ℝ)+(1/4 : ℝ)) =
      (n^2)^j*Real.sqrt n := by
    rw [Real.rpow_add hn2, Real.rpow_natCast, square_rpow_quarter hn.le]
  calc
    degree * (n^2)^((j : ℝ)+(1/4 : ℝ)) ≤
        ((n^2)^(ℓ-j)*gamma) * (n^2)^((j : ℝ)+(1/4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hDegree (Real.rpow_nonneg hn2.le _)
    _ = (n^2)^ℓ * (gamma*Real.sqrt n) := by
      rw [hFactor]
      calc
        ((n^2)^(ℓ-j)*gamma) * ((n^2)^j*Real.sqrt n) =
            ((n^2)^(ℓ-j)*(n^2)^j)*(gamma*Real.sqrt n) := by ring
        _ = _ := by rw [← pow_add, Nat.sub_add_cancel hj]
    _ ≤ (n^2)^ℓ*target := mul_le_mul_of_nonneg_left hGamma (by positivity)
    _ ≤ mass := hMass

def mixedDegreeScale (C : ℝ) (L : ℕ) : ℝ :=
  27*(L : ℝ)^2 + 27*C*(L : ℝ)^2 + 6*(L : ℝ)*C^2 + 2*C + 3

theorem mixedDegreeScale_bounds (C : ℝ) (L : ℕ) (hC : 0 ≤ C) :
    27*(L : ℝ)^2 ≤ mixedDegreeScale C L ∧
    27*C*(L : ℝ)^2 ≤ mixedDegreeScale C L ∧
    6*(L : ℝ)*C^2 ≤ mixedDegreeScale C L ∧
    2*C ≤ mixedDegreeScale C L ∧ 3 ≤ mixedDegreeScale C L := by
  have h1 : 0 ≤ 27*(L : ℝ)^2 := by positivity
  have h2 : 0 ≤ 27*C*(L : ℝ)^2 := by positivity
  have h3 : 0 ≤ 6*(L : ℝ)*C^2 := by positivity
  unfold mixedDegreeScale
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All nonempty partial degrees of the actual mixed completion weights have
linear growth, including roots meeting the bank (whose degree is zero). -/
theorem mixedDegree_le_scale_mul_order (A B : Finset (Finset V))
    (μ : Finset V → ℝ) (C : ℝ) (L : ℕ) (hC : 0 ≤ C)
    (hn : 0 < Fintype.card V) (hA : ∀ Q ∈ A, Q.card = 3)
    (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T)
    (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ3 : ℓ ≤ 3)
    (R : Finset (Finset V)) (hRA : R ⊆ A)
    (hR1 : 1 ≤ R.card) (hRℓ : R.card ≤ ℓ) :
    mixedDegree A B μ ℓ R ≤ mixedDegreeScale C L * (Fintype.card V : ℝ) := by
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  obtain ⟨hG1, hG2, hG3, hG4, hG5⟩ := mixedDegreeScale_bounds C L hC
  have hGn : mixedDegreeScale C L ≤ mixedDegreeScale C L * (Fintype.card V : ℝ) := by
    exact le_mul_of_one_le_right (by linarith) hnR
  rcases (show R.card = 1 ∨ R.card = 2 ∨ R.card = 3 by omega) with hR | hR | hR
  · obtain ⟨Q, rfl⟩ := card_eq_one.mp hR
    by_cases hQB : Q ∈ B
    · rw [mixedDegree_eq_mixedConfigurations,
        mixedConfigurations_empty_of_bank_member (mem_singleton_self Q) hQB]
      simpa only [sum_empty] using (show (0 : ℝ) ≤ mixedDegreeScale C L *
        (Fintype.card V : ℝ) by positivity)
    · have hQ : Q.card = 3 := hA Q (hRA (mem_singleton_self Q))
      rcases (show ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 by omega) with rfl | rfl | rfl
      · exact (mixedDegree_one_root_le A B μ C L hC hn hL hB hμ0 hμb Q hQ hQB).trans
          (by nlinarith [mul_le_mul_of_nonneg_right hG1 (by positivity : (0 : ℝ) ≤ Fintype.card V)])
      · exact (mixedDegree_two_root_le A B μ C L hC hn hL hB hμ0 hμb Q hQ hQB).trans
          (hG2.trans hGn)
      · exact (mixedDegree_three_root_le A B μ C L hC hn hL hB hμ0 hμb Q hQ hQB).trans
          (hG3.trans hGn)
  · rcases (show ℓ = 2 ∨ ℓ = 3 by omega) with rfl | rfl
    · exact (mixedDegree_two_pair_le A B μ C hC hn hμ0 hμb R hR).trans
        (mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ mixedDegreeScale C L) (by positivity))
    · exact (mixedDegree_three_pair_le A B μ C hC hn hμ0 hμb R hR).trans (hG4.trans hGn)
  · have hℓ : ℓ = 3 := by omega
    subst ℓ
    exact (mixedDegree_three_triple_le A B μ C hC hn hμ0 hμb R hR).trans
      (le_trans (by linarith : (1 : ℝ) ≤ mixedDegreeScale C L) hGn)

#print axioms tuple_eligibility_of_gamma_sqrt_at_arity
#print axioms mixedDegreeScale_bounds
#print axioms mixedDegree_le_scale_mul_order
end TypedTriangle.Pasch
