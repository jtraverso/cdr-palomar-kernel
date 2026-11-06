module
public import RequestProject.TypedTriangle.PaschPaddedMixedWeights
public import RequestProject.TypedTriangle.PaschFloorEligibility
public import RequestProject.TypedTriangle.PaschPackingModel
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open WeightedClone

theorem linear_gamma_sqrt_le_quadratic {G c n : ℝ}
    (hG : 0 < G) (hc : 0 < c) (hn : 0 < n) (hScale : (G/c)^2 ≤ n) :
    (G*n)*Real.sqrt n ≤ c*n^2 := by
  have hd : 0 < 2*c/G := by positivity
  have he : 4/(2*c/G)^2 = (G/c)^2 := by field_simp; ring
  have hs := sqrt_le_linear_of_order hd hn (he ▸ hScale)
  have hEq : (2*c/G)*n/2 = c*n/G := by ring
  rw [hEq] at hs
  have hh := (le_div_iff₀ hG).mp hs
  have hm := mul_le_mul_of_nonneg_right hh hn.le
  nlinarith only [hm]

variable {V : Type*} [Fintype V]

def paddedFloorWeight (A B : Finset (Finset V)) (μ : Finset V → ℝ) (n : ℝ) :=
  paddedCompletionWeight A B (floorWeights A μ n)

theorem padded_floor_actual_mass_div (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (n : ℝ) (ℓ : ℕ) :
    tupleMass (indexedPackets A) (floorCopies A μ n)
      (indexedTupleWeight A (paddedFloorWeight A B μ n)) ℓ / (n^2)^ℓ =
      (Nat.choose 4 ℓ : ℝ)*target (floorWeights A μ n) A +
        mixedMass A B (floorWeights A μ n) ℓ := by
  rw [tupleMass_general_indexed_div_of_clean A (floorCopies A μ n) (n^2)
    (paddedFloorWeight A B μ n) ℓ (fun S _ hS =>
      paddedCompletionWeight_clean A B (floorWeights A μ n) S hS)]
  exact paddedCompletionWeight_mass A B (floorWeights A μ n) ℓ

theorem padded_floor_actual_degree_div (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (n : ℝ) (ℓ : ℕ) (R : Finset A) (hR : R.card ≤ ℓ) :
    tupleExtensionMass (indexedPackets A) (floorCopies A μ n)
      (indexedTupleWeight A (paddedFloorWeight A B μ n)) ℓ R / (n^2)^(ℓ-R.card) =
      (Nat.choose (4-R.card) (ℓ-R.card) : ℝ)*
        extensionMass A (floorWeights A μ n) (indexProjection A R) +
        mixedDegree A B (floorWeights A μ n) ℓ (indexProjection A R) := by
  rw [tupleExtensionMass_general_indexed_div_of_clean A (floorCopies A μ n) (n^2)
    (paddedFloorWeight A B μ n) ℓ R (fun S _ hS =>
      paddedCompletionWeight_clean A B (floorWeights A μ n) S hS)]
  have hh := paddedCompletionWeight_degree A B (floorWeights A μ n) ℓ
    (indexProjection A R) (by simpa only [indexProjection_card] using hR)
  simpa only [indexProjection_card, paddedFloorWeight, floorWeights] using hh

/-- Eligibility is proved for the actual clone sums of the padded bank tests.
The mass premise here is the scalar Pasch lower bound, subsequently derived
from the unchanged H1 and H3, rather than an additional host assumption. -/
theorem padded_floor_tuple_eligible (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (C c : ℝ) (L : ℕ) (hC : 1 ≤ C) (hc : 0 < c)
    (hn : 0 < Fintype.card V) (hA : ∀ Q ∈ A, Q.card = 3)
    (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3)
    (hμb : ∀ T ∈ A, floorWeights A μ (Fintype.card V : ℝ) T ≤ C/(Fintype.card V : ℝ))
    (hTarget : c*(Fintype.card V : ℝ)^2 ≤
      target (floorWeights A μ (Fintype.card V : ℝ)) A)
    (hScale : ((6*C^3 + mixedDegreeScale C L)/c)^2 ≤ (Fintype.card V : ℝ))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ3 : ℓ ≤ 3)
    (R : Finset A) (hR1 : 1 ≤ R.card) (hRℓ : R.card ≤ ℓ) :
    let n := (Fintype.card V : ℝ)
    tupleExtensionMass (indexedPackets A) (floorCopies A μ n)
      (indexedTupleWeight A (paddedFloorWeight A B μ n)) ℓ R *
        (n^2)^((R.card : ℝ)+1/4) ≤
      tupleMass (indexedPackets A) (floorCopies A μ n)
        (indexedTupleWeight A (paddedFloorWeight A B μ n)) ℓ := by
  let n := (Fintype.card V : ℝ)
  let θ := floorWeights A μ n
  let G := 6*C^3 + mixedDegreeScale C L
  have hn0 : 0 < n := by dsimp [n]; exact_mod_cast hn
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hG : 0 < G := by dsimp [G, mixedDegreeScale]; positivity
  have hθ0 : ∀ T ∈ A, 0 ≤ θ T := fun T _ => floorWeights_nonneg A μ n T
  have hRA : indexProjection A R ⊆ A := indexProjection_subset A R
  have hDegree := paddedCompletionWeight_degree_le A B θ C L hC hn hA hL hB
    hθ0 hμb ℓ hℓ1 hℓ3 (indexProjection A R) hRA
    (by simpa only [indexProjection_card] using hR1)
    (by simpa only [indexProjection_card] using hRℓ)
  rw [paddedCompletionWeight_degree A B θ ℓ (indexProjection A R)
    (by simpa only [indexProjection_card] using hRℓ)] at hDegree
  simp only [indexProjection_card] at hDegree
  have hDegreeDiv := (padded_floor_actual_degree_div A B μ n ℓ R hRℓ).trans_le hDegree
  have hActualDegree := (div_le_iff₀ (pow_pos (sq_pos_of_pos hn0) (ℓ-R.card))).mp hDegreeDiv
  have hLower := paddedCompletionWeight_mass_lower A B θ ℓ hℓ1 hℓ3 hθ0 hc.le hTarget
  rw [paddedCompletionWeight_mass] at hLower
  have hMassDiv := hLower.trans_eq (padded_floor_actual_mass_div A B μ n ℓ).symm
  have hActualMass := (le_div_iff₀ (pow_pos (sq_pos_of_pos hn0) ℓ)).mp hMassDiv
  apply tuple_eligibility_of_gamma_sqrt_at_arity (gamma := G*n) (target := c*n^2) hn0 hRℓ
  · exact hActualDegree.trans_eq (mul_comm _ _)
  · exact (mul_comm _ _).le.trans hActualMass
  · exact linear_gamma_sqrt_le_quadratic hG hc hn0 hScale

#print axioms linear_gamma_sqrt_le_quadratic
#print axioms padded_floor_actual_mass_div
#print axioms padded_floor_actual_degree_div
#print axioms padded_floor_tuple_eligible
end TypedTriangle.Pasch
