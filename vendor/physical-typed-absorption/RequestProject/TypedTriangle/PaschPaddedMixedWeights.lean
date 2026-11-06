module
public import RequestProject.TypedTriangle.PaschMixedEligibility
public import RequestProject.TypedTriangle.PaschMarginalDegrees
public import RequestProject.TypedTriangle.PaschExtensionUniformBounds
public import RequestProject.TypedTriangle.ClonedTupleIndexedWeights
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch
open WeightedClone
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem IsPasch.baseMatching {K : Finset (Finset V)} (hK : IsPasch K) :
    BaseMatching triEdges K := by
  intro T hT U hU hTU
  have hlin := hK.2.2.2.2 hT hU hTU
  apply disjoint_left.mpr
  intro e heT heU
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨huT,hvT,huv⟩ := mem_triEdges.mp heT
    obtain ⟨huU,hvU,_⟩ := mem_triEdges.mp heU
    have hSub : ({u,v} : Finset V) ⊆ T ∩ U := by
      intro w hw
      rcases mem_insert.mp hw with rfl | hw
      · exact mem_inter.mpr ⟨huT,huU⟩
      · have hwv := mem_singleton.mp hw
        subst w
        exact mem_inter.mpr ⟨hvT,hvU⟩
    have hc := card_le_card hSub
    have hp : ({u,v} : Finset V).card = 2 := by simp [huv]
    omega

theorem extensionMass_zero_of_not_matching (A : Finset (Finset V))
    (μ : Finset V → ℝ) (S : Finset (Finset V)) (hS : ¬ BaseMatching triEdges S) :
    extensionMass A μ S = 0 := by
  apply sum_eq_zero
  intro K hK
  obtain ⟨hK, hSK⟩ := mem_filter.mp hK
  have hMatch := (mem_configurations.mp hK).2.2.baseMatching
  exact (hS (fun _ hT _ hU hTU => hMatch (hSK hT) (hSK hU) hTU)).elim

theorem completionWeight_zero_of_not_matching (B S : Finset (Finset V))
    (hS : ¬ BaseMatching triEdges S) : completionWeight B S = 0 := by
  have hz : completionCount B S = 0 := by
    by_contra hn
    obtain ⟨K, hK, hSK, _⟩ := completionCount_nonzero_subconfiguration B S hn
    have hMatch := hK.baseMatching
    exact hS (fun _ hT _ hU hTU => hMatch (hSK hT) (hSK hU) hTU)
  simp only [completionWeight, hz, Nat.cast_zero]

def paddedCompletionWeight (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (S : Finset (Finset V)) : ℝ := extensionMass A μ S + completionWeight B S

theorem paddedCompletionWeight_nonneg (A B : Finset (Finset V))
    (μ : Finset V → ℝ) (hμ : ∀ T ∈ A, 0 ≤ μ T) (S : Finset (Finset V)) :
    0 ≤ paddedCompletionWeight A B μ S :=
  add_nonneg (extensionMass_nonneg A μ S hμ) (completionWeight_nonneg B S)

theorem paddedCompletionWeight_clean (A B : Finset (Finset V))
    (μ : Finset V → ℝ) (S : Finset (Finset V)) (hS : ¬ BaseMatching triEdges S) :
    paddedCompletionWeight A B μ S = 0 := by
  simp only [paddedCompletionWeight, extensionMass_zero_of_not_matching A μ S hS,
    completionWeight_zero_of_not_matching B S hS, zero_add]

theorem paddedCompletionWeight_mass (A B : Finset (Finset V))
    (μ : Finset V → ℝ) (ℓ : ℕ) :
    (∑ S ∈ A.powersetCard ℓ, paddedCompletionWeight A B μ S * ∏ T ∈ S, μ T) =
      (Nat.choose 4 ℓ : ℝ)*target μ A + mixedMass A B μ ℓ := by
  simp only [paddedCompletionWeight, add_mul, sum_add_distrib]
  rw [extensionMass_integrated]
  rfl

theorem paddedCompletionWeight_degree (A B : Finset (Finset V))
    (μ : Finset V → ℝ) (ℓ : ℕ) (R : Finset (Finset V)) (hR : R.card ≤ ℓ) :
    (∑ S ∈ (A.powersetCard ℓ).filter (fun S => R ⊆ S),
      paddedCompletionWeight A B μ S * ∏ T ∈ S \ R, μ T) =
      (Nat.choose (4-R.card) (ℓ-R.card) : ℝ)*extensionMass A μ R + mixedDegree A B μ ℓ R := by
  simp only [paddedCompletionWeight, add_mul, sum_add_distrib]
  rw [extensionMass_integrated_over_supersets A μ R ℓ hR]
  rfl

theorem mixedMass_nonneg (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (ℓ : ℕ) (hμ : ∀ T ∈ A, 0 ≤ μ T) : 0 ≤ mixedMass A B μ ℓ := by
  apply sum_nonneg
  intro S hS
  exact mul_nonneg (completionWeight_nonneg B S)
    (prod_nonneg (fun T hT => hμ T ((mem_powersetCard.mp hS).1 hT)))

/-- Padding contributes the already established Pasch mass at every mixed
arity, so eligibility does not require a lower bound on the bank contribution. -/
theorem paddedCompletionWeight_mass_lower (A B : Finset (Finset V))
    (μ : Finset V → ℝ) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ3 : ℓ ≤ 3)
    (hμ : ∀ T ∈ A, 0 ≤ μ T) {c n : ℝ} (hc : 0 ≤ c)
    (hTarget : c*n^2 ≤ target μ A) :
    c*n^2 ≤ ∑ S ∈ A.powersetCard ℓ, paddedCompletionWeight A B μ S * ∏ T ∈ S, μ T := by
  rw [paddedCompletionWeight_mass]
  have hTarget0 : 0 ≤ target μ A := (by positivity : (0 : ℝ) ≤ c*n^2).trans hTarget
  have hm := mixedMass_nonneg A B μ ℓ hμ
  have hChoose : (1 : ℝ) ≤ Nat.choose 4 ℓ := by
    rcases (show ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 by omega) with rfl | rfl | rfl <;> norm_num [Nat.choose]
  nlinarith only [hTarget, hm, mul_le_mul_of_nonneg_right hChoose hTarget0]

/-- The padded weights have all nonempty partial degrees bounded by an
explicit constant times the order of the ambient carrier. -/
theorem paddedCompletionWeight_degree_le (A B : Finset (Finset V))
    (μ : Finset V → ℝ) (C : ℝ) (L : ℕ) (hC : 1 ≤ C)
    (hn : 0 < Fintype.card V) (hA : ∀ Q ∈ A, Q.card = 3)
    (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T)
    (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ3 : ℓ ≤ 3)
    (R : Finset (Finset V)) (hRA : R ⊆ A)
    (hR1 : 1 ≤ R.card) (hRℓ : R.card ≤ ℓ) :
    (∑ S ∈ (A.powersetCard ℓ).filter (fun S => R ⊆ S),
      paddedCompletionWeight A B μ S * ∏ T ∈ S \ R, μ T) ≤
        (6*C^3 + mixedDegreeScale C L)*(Fintype.card V : ℝ) := by
  rw [paddedCompletionWeight_degree A B μ ℓ R hRℓ]
  have hExt := extensionMass_le_two_mul_cube A μ R hC (by omega) hA hRA hR1
    (by omega) hμ0 hμb
  have hExt0 := extensionMass_nonneg A μ R hμ0
  have hChoose : (Nat.choose (4-R.card) (ℓ-R.card) : ℝ) ≤ 3 := by
    have hRcases : R.card = 1 ∨ R.card = 2 ∨ R.card = 3 := by omega
    rcases hRcases with hR | hR | hR <;>
      rcases (show ℓ = 1 ∨ ℓ = 2 ∨ ℓ = 3 by omega) with hℓ | hℓ | hℓ <;>
      norm_num [hR, hℓ]
  have hBase : (Nat.choose (4-R.card) (ℓ-R.card) : ℝ)*extensionMass A μ R ≤ 6*C^3 := by
    have hh := mul_le_mul_of_nonneg_right hChoose hExt0
    linarith
  have hMixed := mixedDegree_le_scale_mul_order A B μ C L (by linarith) hn hA hL hB
    hμ0 hμb ℓ hℓ1 hℓ3 R hRA hR1 hRℓ
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hBaseN := mul_le_mul_of_nonneg_left hnR (show (0 : ℝ) ≤ 6*C^3 by positivity)
  nlinarith only [hBase, hMixed, hBaseN]

#print axioms IsPasch.baseMatching
#print axioms extensionMass_zero_of_not_matching
#print axioms completionWeight_zero_of_not_matching
#print axioms paddedCompletionWeight_nonneg
#print axioms paddedCompletionWeight_clean
#print axioms paddedCompletionWeight_mass
#print axioms paddedCompletionWeight_degree
#print axioms paddedCompletionWeight_mass_lower
#print axioms paddedCompletionWeight_degree_le
end TypedTriangle.Pasch
