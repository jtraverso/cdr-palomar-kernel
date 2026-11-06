module
public import RequestProject.TypedTriangle.PaschMixedConfigurationBounds
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mixedDegree_le_nat_bound (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (ℓ : ℕ) (R : Finset (Finset V)) (C : ℝ) (hC : 0 ≤ C) (hn : 0 < Fintype.card V)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ))
    (M : ℕ) (hM : (mixedConfigurations A B ℓ R).card ≤ M) :
    mixedDegree A B μ ℓ R ≤ (M : ℝ)*(C/(Fintype.card V : ℝ))^(ℓ-R.card) := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hb := div_nonneg hC hnR.le
  have hh := mixedDegree_le_card_power A B μ ℓ R hb hμ0 hμb
  have hCount : ((mixedConfigurations A B ℓ R).card : ℝ) ≤ M := by exact_mod_cast hM
  exact hh.trans (mul_le_mul_of_nonneg_right hCount (pow_nonneg hb _))

theorem mixedMass_three_le (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hn : 0 < Fintype.card V)
    (hB : ∀ Q ∈ B, Q.card = 3) (hμ0 : ∀ T ∈ A, 0 ≤ μ T)
    (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ)) :
    mixedMass A B μ 3 ≤ C^3*B.card := by
  rw [mixedMass_eq_mixedDegree_empty]
  have hh := mixedDegree_le_nat_bound A B μ 3 ∅ C hC hn hμ0 hμb
    ((Fintype.card V)^3*B.card) (mixedConfigurations_three_card_le A B ∅ hB)
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  apply hh.trans_eq
  simp only [card_empty, Nat.sub_zero, Nat.cast_mul, Nat.cast_pow]
  field_simp [ne_of_gt hnR]
  <;> ring

theorem mixedMass_two_le (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (C : ℝ) (L : ℕ) (hC : 0 ≤ C) (hn : 0 < Fintype.card V)
    (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ)) :
    mixedMass A B μ 2 ≤ 6*(L : ℝ)*C^2*B.card := by
  rw [mixedMass_eq_mixedDegree_empty]
  have hh := mixedDegree_le_nat_bound A B μ 2 ∅ C hC hn hμ0 hμb
    (6*(Fintype.card V)^2*L*B.card) (mixedConfigurations_two_card_le A B ∅ L hL hB)
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  apply hh.trans_eq
  simp only [card_empty, Nat.sub_zero, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  <;> field_simp [ne_of_gt hnR]
  <;> ring

theorem mixedMass_one_le (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (C : ℝ) (L : ℕ) (hC : 0 ≤ C) (hn : 0 < Fintype.card V)
    (hL : PairCodegreeBound B L) (hB : ∀ Q ∈ B, Q.card = 3)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ)) :
    mixedMass A B μ 1 ≤ 27*C*(L : ℝ)^2*B.card := by
  rw [mixedMass_eq_mixedDegree_empty]
  have hh := mixedDegree_le_nat_bound A B μ 1 ∅ C hC hn hμ0 hμb
    (27*Fintype.card V*L^2*B.card) (mixedConfigurations_one_card_le A B ∅ L hL hB)
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  apply hh.trans_eq
  simp only [card_empty, Nat.sub_zero, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_one]
  <;> field_simp [ne_of_gt hnR]
  <;> ring

theorem mixedDegree_one_root_le (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (C : ℝ) (L : ℕ) (hC : 0 ≤ C) (hn : 0 < Fintype.card V)
    (hL : PairCodegreeBound B L) (hB : ∀ T ∈ B, T.card = 3)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ))
    (Q : Finset V) (hQ : Q.card = 3) (hQB : Q ∉ B) :
    mixedDegree A B μ 1 {Q} ≤ 27*(Fintype.card V : ℝ)*(L : ℝ)^2 := by
  have hh := mixedDegree_le_nat_bound A B μ 1 {Q} C hC hn hμ0 hμb
    (27*Fintype.card V*L^2) (mixedConfigurations_root_small_card_le A B L hL hB Q hQ hQB 1 (by omega))
  simpa only [card_singleton, Nat.sub_self, pow_zero, mul_one,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hh

theorem mixedDegree_two_root_le (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (C : ℝ) (L : ℕ) (hC : 0 ≤ C) (hn : 0 < Fintype.card V)
    (hL : PairCodegreeBound B L) (hB : ∀ T ∈ B, T.card = 3)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ))
    (Q : Finset V) (hQ : Q.card = 3) (hQB : Q ∉ B) :
    mixedDegree A B μ 2 {Q} ≤ 27*C*(L : ℝ)^2 := by
  have hh := mixedDegree_le_nat_bound A B μ 2 {Q} C hC hn hμ0 hμb
    (27*Fintype.card V*L^2) (mixedConfigurations_root_small_card_le A B L hL hB Q hQ hQB 2 (by omega))
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  apply hh.trans_eq
  simp only [card_singleton, Nat.reduceSub, pow_one, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  <;> field_simp [ne_of_gt hnR]
  <;> ring

theorem mixedDegree_three_root_le (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (C : ℝ) (L : ℕ) (hC : 0 ≤ C) (hn : 0 < Fintype.card V)
    (hL : PairCodegreeBound B L) (hB : ∀ T ∈ B, T.card = 3)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ))
    (Q : Finset V) (hQ : Q.card = 3) (hQB : Q ∉ B) :
    mixedDegree A B μ 3 {Q} ≤ 6*(L : ℝ)*C^2 := by
  have hh := mixedDegree_le_nat_bound A B μ 3 {Q} C hC hn hμ0 hμb
    (6*(Fintype.card V)^2*L) (mixedConfigurations_root_three_card_le A B L hL hB Q hQ hQB)
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  apply hh.trans_eq
  simp only [card_singleton, Nat.reduceSub, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  <;> field_simp [ne_of_gt hnR]
  <;> ring

theorem mixedDegree_two_pair_le (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hn : 0 < Fintype.card V)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ))
    (R : Finset (Finset V)) (hR : R.card = 2) :
    mixedDegree A B μ 2 R ≤ 2*(Fintype.card V : ℝ) := by
  have hh := mixedDegree_le_nat_bound A B μ 2 R C hC hn hμ0 hμb
    (2*Fintype.card V) (mixedConfigurations_pair_card_le A B R 2 hR)
  simpa only [hR, Nat.sub_self, pow_zero, mul_one, Nat.cast_mul, Nat.cast_ofNat] using hh

theorem mixedDegree_three_pair_le (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hn : 0 < Fintype.card V)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ))
    (R : Finset (Finset V)) (hR : R.card = 2) :
    mixedDegree A B μ 3 R ≤ 2*C := by
  have hh := mixedDegree_le_nat_bound A B μ 3 R C hC hn hμ0 hμb
    (2*Fintype.card V) (mixedConfigurations_pair_card_le A B R 3 hR)
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  apply hh.trans_eq
  simp only [hR, Nat.reduceSub, pow_one, Nat.cast_mul, Nat.cast_ofNat]
  <;> field_simp [ne_of_gt hnR]
  <;> ring

theorem mixedDegree_three_triple_le (A B : Finset (Finset V)) (μ : Finset V → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hn : 0 < Fintype.card V)
    (hμ0 : ∀ T ∈ A, 0 ≤ μ T) (hμb : ∀ T ∈ A, μ T ≤ C/(Fintype.card V : ℝ))
    (R : Finset (Finset V)) (hR : R.card = 3) : mixedDegree A B μ 3 R ≤ 1 := by
  have hh := mixedDegree_le_nat_bound A B μ 3 R C hC hn hμ0 hμb
    1 (mixedConfigurations_triple_card_le A B R 3 hR)
  simpa only [hR, Nat.sub_self, pow_zero, mul_one, Nat.cast_one] using hh

#print axioms mixedMass_one_le
#print axioms mixedMass_two_le
#print axioms mixedMass_three_le
#print axioms mixedDegree_one_root_le
#print axioms mixedDegree_two_root_le
#print axioms mixedDegree_three_root_le
#print axioms mixedDegree_two_pair_le
#print axioms mixedDegree_three_pair_le
#print axioms mixedDegree_three_triple_le
end TypedTriangle.Pasch
