module
public import RequestProject.TypedTriangle.PaschRootedInfluence
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V] {H : Host V I} {F : Set (Multiset I)}

/-- A terminal extension of at most K blocks costs at most K times the
ambient order. The bound is applied to the actual final packing. -/
theorem terminal_extension_count_error {P D : Finset (Finset V)} {K : ℕ}
    (hP : IsPacking H F P) (hD : IsPacking H F D) (hPD : P ⊆ D)
    (hK : (D \ P).card ≤ K) :
    |(count D : ℝ)-count P| ≤ (K : ℝ)*(Fintype.card V : ℝ) := by
  have hh := count_difference_le_of_packings hD hP
  have hEmpty : P \ D = ∅ := sdiff_eq_empty_iff_subset.mpr hPD
  rw [hEmpty, card_empty, Nat.cast_zero, max_eq_left (Nat.cast_nonneg _)] at hh
  have hDiff : ((D \ P).card : ℝ) ≤ K := by exact_mod_cast hK
  have hOrder : ((Fintype.card V - 3 : ℕ) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (Nat.sub_le (Fintype.card V) 3)
  exact hh.trans ((mul_le_mul_of_nonneg_left hDiff
    (Nat.cast_nonneg (Fintype.card V - 3))).trans
      ((mul_le_mul_of_nonneg_right hOrder (Nat.cast_nonneg K)).trans_eq (mul_comm _ _)))

/-- An order threshold absorbs the finite terminal addition into the
quadratic error budget relative to the same original target. -/
theorem terminal_extension_target_error {P D : Finset (Finset V)} {K : ℕ}
    {ε τ targetValue : ℝ} (hP : IsPacking H F P) (hD : IsPacking H F D)
    (hPD : P ⊆ D) (hK : (D \ P).card ≤ K)
    (hOrder : (K : ℝ) ≤ τ*(Fintype.card V : ℝ))
    (hTarget : |(count P : ℝ)-targetValue| ≤ ε*(Fintype.card V : ℝ)^2) :
    |(count D : ℝ)-targetValue| ≤ (ε+τ)*(Fintype.card V : ℝ)^2 := by
  have hCount := terminal_extension_count_error hP hD hPD hK
  have hPay := mul_le_mul_of_nonneg_right hOrder
    (show (0 : ℝ) ≤ Fintype.card V by positivity)
  have hTriangle := abs_add_le ((count D : ℝ)-count P) ((count P : ℝ)-targetValue)
  have hEq : ((count D : ℝ)-count P)+((count P : ℝ)-targetValue) =
      (count D : ℝ)-targetValue := by ring
  rw [hEq] at hTriangle
  nlinarith only [hCount, hPay, hTriangle, hTarget]

#print axioms terminal_extension_count_error
#print axioms terminal_extension_target_error
end TypedTriangle.Pasch
