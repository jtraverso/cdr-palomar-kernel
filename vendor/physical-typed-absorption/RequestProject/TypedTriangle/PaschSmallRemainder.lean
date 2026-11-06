module
public import RequestProject.TypedTriangle.PaschAdaptiveBudget
public import RequestProject.TypedTriangle.PaschPackingModel
public import RequestProject.TypedTriangle.TriangleMonitorCompletionCount
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

theorem fourth_root_square_le_sqrt (n m : ℕ)
    (hCut : m ≤ Nat.sqrt (Nat.sqrt n)) : (m : ℝ)^2 ≤ Real.sqrt (n : ℝ) := by
  have hSq : m^2 ≤ Nat.sqrt n := Nat.le_sqrt'.mp hCut
  have hCast : (m : ℝ)^2 ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast hSq
  exact hCast.trans Real.nat_sqrt_le_real_sqrt

/-- Every block added by the existing exact tail assembly is paid for by
the uncovered edges. No assertion about its individual Pasch modes is needed. -/
theorem completion_blocks_le_remainder {H : Host V I} {F : Set (Multiset I)}
    {P D : Finset (Finset V)} (hD : IsDecomposition H F (edges H) D)
    (hPD : P ⊆ D) (K m : ℕ)
    (hRest : (edges H \ P.biUnion triEdges).card ≤ K+m^2) :
    (D \ P).card ≤ K+m^2 := by
  have hh := TriangleMonitors.completion_card_identity hD hPD
  omega

theorem small_remainder_order_payment (K m n : ℕ) (τ : ℝ)
    (hτ : 0 < τ) (hn : 0 < n)
    (hCut : m ≤ Nat.sqrt (Nat.sqrt n))
    (hReserve : ⌈(K : ℝ)/τ⌉₊ ≤ n) (hSqrt : ⌈1/τ^2⌉₊ ≤ n) :
    ((K+m^2 : ℕ) : ℝ) ≤ (2*τ)*(n : ℝ) := by
  have hK := terminal_order_payment K τ hτ n hReserve
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : 4/(2*τ)^2 ≤ (n : ℝ) := by
    have hh : 1/τ^2 ≤ (n : ℝ) := Nat.ceil_le.mp hSqrt
    have hEq : (4 : ℝ)/(2*τ)^2 = 1/τ^2 := by field_simp; ring
    rw [hEq]
    exact hh
  have hSq := fourth_root_square_le_sqrt n m hCut
  have hLinear := sqrt_le_linear_of_order (show 0 < 2*τ by positivity) hnR hN
  push_cast
  nlinarith only [hK,hSq,hLinear]

/-- The literal paid prefix is retained by the final decomposition. Its
same original target survives arbitrary exact completion below the cutoff. -/
theorem small_remainder_completion_target_error {H : Host V I}
    {F : Set (Multiset I)} {P D : Finset (Finset V)}
    (hP : IsPacking H F P) (hD : IsDecomposition H F (edges H) D)
    (hPD : P ⊆ D) (K m : ℕ) (τ σ targetValue : ℝ)
    (hτ : 0 < τ) (hn : 0 < Fintype.card V)
    (hCut : m ≤ Nat.sqrt (Nat.sqrt (Fintype.card V)))
    (hReserve : ⌈(K : ℝ)/τ⌉₊ ≤ Fintype.card V)
    (hSqrt : ⌈1/τ^2⌉₊ ≤ Fintype.card V)
    (hRest : (edges H \ P.biUnion triEdges).card ≤ K+m^2)
    (hTarget : |(count P : ℝ)-targetValue| ≤ σ*(Fintype.card V : ℝ)^2) :
    |(count D : ℝ)-targetValue| ≤ (σ+2*τ)*(Fintype.card V : ℝ)^2 := by
  have hDP : IsPacking H F D := ⟨hD.1,hD.2.1⟩
  exact terminal_extension_target_error hP hDP hPD
    (completion_blocks_le_remainder hD hPD K m hRest)
    (small_remainder_order_payment K m (Fintype.card V) τ hτ hn hCut hReserve hSqrt)
    hTarget

#print axioms fourth_root_square_le_sqrt
#print axioms completion_blocks_le_remainder
#print axioms small_remainder_order_payment
#print axioms small_remainder_completion_target_error
end TypedTriangle.Pasch
