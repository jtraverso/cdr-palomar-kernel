module
public import RequestProject.TypedTriangle.PaschTerminalEstimate
public import RequestProject.TypedTriangle.PaschPaddedMixedAssembly
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V]

/-- Sum the actual one-step count certificates along a finite adaptive run. -/
theorem count_prefix_budget (U : ℕ → Finset (Finset V)) (cost : ℕ → ℝ)
    (hStep : ∀ j, (count (U (j+1)) : ℝ) ≤ count (U j)+cost j) (N : ℕ) :
    (count (U N) : ℝ) ≤ count (U 0)+∑ j ∈ range N, cost j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hs := hStep N
    linarith only [ih,hs]

/-- Final activation may select any stored modes. Literal containment of
the original packing and the completed family is enough to transfer the
accumulated count certificate to the exact decomposition. -/
theorem adaptive_sandwich_target_error (base available D : Finset (Finset V))
    (targetValue σ τ spent : ℝ) (hBaseD : base ⊆ D) (hDU : D ⊆ available)
    (hCount : (count available : ℝ) ≤ count base+spent)
    (hSpent0 : 0 ≤ spent) (hSpent : spent ≤ τ*(Fintype.card V : ℝ)^2)
    (hBase : |(count base : ℝ)-targetValue| ≤ σ*(Fintype.card V : ℝ)^2) :
    |(count D : ℝ)-targetValue| ≤ (σ+τ)*(Fintype.card V : ℝ)^2 := by
  have hLo : (count base : ℝ) ≤ count D := by exact_mod_cast count_mono_of_subset hBaseD
  have hHi : (count D : ℝ) ≤ count available := by exact_mod_cast count_mono_of_subset hDU
  obtain ⟨hBaseLo,hBaseHi⟩ := abs_le.mp hBase
  apply abs_le.mpr
  constructor <;> nlinarith only [hLo,hHi,hCount,hSpent0,hSpent,hBaseLo,hBaseHi]

/-- The upper size ratio in the existing vortex is at most 1/16. -/
theorem shrinking_host_sum_le (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hShrink : ∀ j, a (j+1) ≤ a j/16) (N : ℕ) :
    (∑ j ∈ range N, a j) ≤ 16*a 0/15 := by
  have hStrong : ∀ M, (∑ j ∈ range M, a j) ≤ 16*(a 0-a M)/15 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [sum_range_succ]
      have hs := hShrink M
      linarith only [ih,hs]
  have hh := hStrong N
  have hLast := ha N
  linarith only [hh,hLast]

/-- Ambient support costs sum quadratically despite the changing carrier.
The exact nRoot/nHost factor has already been multiplied by the actual
number of local choices, leaving nRoot*nHost at each layer. -/
theorem adaptive_linear_cost_sum_bound (a : ℕ → ℝ) (D nRoot q : ℝ)
    (hD : 0 ≤ D) (hnRoot : 0 ≤ nRoot) (ha : ∀ j, 0 ≤ a j)
    (hShrink : ∀ j, a (j+1) ≤ a j/16) (hFirst : a 0 ≤ 2*q*nRoot) (N : ℕ) :
    (∑ j ∈ range N, D*nRoot*a j) ≤ (32/15 : ℝ)*D*q*nRoot^2 := by
  have hs := shrinking_host_sum_le a ha hShrink N
  have hFirst' : 16*a 0/15 ≤ 16*(2*q*nRoot)/15 := by linarith only [hFirst]
  calc
    _ = (D*nRoot)*(∑ j ∈ range N, a j) := (mul_sum _ _ _).symm
    _ ≤ (D*nRoot)*(16*a 0/15) := mul_le_mul_of_nonneg_left hs (mul_nonneg hD hnRoot)
    _ ≤ (D*nRoot)*(16*(2*q*nRoot)/15) :=
      mul_le_mul_of_nonneg_left hFirst' (mul_nonneg hD hnRoot)
    _ = _ := by ring

def paschBudgetRate (legacy cost ε : ℝ) : ℝ := min legacy (ε/(cost+1))

/-- An explicit positive rate, chosen before the host, pays a proved cost
coefficient while preserving the original parameter cap. -/
theorem paschBudgetRate_spec (legacy cost ε : ℝ)
    (hLegacy : 0 < legacy) (hCost : 0 ≤ cost) (hε : 0 < ε) :
    0 < paschBudgetRate legacy cost ε ∧ paschBudgetRate legacy cost ε ≤ legacy ∧
      cost*paschBudgetRate legacy cost ε ≤ ε := by
  have hPos : 0 < paschBudgetRate legacy cost ε := lt_min hLegacy (by positivity)
  have hCap : paschBudgetRate legacy cost ε ≤ ε/(cost+1) := min_le_right _ _
  have hMul := (le_div_iff₀ (by positivity : 0 < cost+1)).mp hCap
  exact ⟨hPos,min_le_left _ _,by nlinarith only [hMul,hPos.le]⟩

theorem terminal_order_payment (K : ℕ) (τ : ℝ) (hτ : 0 < τ) (n : ℕ)
    (hOrder : ⌈(K : ℝ)/τ⌉₊ ≤ n) : (K : ℝ) ≤ τ*(n : ℝ) := by
  have hh : (K : ℝ)/τ ≤ (n : ℝ) := Nat.ceil_le.mp hOrder
  exact ((div_le_iff₀ hτ).mp hh).trans_eq (mul_comm _ _)

#print axioms count_prefix_budget
#print axioms adaptive_sandwich_target_error
#print axioms shrinking_host_sum_le
#print axioms adaptive_linear_cost_sum_bound
#print axioms paschBudgetRate_spec
#print axioms terminal_order_payment
end TypedTriangle.Pasch
