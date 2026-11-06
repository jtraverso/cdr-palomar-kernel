module
public import RequestProject.TypedTriangle.PaschAdaptiveBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace TypedTriangle.Pasch

/-- The additive ceiling loss in a resource degree is paid by a finite
order threshold, after the geometric coefficient has been fixed. -/
theorem resource_degree_payment_le {cost β ρ n : ℝ} (hCost : 0 ≤ cost)
    (hβ : 0 < β) (hn : 0 ≤ n) (hRate : 2*cost*ρ ≤ β)
    (hOrder : 4*cost/β ≤ n) (r : ℕ) (hR : (r : ℝ) ≤ ρ*n+1) :
    cost*((r : ℝ)+1)*n ≤ β*n^2 := by
  have hRPay := mul_le_mul_of_nonneg_right hR (mul_nonneg hCost hn)
  have hRatePay := mul_le_mul_of_nonneg_right hRate (sq_nonneg n)
  have hOrder' := (div_le_iff₀ hβ).mp hOrder
  have hOrderPay := mul_le_mul_of_nonneg_right hOrder' hn
  nlinarith only [hRPay,hRatePay,hOrderPay]

def outerResourceRate (legacy cost β : ℝ) : ℝ := paschBudgetRate legacy (2*cost) β

def outerResourceOrder (cost β : ℝ) : ℕ := max 1 ⌈4*cost/β⌉₊

/-- The rate and order depend only on already chosen numerical parameters,
before the host. Reducing the input degree does not invert the stock supply
in the geometric selector payment. -/
theorem outer_resource_rate_and_order (legacy cost β : ℝ)
    (hLegacy : 0 < legacy) (hCost : 0 ≤ cost) (hβ : 0 < β) :
    0 < outerResourceRate legacy cost β ∧ outerResourceRate legacy cost β ≤ legacy ∧
      ∀ n r : ℕ, outerResourceOrder cost β ≤ n →
      (r : ℝ) ≤ outerResourceRate legacy cost β*(n : ℝ)+1 →
      cost*((r : ℝ)+1)*(n : ℝ) ≤ β*(n : ℝ)^2 := by
  obtain ⟨hPos,hCap,hRate⟩ := paschBudgetRate_spec legacy (2*cost) β hLegacy (by positivity) hβ
  refine ⟨hPos,hCap,?_⟩
  intro n r hn hR
  have hOrder : 4*cost/β ≤ (n : ℝ) := by
    apply Nat.ceil_le.mp
    exact (le_max_right _ _).trans hn
  exact resource_degree_payment_le hCost hβ (by positivity) hRate hOrder r hR

#print axioms resource_degree_payment_le
#print axioms outer_resource_rate_and_order
end TypedTriangle.Pasch
