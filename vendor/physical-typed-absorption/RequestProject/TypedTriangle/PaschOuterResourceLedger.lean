module
public import RequestProject.TypedTriangle.PaschOuterPackingUniverseBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace TypedTriangle.Pasch
variable {V : Type*} [Fintype V]

/-- Combine the actual stock, withdrawal and bank certificates. Size is
paid from support and degrees independently of the Pasch-count budget. -/
theorem outer_resource_count_and_size_budget
    (D U Bank : Finset (Finset V)) (β δ ρ τSel : ℝ)
    (hStock : (count D : ℝ) ≤ (β/3)*(Fintype.card V : ℝ)^2)
    (hWithdrawal : (count (D∪U) : ℝ) ≤ count D+(β/3)*(Fintype.card V : ℝ)^2)
    (hBank : (count ((D∪U)∪Bank) : ℝ) ≤ count (D∪U)+(β/3)*(Fintype.card V : ℝ)^2)
    (hStockSize : (D.card : ℝ) ≤ ρ*(Fintype.card V : ℝ)^2)
    (hWithdrawalSize : (U.card : ℝ) ≤ 63*(τSel+ρ)*(Fintype.card V : ℝ)^2)
    (hBankSize : (Bank.card : ℝ) ≤ (δ/2)*(Fintype.card V : ℝ)^2)
    (hSizeRates : 64*ρ+63*τSel ≤ δ/2) :
    (count ((D∪U)∪Bank) : ℝ) ≤ β*(Fintype.card V : ℝ)^2 ∧
    (((D∪U)∪Bank).card : ℝ) ≤ δ*(Fintype.card V : ℝ)^2 := by
  constructor
  · linarith only [hStock,hWithdrawal,hBank]
  · have hUnion : (((D∪U)∪Bank).card : ℝ) ≤ D.card+U.card+Bank.card := by
      exact_mod_cast (card_union_le (D∪U) Bank).trans
        (Nat.add_le_add_right (card_union_le D U) Bank.card)
    have hRates := mul_le_mul_of_nonneg_right hSizeRates (sq_nonneg (Fintype.card V : ℝ))
    nlinarith only [hUnion,hStockSize,hWithdrawalSize,hBankSize,hRates]

theorem quadratic_bank_size_payment (q coefficient δ : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hCoefficient : 0 ≤ coefficient)
    (hRate : 2*coefficient*q ≤ δ) : coefficient*q^2 ≤ δ/2 := by
  have hSquare : q^2 ≤ q := by nlinarith only [hq0,hq1]
  have hPay := mul_le_mul_of_nonneg_left hSquare hCoefficient
  linarith only [hRate,hPay]

#print axioms outer_resource_count_and_size_budget
#print axioms quadratic_bank_size_payment
end TypedTriangle.Pasch
