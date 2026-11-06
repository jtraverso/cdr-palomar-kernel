module
public import RequestProject.TypedTriangle.PaschCatalogPotentialGrowth
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace TypedTriangle.Pasch
open CatalogNative.Explicit

/-- Geometry-only coefficient: no packing, precision cap, stock density,
or previous universe occurs in this expression. -/
def bankCubicPaymentCoefficient (α β : ℝ) (h d c E d' c' E' B : ℕ) : ℝ :=
  8*(B:ℝ)*catalogCellPotentialCost α β h d c E d' c' E' 1

theorem bankCubicPaymentCoefficient_nonneg {α β : ℝ} (hα : 0 < α)
    (h d c E d' c' E' B : ℕ) :
    0 ≤ bankCubicPaymentCoefficient α β h d c E d' c' E' B := by
  unfold bankCubicPaymentCoefficient
  exact mul_nonneg (by positivity) (RichBank.catalogCellPotentialCost_nonneg hα h d c E d' c' E' 1)

/-- The actual ambient denominator is the LOCAL HOST order; the quadratic
round count uses the possibly smaller catalog core. Both scales are retained. -/
theorem bank_total_payment_le (entries B nRoot nHost nCore : ℕ) (κ cost : ℝ)
    (hκ : 0 ≤ κ) (hcost : 0 ≤ cost) (hCore : 0 < nCore) (hCH : nCore ≤ nHost)
    (hLen : entries ≤ B*⌊κ*(nCore:ℝ)^2⌋₊) :
    (entries:ℝ)*((nRoot:ℝ)/nHost*cost) ≤ (B:ℝ)*κ*cost*nRoot*nCore := by
  have hHost : (0:ℝ) < nHost := by exact_mod_cast (hCore.trans_le hCH)
  have hCHr : (nCore:ℝ) ≤ nHost := by exact_mod_cast hCH
  have hRatio : (nCore:ℝ)/nHost ≤ 1 := (div_le_one hHost).mpr hCHr
  have hLenr : (entries:ℝ) ≤ (B:ℝ)*(⌊κ*(nCore:ℝ)^2⌋₊:ℝ) := by exact_mod_cast hLen
  have hFloor : (⌊κ*(nCore:ℝ)^2⌋₊:ℝ) ≤ κ*(nCore:ℝ)^2 :=
    Nat.floor_le (mul_nonneg hκ (sq_nonneg _))
  have hBound : (entries:ℝ) ≤ (B:ℝ)*(κ*(nCore:ℝ)^2) :=
    hLenr.trans (mul_le_mul_of_nonneg_left hFloor (by positivity))
  calc
    _ ≤ ((B:ℝ)*(κ*(nCore:ℝ)^2))*((nRoot:ℝ)/nHost*cost) :=
      mul_le_mul_of_nonneg_right hBound (mul_nonneg (by positivity) hcost)
    _ = ((B:ℝ)*κ*cost*nRoot*nCore)*((nCore:ℝ)/nHost) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hRatio

private theorem shifted_cube_le (L : ℕ) :
    ((L+2:ℕ):ℝ)^3 ≤ 8*((L+1:ℕ):ℝ)^3 := by
  have hh : ((L+2:ℕ):ℝ) ≤ 2*((L+1:ℕ):ℝ) := by push_cast; linarith
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ((L+2:ℕ):ℝ)) hh 3
  nlinarith only [hp]

/-- The cubic codegree loss is independent of all bank precision caps. -/
theorem catalog_bank_total_payment_cubic_le (α β : ℝ) (hα : 0 < α)
    (h d c E d' c' E' entries B nRoot nHost nCore L : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ) (hCore : 0 < nCore) (hCH : nCore ≤ nHost)
    (hLen : entries ≤ B*⌊κ*(nCore:ℝ)^2⌋₊) :
    (entries:ℝ)*((nRoot:ℝ)/nHost*catalogCellPotentialCost α β h d c E d' c' E' (L+2)) ≤
      bankCubicPaymentCoefficient α β h d c E d' c' E' B *κ*((L+1:ℕ):ℝ)^3*nRoot*nCore := by
  have hCost0 := RichBank.catalogCellPotentialCost_nonneg (β:=β) hα h d c E d' c' E' 1
  have hCost : catalogCellPotentialCost α β h d c E d' c' E' (L+2) ≤
      8*((L+1:ℕ):ℝ)^3*catalogCellPotentialCost α β h d c E d' c' E' 1 :=
    (catalogCellPotentialCost_cubic_le α β h d c E d' c' E' (L+2) (by omega)).trans
      (mul_le_mul_of_nonneg_right (shifted_cube_le L) hCost0)
  have hFirst := bank_total_payment_le entries B nRoot nHost nCore κ
    (catalogCellPotentialCost α β h d c E d' c' E' (L+2)) hκ
    (RichBank.catalogCellPotentialCost_nonneg hα h d c E d' c' E' (L+2)) hCore hCH hLen
  calc
    _ ≤ (B:ℝ)*κ*catalogCellPotentialCost α β h d c E d' c' E' (L+2)*nRoot*nCore := hFirst
    _ ≤ (B:ℝ)*κ*(8*((L+1:ℕ):ℝ)^3*catalogCellPotentialCost α β h d c E d' c' E' 1)*nRoot*nCore := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCost (by positivity)) (by positivity)) (by positivity)
    _ = _ := by unfold bankCubicPaymentCoefficient; ring

/-- Inner payment is O((L+1)^3 nRoot nHost), with the actual rate retained. -/
theorem catalog_bank_inner_payment_le (α β : ℝ) (hα : 0 < α)
    (h d c E d' c' E' entries B nRoot nHost nCore L : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ) (hCore : 0 < nCore) (hCH : nCore ≤ nHost)
    (hLen : entries ≤ B*⌊κ*(nCore:ℝ)^2⌋₊) :
    (entries:ℝ)*((nRoot:ℝ)/nHost*catalogCellPotentialCost α β h d c E d' c' E' (L+2)) ≤
      bankCubicPaymentCoefficient α β h d c E d' c' E' B *κ*((L+1:ℕ):ℝ)^3*nRoot*nHost := by
  apply (catalog_bank_total_payment_cubic_le α β hα h d c E d' c' E' entries B nRoot nHost nCore L κ
    hκ hCore hCH hLen).trans
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hCH)
    (mul_nonneg (mul_nonneg (mul_nonneg (bankCubicPaymentCoefficient_nonneg hα h d c E d' c' E' B)
      hκ) (by positivity)) (by positivity))

/-- On the first core the total cost tends to zero with qOuter, even though
the price of one cell contains the reciprocal core/host ratio. -/
theorem catalog_bank_outer_payment_le (α β : ℝ) (hα : 0 < α)
    (h d c E d' c' E' entries B nRoot nHost nCore L : ℕ) (κ qOuter : ℝ)
    (hκ : 0 ≤ κ) (hCore : 0 < nCore) (hCH : nCore ≤ nHost)
    (hWindow : (nCore:ℝ) ≤ 2*qOuter*nRoot)
    (hLen : entries ≤ B*⌊κ*(nCore:ℝ)^2⌋₊) :
    (entries:ℝ)*((nRoot:ℝ)/nHost*catalogCellPotentialCost α β h d c E d' c' E' (L+2)) ≤
      2*bankCubicPaymentCoefficient α β h d c E d' c' E' B *κ*((L+1:ℕ):ℝ)^3*qOuter*(nRoot:ℝ)^2 := by
  have hK : 0 ≤ bankCubicPaymentCoefficient α β h d c E d' c' E' B *κ*((L+1:ℕ):ℝ)^3*nRoot :=
    mul_nonneg (mul_nonneg (mul_nonneg (bankCubicPaymentCoefficient_nonneg hα h d c E d' c' E' B)
      hκ) (by positivity)) (by positivity)
  calc
    _ ≤ bankCubicPaymentCoefficient α β h d c E d' c' E' B *κ*((L+1:ℕ):ℝ)^3*nRoot*nCore :=
      catalog_bank_total_payment_cubic_le α β hα h d c E d' c' E' entries B nRoot nHost nCore L κ
        hκ hCore hCH hLen
    _ ≤ bankCubicPaymentCoefficient α β h d c E d' c' E' B *κ*((L+1:ℕ):ℝ)^3*nRoot*(2*qOuter*nRoot) :=
      mul_le_mul_of_nonneg_left hWindow hK
    _ = _ := by ring

/-- The native producer uses precisely this ratio and the catalog window
cardinality. Its actual-list length certificate supplies hLen directly. -/
theorem ambient_catalog_bank_inner_payment_le {X V : Type*} [Fintype X] [Fintype V]
    (ι : X ↪ V) (W : Finset X) (α β : ℝ) (hα : 0 < α)
    (h d c E d' c' E' entries B L : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ) (hW : 0 < W.card) (hLen : entries ≤ B*⌊κ*(W.card:ℝ)^2⌋₊) :
    (entries:ℝ)*(Ambient.orderRatio ι*catalogCellPotentialCost α β h d c E d' c' E' (L+2)) ≤
      bankCubicPaymentCoefficient α β h d c E d' c' E' B *κ*((L+1:ℕ):ℝ)^3*
        Fintype.card V*Fintype.card X := by
  exact catalog_bank_inner_payment_le α β hα h d c E d' c' E' entries B
    (Fintype.card V) (Fintype.card X) W.card L κ hκ hW (Finset.card_le_univ W) hLen

theorem ambient_catalog_bank_outer_payment_le {X V : Type*} [Fintype X] [Fintype V]
    (ι : X ↪ V) (W : Finset X) (α β : ℝ) (hα : 0 < α)
    (h d c E d' c' E' entries B L : ℕ) (κ qOuter : ℝ)
    (hκ : 0 ≤ κ) (hW : 0 < W.card) (hWindow : (W.card:ℝ) ≤ 2*qOuter*Fintype.card V)
    (hLen : entries ≤ B*⌊κ*(W.card:ℝ)^2⌋₊) :
    (entries:ℝ)*(Ambient.orderRatio ι*catalogCellPotentialCost α β h d c E d' c' E' (L+2)) ≤
      2*bankCubicPaymentCoefficient α β h d c E d' c' E' B *κ*((L+1:ℕ):ℝ)^3*
        qOuter*(Fintype.card V:ℝ)^2 := by
  exact catalog_bank_outer_payment_le α β hα h d c E d' c' E' entries B
    (Fintype.card V) (Fintype.card X) W.card L κ qOuter hκ hW (Finset.card_le_univ W) hWindow hLen

/-- This upper rate is fixed from geometry and multiplicity before choosing
εcap, δcap or any stock density. It does not replace the actual rate. -/
def geometricBankRoundRate (α β : ℝ) (h P : ℕ) : ℝ :=
  quadraticBankRate (bankProtectionBudget α β h) (ExplicitGeometry.deletionBudget α h)
    (bankCellSize α β h) (bankCopies α β h P)

theorem bankRoundRate_le_geometric (α β εcap δcap : ℝ) (h P : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hε : 0 < εcap) (hδ : 0 < δcap) :
    bankRoundRate α β εcap δcap h P ≤ geometricBankRoundRate α β h P := by
  have hTol : bankTolerance α β εcap h ≤ bankProtectionBudget α β h := min_le_left _ _
  have hDel : bankDeletionBudget α β δcap h ≤ ExplicitGeometry.deletionBudget α h := min_le_left _ _
  unfold bankRoundRate geometricBankRoundRate quadraticBankRate
  exact div_le_div_of_nonneg_right (mul_le_mul hTol hDel
    (bankDeletionBudget_pos h hα hβ hδ).le (bankProtectionBudget_pos h hα hβ).le) (by positivity)

end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.bank_total_payment_le
#print axioms TypedTriangle.Pasch.catalog_bank_total_payment_cubic_le
#print axioms TypedTriangle.Pasch.catalog_bank_inner_payment_le
#print axioms TypedTriangle.Pasch.catalog_bank_outer_payment_le
#print axioms TypedTriangle.Pasch.bankRoundRate_le_geometric

#print axioms TypedTriangle.Pasch.ambient_catalog_bank_inner_payment_le
#print axioms TypedTriangle.Pasch.ambient_catalog_bank_outer_payment_le
