module
public import RequestProject.TypedTriangle.PaschMixedBudget
public import RequestProject.TypedTriangle.PaschAdaptiveInitialState
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace TypedTriangle.Pasch

/-- A common profile cap, fixed before either sampled rate. -/
def commonProfileBudget (α γLegacy γInner γOuter εInner εOuter : ℝ) : ℝ :=
  min γLegacy (min γInner (min γOuter (min εInner εOuter/(α+1))))

theorem commonProfileBudget_pos (α γLegacy γInner γOuter εInner εOuter : ℝ)
    (hα : 0 ≤ α) (hL : 0 < γLegacy) (hI : 0 < γInner) (hO : 0 < γOuter)
    (hεI : 0 < εInner) (hεO : 0 < εOuter) :
    0 < commonProfileBudget α γLegacy γInner γOuter εInner εOuter := by
  unfold commonProfileBudget
  exact lt_min hL (lt_min hI (lt_min hO (div_pos (lt_min hεI hεO) (by linarith))))

theorem common_profile_caps (α γLegacy γInner γOuter εInner εOuter q ζ : ℝ)
    (hα : 0 ≤ α) (hL : 0 < γLegacy) (hI : 0 < γInner) (hO : 0 < γOuter)
    (hεI : 0 < εInner) (hεO : 0 < εOuter)
    (hq : q ≤ commonProfileBudget α γLegacy γInner γOuter εInner εOuter/8)
    (hζ : ζ ≤ α*q/128) :
    q ≤ γInner/8 ∧ q ≤ γOuter/8 ∧ ζ ≤ εInner ∧ ζ ≤ εOuter := by
  let γ := commonProfileBudget α γLegacy γInner γOuter εInner εOuter
  have hγ : 0 < γ := commonProfileBudget_pos _ _ _ _ _ _ hα hL hI hO hεI hεO
  have hγI : γ ≤ γInner := (min_le_right _ _).trans (min_le_left _ _)
  have hγO : γ ≤ γOuter := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγε : γ ≤ min εInner εOuter/(α+1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hPay := (le_div_iff₀ (by linarith : 0 < α+1)).mp hγε
  have hRate := mul_le_mul_of_nonneg_left hq hα
  have hProd := mul_nonneg hα hγ.le
  have hminI := min_le_left εInner εOuter
  have hminO := min_le_right εInner εOuter
  refine ⟨hq.trans (by linarith only [hγI]),hq.trans (by linarith only [hγO]),?_,?_⟩ <;>
    dsimp only [γ] at hPay hRate hProd <;> nlinarith only [hζ,hPay,hRate,hProd,hγ,hminI,hminO]

def outerMixedCountBudget (θ : ℝ) : ℝ := θ/4
def outerMixedSizeBudget (C θ : ℝ) (L : ℕ) : ℝ :=
  min 1 (θ/(4*(mixedMassBudget C L+1)))
def outerMixedTestBudget (C θ : ℝ) (L : ℕ) : ℝ :=
  min 1 (θ/(4*(7*C^3+mixedMassBudget C L+1)))

/-- Separate count, size and tuple-test errors can be chosen before the
outer stock is sampled. These are finite formulas in the fixed geometry. -/
theorem outer_mixed_budgets (C θ : ℝ) (L : ℕ) (hC : 0 ≤ C) (hθ : 0 < θ) :
    0 < outerMixedCountBudget θ ∧
    0 < outerMixedSizeBudget C θ L ∧ outerMixedSizeBudget C θ L ≤ 1 ∧
    0 < outerMixedTestBudget C θ L ∧ outerMixedTestBudget C θ L ≤ 1 ∧
    outerMixedCountBudget θ+mixedMassBudget C L*outerMixedSizeBudget C θ L+
      outerMixedTestBudget C θ L*(7*C^3+mixedMassBudget C L*outerMixedSizeBudget C θ L) ≤ θ := by
  let B := mixedMassBudget C L
  have hB : 0 ≤ B := by dsimp only [B,mixedMassBudget]; positivity
  have hC3 : 0 ≤ C^3 := pow_nonneg hC _
  have hd : 0 < outerMixedSizeBudget C θ L := lt_min (by norm_num) (by positivity)
  have hr : 0 < outerMixedTestBudget C θ L := lt_min (by norm_num) (by positivity)
  have hd1 : outerMixedSizeBudget C θ L ≤ 1 := min_le_left _ _
  have hr1 : outerMixedTestBudget C θ L ≤ 1 := min_le_left _ _
  have hdCap := (le_div_iff₀ (by positivity : 0 < 4*(B+1))).mp
    (show outerMixedSizeBudget C θ L ≤ θ/(4*(B+1)) from min_le_right _ _)
  have hrCap := (le_div_iff₀ (by positivity : 0 < 4*(7*C^3+B+1))).mp
    (show outerMixedTestBudget C θ L ≤ θ/(4*(7*C^3+B+1)) from min_le_right _ _)
  have hBd := mul_le_mul_of_nonneg_left hd1 hB
  have hPay := mul_le_mul_of_nonneg_left hBd hr.le
  refine ⟨by unfold outerMixedCountBudget; positivity,hd,hd1,hr,hr1,?_⟩
  change θ/4+B*outerMixedSizeBudget C θ L+
    outerMixedTestBudget C θ L*(7*C^3+B*outerMixedSizeBudget C θ L) ≤ θ
  nlinarith only [hdCap,hrCap,hPay,hd.le,hr.le,hθ]

def adaptiveOuterRate (legacy cost τ β δ bankCost bankSize : ℝ) : ℝ :=
  min legacy (min (τ/(8*(cost+1)))
    (min (β/(3*(bankCost+1))) (δ/(2*(bankSize+1)))))

theorem adaptiveOuterRate_spec (legacy cost τ β δ bankCost bankSize : ℝ)
    (hLegacy : 0 < legacy) (hCost : 0 ≤ cost) (hτ : 0 < τ)
    (hβ : 0 < β) (hδ : 0 < δ) (hBank : 0 ≤ bankCost) (hSize : 0 ≤ bankSize) :
    0 < adaptiveOuterRate legacy cost τ β δ bankCost bankSize ∧
    adaptiveOuterRate legacy cost τ β δ bankCost bankSize ≤ legacy ∧
    8*cost*adaptiveOuterRate legacy cost τ β δ bankCost bankSize ≤ τ ∧
    3*bankCost*adaptiveOuterRate legacy cost τ β δ bankCost bankSize ≤ β ∧
    2*bankSize*adaptiveOuterRate legacy cost τ β δ bankCost bankSize ≤ δ := by
  let q := adaptiveOuterRate legacy cost τ β δ bankCost bankSize
  have hq : 0 < q := by dsimp only [q,adaptiveOuterRate]; positivity
  have hqτ : q ≤ τ/(8*(cost+1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hqβ : q ≤ β/(3*(bankCost+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hqδ : q ≤ δ/(2*(bankSize+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hτPay := (le_div_iff₀ (by positivity : 0 < 8*(cost+1))).mp hqτ
  have hβPay := (le_div_iff₀ (by positivity : 0 < 3*(bankCost+1))).mp hqβ
  have hδPay := (le_div_iff₀ (by positivity : 0 < 2*(bankSize+1))).mp hqδ
  exact ⟨hq,min_le_left _ _,by nlinarith only [hτPay,hq],
    by nlinarith only [hβPay,hq],by nlinarith only [hδPay,hq]⟩

theorem terminal_below_fourth_root (n t : ℕ) (hOrder : t^4 ≤ n) :
    t ≤ Nat.sqrt (Nat.sqrt n) := by
  apply Nat.le_sqrt'.mpr
  apply Nat.le_sqrt'.mpr
  convert hOrder using 1 <;> ring

#print axioms commonProfileBudget
#print axioms commonProfileBudget_pos
#print axioms common_profile_caps
#print axioms outerMixedCountBudget
#print axioms outerMixedSizeBudget
#print axioms outerMixedTestBudget
#print axioms outer_mixed_budgets
#print axioms adaptiveOuterRate
#print axioms adaptiveOuterRate_spec
#print axioms terminal_below_fourth_root
end TypedTriangle.Pasch
