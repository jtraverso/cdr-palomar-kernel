module
public import RequestProject.TypedTriangle.PaschRawHostStockRich
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.BasalIncidence
open TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

theorem rawStockProfileMargin_bounds {α : ℝ} (hα : 0 < α) :
    0 < rawStockProfileMargin α ∧ rawStockProfileMargin α ≤ 1/2 := by
  constructor
  · exact lt_min (by positivity) (by norm_num)
  · exact (min_le_right _ _).trans (by norm_num)

/-- The original raw window supplies the actual normalized window on the
returned residual stock host. This is derived data, not an extra stock input. -/
theorem raw_stock_normalized_coefficient_window {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {a b α : ℝ} (ha : 0 < a) (hα : 0 < α)
    (hn : 0 < (Fintype.card V:ℝ))
    (hWindow : ∀ T, IsAllowed H F T →
      a/Fintype.card V ≤ μ T ∧ μ T ≤ b/Fintype.card V)
    (S B : Finset (Sym2 V)) :
    ∀ T, IsAllowed (residual H (S∪B)) F T →
      1/(rawProfileConstant a b*Fintype.card V) ≤ μ T/(1+rawStockProfileMargin α) ∧
        μ T/(1+rawStockProfileMargin α) ≤ rawProfileConstant a b/Fintype.card V := by
  intro T hT
  have hr := rawStockProfileMargin_bounds hα
  exact raw_normalized_coefficient_window ha hr.1.le hr.2 hn
    (hWindow T (isAllowed_mono (subHost_le H _) rfl hT))

/-- The returned raw load window gives positive capped loads for the same
literal normalized profile used by every tuple control in the rich stock. -/
theorem raw_stock_normalized_load_window {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {α : ℝ} (hα : 0 < α) (S B : Finset (Sym2 V))
    (hLoad : ∀ f ∈ edges (residual H (S∪B)),
      |bdry (residual H (S∪B)) F μ f-1| ≤ rawStockProfileMargin α) :
    ∀ f ∈ edges (residual H (S∪B)),
      1-2*rawStockProfileMargin α ≤
        bdry (residual H (S∪B)) F (fun T => μ T/(1+rawStockProfileMargin α)) f ∧
      1/3 ≤ bdry (residual H (S∪B)) F (fun T => μ T/(1+rawStockProfileMargin α)) f ∧
      bdry (residual H (S∪B)) F (fun T => μ T/(1+rawStockProfileMargin α)) f ≤ 1 := by
  intro f hf
  rw [bdry_div_constant]
  have hr := rawStockProfileMargin_bounds hα
  exact raw_normalized_load_window hr.1.le hr.2 (hLoad f hf)

#print axioms rawStockProfileMargin_bounds
#print axioms raw_stock_normalized_coefficient_window
#print axioms raw_stock_normalized_load_window
end TypedTriangle.BasalIncidence
