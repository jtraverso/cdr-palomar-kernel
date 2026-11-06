module
public import RequestProject.TypedTriangle.PaschRawProfileBounds
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I : Type*} [Fintype V]

/-- A raw coefficient window and H3 give the rounded quadratic target
lower bound. The allowed-root witness is local to this auxiliary lemma. -/
theorem floor_target_lower_of_coefficient_window {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {α C : ℝ} (hH3 : CommonNbrCond H F α)
    (hα : 0 < α) (hC : 1 ≤ C)
    (hLow : ∀ T, IsAllowed H F T → 1/(C*Fintype.card V) ≤ μ T)
    (hUp : ∀ T, IsAllowed H F T → μ T ≤ C/Fintype.card V)
    (hN : max (supersaturationOrder α) ⌈2*C⌉₊ ≤ Fintype.card V)
    {x y z : V} (hRoot : IsAllowed H F {x,y,z}) :
    (massConstant α C/16)*(Fintype.card V:ℝ)^2 ≤
      target (floorWeights (allowed H F) μ (Fintype.card V:ℝ)) (allowed H F) := by
  let A := allowed H F
  let n := (Fintype.card V:ℝ)
  change (massConstant α C/16)*n^2 ≤ target (floorWeights A μ n) A
  have hNS : supersaturationOrder α ≤ Fintype.card V := (le_max_left _ _).trans hN
  have hnNat : 0 < Fintype.card V := by
    have hh : 6 ≤ Fintype.card V := (le_max_left _ _).trans hNS
    omega
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast hnNat
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hRound : 2*C ≤ n := Nat.ceil_le.mp ((le_max_right _ _).trans hN)
  have hSource : massConstant α C*n^2 ≤ target μ A :=
    target_lower_of_coefficient_window hLow hH3 hα hC0 hNS hRoot
  have hSource0 : 0 ≤ target μ A :=
    (by unfold massConstant; positivity : (0:ℝ) ≤ massConstant α C*n^2).trans hSource
  have hRounded := floorWeights_target_lower A μ hC0 hn
    (by linarith only [hRound,hC0]) (fun T hT => hLow T (isAllowed_of_mem_allowed hT))
  have hFactor := fourth_rounding_factor_lower
    ((div_le_iff₀ hn).mpr (by linarith only [hRound]) : C/n ≤ (1/2:ℝ))
  have h1 := mul_le_mul_of_nonneg_right hFactor hSource0
  have h2 := div_le_div_of_nonneg_right hSource (by norm_num : (0:ℝ) ≤ 16)
  nlinarith only [h1,h2,hRounded]

/-- The nonempty root family in an actual tuple-degree test supplies the
allowed triangle; no root is added as a final host hypothesis. -/
theorem floor_target_lower_of_nonempty_index_family {H : Host V I} {F : Set (Multiset I)}
    {μ : Finset V → ℝ} {α C : ℝ} (hH3 : CommonNbrCond H F α)
    (hα : 0 < α) (hC : 1 ≤ C)
    (hLow : ∀ T, IsAllowed H F T → 1/(C*Fintype.card V) ≤ μ T)
    (hUp : ∀ T, IsAllowed H F T → μ T ≤ C/Fintype.card V)
    (hN : max (supersaturationOrder α) ⌈2*C⌉₊ ≤ Fintype.card V)
    (R : Finset (allowed H F)) (hR : R.Nonempty) :
    (massConstant α C/16)*(Fintype.card V:ℝ)^2 ≤
      target (floorWeights (allowed H F) μ (Fintype.card V:ℝ)) (allowed H F) := by
  obtain ⟨i,_⟩ := hR
  have hAllow := isAllowed_of_mem_allowed i.property
  obtain ⟨x,y,z,_,_,_,hEq⟩ := card_eq_three.mp hAllow.1
  exact floor_target_lower_of_coefficient_window hH3 hα hC hLow hUp hN (hEq ▸ hAllow)

#print axioms floor_target_lower_of_coefficient_window
#print axioms floor_target_lower_of_nonempty_index_family
end TypedTriangle.Pasch
