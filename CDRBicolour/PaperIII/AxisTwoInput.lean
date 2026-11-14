/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.PaperIII.CapTwo
public import CDRBicolour.PaperIII.AxisSixInput
public import CDRBicolour.PaperIII.Four
public import CDRBicolour.PaperIII.LPSeedExample
public import CDRBicolour.PaperIII.Main

/-!
# A fixed integer-cap input for four colours

No angular equidistribution theorem is asserted here. These reductions show
that a single fixed cone suffices, and propagate a supplied arithmetic cut-off
to the already explicit combinatorial counting threshold.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.PaperIII
open Finset CDRBicolour.KBicolor

/-- The original general theorem with its Gale input discharged by the registered proof. -/
theorem bicolourable_eventually_with_registered_gale (hA : ThreeSquaresDense)
    {k : ℕ} (hk : 4≤k) :
    ∃ v₀ : ℕ,∀ v,v₀≤v → Admissible v → Bicolourable v k :=
  bicolourable_eventually galeInt_verified hA hk

theorem conj36_large_with_registered_gale (hA : ThreeSquaresDense) :
    ∃ v₀ : ℕ,∀ v,v₀≤v → Admissible v → Bicolourable v 5 :=
  bicolourable_eventually_with_registered_gale hA (by norm_num)

/-- Every sufficiently large prescribed radius has a representation in one fixed cone. -/
def TwoCapAt (N₀ : ℕ) : Prop :=
  ∀ N : ℕ,N₀≤N → N%8=3 → ∃ a b c : ℤ,
    a^2+b^2+c^2=(N : ℤ) ∧ 2*|b|≤a ∧ 2*|c|≤a

/-- This particular witness is admitted by two and excluded by six. -/
theorem example_cap_two_witness :
    3*((2331 : ℤ)^2+27^2+421^2)=4099*(4099+8) ∧
      2*|(27 : ℤ)|≤2331 ∧ 2*|(421 : ℤ)|≤2331 ∧ 2331<6*|(421 : ℤ)| := by
  norm_num

theorem example_cap_two_representation : CapRepTwo 4099 := by
  exact ⟨2331,27,421,by norm_num⟩

theorem threeSquaresDense_supplies_two_cap (hA : ThreeSquaresDense) :
    ∃ N₀ : ℕ,TwoCapAt N₀ := by
  obtain ⟨N₀,hN⟩ := hA ![1,0,0] (by simp [Fin.sum_univ_three]) (1/3) (by norm_num)
  refine ⟨N₀,fun N hlarge hmod => ?_⟩
  obtain ⟨x,hx,hxu⟩ := hN N hlarge hmod
  have h0 := hxu 0
  have h1 := hxu 1
  have h2 := hxu 2
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.tail_cons,mul_one,mul_zero,sub_zero] at h0 h1 h2
  have hs := Real.sqrt_nonneg (N : ℝ)
  have h0a := (abs_le.mp h0).1
  refine ⟨x 0,x 1,x 2,?_,?_,?_⟩
  · simpa only [Fin.sum_univ_three] using hx
  · have hh : (2 : ℝ)*|((x 1 : ℤ) : ℝ)|≤((x 0 : ℤ) : ℝ) := by linarith
    exact_mod_cast hh
  · have hh : (2 : ℝ)*|((x 2 : ℤ) : ℝ)|≤((x 0 : ℤ) : ℝ) := by linarith
    exact_mod_cast hh

theorem cap_two_of_radius_cap {N₀ v : ℕ} (hA : TwoCapAt N₀)
    (hv : N₀≤v) (hadm : Admissible v) : CapRepTwo v := by
  obtain ⟨h3,h8⟩ := vv8_facts hadm
  set N := v*(v+8)/3
  have hN3 : 3*N=v*(v+8) := by omega
  have hN8 : N%8=3 := by omega
  have hNv : v≤N := by nlinarith
  obtain ⟨a,b,c,he,hb,hc⟩ := hA N (hv.trans hNv) hN8
  have hz : (3 : ℤ)*N=(v : ℤ)*(v+8) := by exact_mod_cast hN3
  exact ⟨a,b,c,by nlinarith,hb,hc⟩

theorem cap_two_eventually_of_radius_caps (hA : ∃ N₀ : ℕ,TwoCapAt N₀) :
    ∃ V₀ : ℕ,∀ v,V₀≤v → (v%6=1 ∨ v%6=3) → CapRepTwo v := by
  obtain ⟨N₀,hN⟩ := hA
  exact ⟨N₀,fun _ hv hadm => cap_two_of_radius_cap hN hv hadm⟩

theorem conj35_large_of_two_radius_caps (hA : ∃ N₀ : ℕ,TwoCapAt N₀) :
    ∃ V₀ : ℕ,∀ v,V₀≤v → Admissible v → Bicolourable v 4 :=
  conj35_large_of_cap_two (cap_two_eventually_of_radius_caps hA)

/-- An effective arithmetic radius cut-off gives a specified final counting cut-off. -/
theorem sharp_counting_at_two_cap_threshold {N₀ : ℕ} (hA : TwoCapAt N₀)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : max N₀ (capTwoCountingThreshold ε)≤v)
    (hadm : Admissible v) :
    ∃ lab : Fin v → Fin 4,(∀ X,0<ksz lab X) ∧ 0<kCount lab ∧
      (1/6-ε)*(v : ℝ)^2*Real.log v≤Real.log (kCount lab) ∧
      Real.log (kCount lab)≤(1/6+ε)*(v : ℝ)^2*Real.log v := by
  exact sharp_counting_of_cap_two hε ((le_max_right _ _).trans hv) hadm
    (cap_two_of_radius_cap hA ((le_max_left _ _).trans hv) hadm)

end CDRBicolour.PaperIII
