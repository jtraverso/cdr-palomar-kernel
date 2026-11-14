/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.PaperIII.CapSix
public import CDRBicolour.PaperIII.Four

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

/-- Every sufficiently large prescribed radius has a representation in one fixed cone. -/
def SixCapAt (N₀ : ℕ) : Prop :=
  ∀ N : ℕ,N₀≤N → N%8=3 → ∃ a b c : ℤ,
    a^2+b^2+c^2=(N : ℤ) ∧ 6*|b|≤a ∧ 6*|c|≤a

/-- This particular witness is admitted by six and excluded by seven. -/
theorem example_cap_six_witness :
    3*((2343 : ℤ)^2+9^2+349^2)=4099*(4099+8) ∧
      6*|(9 : ℤ)|≤2343 ∧ 6*|(349 : ℤ)|≤2343 ∧ 2343<7*|(349 : ℤ)| := by
  norm_num

theorem example_cap_six_representation : CapRepSix 4099 := by
  exact ⟨2343,9,349,by norm_num⟩

theorem threeSquaresDense_supplies_six_cap (hA : ThreeSquaresDense) :
    ∃ N₀ : ℕ,SixCapAt N₀ := by
  obtain ⟨N₀,hN⟩ := hA ![1,0,0] (by simp [Fin.sum_univ_three]) (1/7) (by norm_num)
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
  · have hh : (6 : ℝ)*|((x 1 : ℤ) : ℝ)|≤((x 0 : ℤ) : ℝ) := by linarith
    exact_mod_cast hh
  · have hh : (6 : ℝ)*|((x 2 : ℤ) : ℝ)|≤((x 0 : ℤ) : ℝ) := by linarith
    exact_mod_cast hh

theorem cap_six_of_radius_cap {N₀ v : ℕ} (hA : SixCapAt N₀)
    (hv : N₀≤v) (hadm : Admissible v) : CapRepSix v := by
  obtain ⟨h3,h8⟩ := vv8_facts hadm
  set N := v*(v+8)/3
  have hN3 : 3*N=v*(v+8) := by omega
  have hN8 : N%8=3 := by omega
  have hNv : v≤N := by nlinarith
  obtain ⟨a,b,c,he,hb,hc⟩ := hA N (hv.trans hNv) hN8
  have hz : (3 : ℤ)*N=(v : ℤ)*(v+8) := by exact_mod_cast hN3
  exact ⟨a,b,c,by nlinarith,hb,hc⟩

theorem cap_six_eventually_of_radius_caps (hA : ∃ N₀ : ℕ,SixCapAt N₀) :
    ∃ V₀ : ℕ,∀ v,V₀≤v → (v%6=1 ∨ v%6=3) → CapRepSix v := by
  obtain ⟨N₀,hN⟩ := hA
  exact ⟨N₀,fun _ hv hadm => cap_six_of_radius_cap hN hv hadm⟩

theorem conj35_large_of_radius_caps (hA : ∃ N₀ : ℕ,SixCapAt N₀) :
    ∃ V₀ : ℕ,∀ v,V₀≤v → Admissible v → Bicolourable v 4 :=
  conj35_large_of_cap_six (cap_six_eventually_of_radius_caps hA)

/-- An effective arithmetic radius cut-off gives a specified final counting cut-off. -/
theorem sharp_counting_at_six_cap_threshold {N₀ : ℕ} (hA : SixCapAt N₀)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : max N₀ (capSixCountingThreshold ε)≤v)
    (hadm : Admissible v) :
    ∃ lab : Fin v → Fin 4,(∀ X,0<ksz lab X) ∧ 0<kCount lab ∧
      (1/6-ε)*(v : ℝ)^2*Real.log v≤Real.log (kCount lab) ∧
      Real.log (kCount lab)≤(1/6+ε)*(v : ℝ)^2*Real.log v := by
  exact sharp_counting_of_cap_six hε ((le_max_right _ _).trans hv) hadm
    (cap_six_of_radius_cap hA ((le_max_left _ _).trans hv) hadm)

end CDRBicolour.PaperIII
