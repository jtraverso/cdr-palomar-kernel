/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.PaperIII.MeridianMain
public import CDRIIILib.PaperIII.FourSeed70

/-! # The constant-two route with seed margin 1/70 -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.KBicolor
open Finset TypedTriangle

theorem profile_of_cap_two70 {v : ℕ} (hv : 78400≤v)
    (hadm : v%6=1 ∨ v%6=3) (hcap : CapRepTwo v) :
    ∃ cs : Fin 4 → ℕ,(∑ X,cs X=v) ∧
      3*∑ X,cs X*(cs X-1)=v*(v-1) ∧ (∀ X,v≤70*cs X) ∧
      (∀ X Y,X≠Y → Even (cs X*cs Y)) ∧ ∃ a,SeedData cs (1/70) a := by
  obtain ⟨a,b,c,he,hb,hc⟩ := hcap
  have hodd : v%2=1 := by omega
  obtain ⟨cs,hs,hd,hlo,hhi⟩ := split_of_cap_two hv hodd he hb hc
  have hqR := Wilson.profile_square_of_div cs hs hd
  have hqZ : 3*∑ X,(cs X : ℤ)^2=(v : ℤ)^2+2*v := by exact_mod_cast hqR
  exact ⟨cs,hs,hd,hlo,even_products_four cs hodd hs hd,
    CDRBicolour.PaperIII.seed_of_robust_four_profile70 (by omega) cs hs hqZ hlo hhi⟩

def capTwoCountingThreshold70 (ε : ℝ) : ℕ :=
  max 78400 (Wilson.sharpCountThreshold (k := 4) (by norm_num) (1/70) (1/70) ε)

/-- A labelled four-colour profile and both sharp bounds, at a specified threshold. -/
theorem sharp_counting_of_cap_two70 {ε : ℝ} (hε : 0 < ε) {v : ℕ}
    (hv : capTwoCountingThreshold70 ε≤v) (hadm : v%6=1 ∨ v%6=3) (hcap : CapRepTwo v) :
    ∃ lab : Fin v → Fin 4, (∀ X,0<ksz lab X) ∧ 0<kCount lab ∧
      (1/6-ε)*(v : ℝ)^2*Real.log v≤Real.log (kCount lab) ∧
      Real.log (kCount lab)≤(1/6+ε)*(v : ℝ)^2*Real.log v := by
  have hv4 : 78400≤v := (le_max_left _ _).trans hv
  obtain ⟨cs,hs,hd,hlo,heven,hseed⟩ := profile_of_cap_two70 hv4 hadm hcap
  obtain ⟨lab,hlab⟩ := exists_lab cs hs
  have hsize : ksz lab=cs := funext hlab
  have hpos : ∀ X,0<ksz lab X := by
    intro X
    rw [hlab]
    have := hlo X
    omega
  refine ⟨lab,hpos,?_⟩
  apply Wilson.sharp_counting_at_explicit_order (by norm_num : 4≤4)
    (by norm_num : (0 : ℝ)<1/70) (by norm_num : (0 : ℝ)<1/70) hε v lab
    ((le_max_right _ _).trans hv) (show Odd v from ⟨v/2,by omega⟩)
  · simpa only [hsize] using heven
  · simpa only [hsize] using hd
  · intro X
    rw [hlab]
    have hh : (v : ℝ)≤70*(cs X : ℝ) := by exact_mod_cast hlo X
    linarith
  · simpa only [hsize] using hseed

theorem cap_two_bicolourable70 {v : ℕ} (hv : capTwoCountingThreshold70 (1/12)≤v)
    (hadm : v%6=1 ∨ v%6=3) (hcap : CapRepTwo v) :
    CDRBicolour.PaperIII.Bicolourable v 4 := by
  obtain ⟨lab,hpos,hcount,-,-⟩ := sharp_counting_of_cap_two70 (by norm_num : (0 : ℝ)<1/12) hv hadm hcap
  exact bicolourable_of_positive_kCount lab hpos hcount

theorem conj35_large_of_cap_two70
    (hcap : ∃ V₀ : ℕ,∀ v,V₀≤v → (v%6=1 ∨ v%6=3) → CapRepTwo v) :
    ∃ V₀ : ℕ,∀ v,V₀≤v → CDRBicolour.PaperIII.Admissible v →
      CDRBicolour.PaperIII.Bicolourable v 4 := by
  obtain ⟨V₀,hV⟩ := hcap
  refine ⟨max V₀ (capTwoCountingThreshold70 (1/12)),fun v hv hadm => ?_⟩
  exact cap_two_bicolourable70 ((le_max_right _ _).trans hv) hadm
    (hV v ((le_max_left _ _).trans hv) hadm)

end CDRBicolour.KBicolor

namespace CDRBicolour.PaperIII
open CDRBicolour.KBicolor

theorem sharp_counting_at_two_cap_threshold70 {N₀ : ℕ} (hA : TwoCapAt N₀)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : max N₀ (capTwoCountingThreshold70 ε)≤v)
    (hadm : Admissible v) :
    ∃ lab : Fin v → Fin 4,(∀ X,0<ksz lab X) ∧ 0<kCount lab ∧
      (1/6-ε)*(v : ℝ)^2*Real.log v≤Real.log (kCount lab) ∧
      Real.log (kCount lab)≤(1/6+ε)*(v : ℝ)^2*Real.log v := by
  exact sharp_counting_of_cap_two70 hε ((le_max_right _ _).trans hv) hadm
    (cap_two_of_radius_cap hA ((le_max_left _ _).trans hv) hadm)

end CDRBicolour.PaperIII
