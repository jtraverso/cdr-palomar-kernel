/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.PaperIII.SeedGale

/-! # An exact primal and dual LP certificate beyond the closed-form seed -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace CDRBicolour.PaperIII
open Finset CDRBicolour.KBicolor

def lpExampleProfile : Fin 4 → ℕ := ![330,554,1706,1509]

def lpExampleWeights : Fin 4 → Fin 4 → ℝ :=
  ![![0,53/442,58028/710515,58028/710515],
    ![389/442,0,58028/710515,58028/710515],
    ![1-58028/710515,1-58028/710515,0,1903/3215],
    ![1-58028/710515,1-58028/710515,1312/3215,0]]

theorem lp_example_primal : SeedData lpExampleProfile (58028/710515) lpExampleWeights := by
  refine ⟨?_,?_,?_⟩
  · intro X Y h
    fin_cases X <;> fin_cases Y <;> norm_num [lpExampleWeights] at *
  · intro X Y h
    fin_cases X <;> fin_cases Y <;> norm_num [lpExampleWeights] at *
  · intro X
    fin_cases X <;> norm_num [sum_filter,Fin.sum_univ_four,lpExampleWeights,lpExampleProfile]

/-- Summing the two row equations on classes 0 and 1 gives the dual bound. -/
theorem lp_example_margin_upper {η : ℝ} {a : Fin 4 → Fin 4 → ℝ}
    (hs : SeedData lpExampleProfile η a) : η≤58028/710515 := by
  have h0 := hs.2.2 0
  have h1 := hs.2.2 1
  norm_num [sum_filter,Fin.sum_univ_four,lpExampleProfile] at h0 h1
  have hp := hs.1 0 1 (by decide)
  have h02 := hs.2.1 0 2 (by decide)
  have h03 := hs.2.1 0 3 (by decide)
  have h12 := hs.2.1 1 2 (by decide)
  have h13 := hs.2.1 1 3 (by decide)
  linarith only [h0,h1,hp,h02,h03,h12,h13]

theorem lp_example_closed_formula_negative :
    (1/2 : ℝ)+3*((330 : ℝ)-1706)/(2*4099) = -29/8198 := by norm_num

theorem lp_example_margin_stronger : (1/137 : ℝ)<58028/710515 := by norm_num

end CDRBicolour.PaperIII
