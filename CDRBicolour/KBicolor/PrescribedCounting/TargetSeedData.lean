/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.ExactSeedK

/-! # The original interior target supplies the robust seed data -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical
variable {n k : ℕ}

theorem seedData_from_interior_target (lab : Fin n → Fin k) {δ ζ : ℝ}
    (hδ : 0 < δ) (hζ : 0 < ζ) (hn : 0 < n) (hcls : ∀ i, δ*n ≤ ksz lab i)
    (t : Fin k → Fin k → ℕ)
    (hpair : ∀ i j, i ≠ j → 2*(t i j+t j i)=ksz lab i*ksz lab j)
    (hrow : ∀ i, 2*∑ j ∈ univ.filter (fun j => j ≠ i), t i j=ksz lab i*(ksz lab i-1))
    (hlow : ∀ i j, i ≠ j → ζ*(n : ℝ)^2 ≤ t i j) :
    ∃ a, SeedData (ksz lab) ζ a := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : ∀ i, 0 < ksz lab i := by
    intro i
    have hh := lt_of_lt_of_le (mul_pos hδ hnR) (hcls i)
    exact_mod_cast hh
  have hcN : ∀ i, (ksz lab i : ℝ) ≤ n := by
    intro i
    have hh := card_le_univ ((univ : Finset (Fin n)).filter fun v => lab v=i)
    simpa only [Fintype.card_fin,ksz] using (Nat.cast_le.mpr hh :
      ((#(univ.filter fun v : Fin n => lab v=i) : ℕ) : ℝ) ≤ Fintype.card (Fin n))
  refine ⟨_,seedData_of_targetR lab (fun i j => (t i j : ℝ)) hc (fun i j hij => ?_) (fun i => ?_)
    (fun i j hij => ?_)⟩
  · exact_mod_cast hpair i j hij
  · have hh : ((2*∑ j ∈ univ.filter (fun j => j ≠ i), t i j : ℕ) : ℝ)=
        ((ksz lab i*(ksz lab i-1) : ℕ) : ℝ) := by rw [hrow]
    push_cast [Nat.cast_sub (show 1 ≤ ksz lab i by have := hc i; omega)] at hh
    exact hh
  · have hprod : (ksz lab i : ℝ)*ksz lab j ≤ (n : ℝ)^2 := by
      nlinarith [mul_le_mul (hcN i) (hcN j) (Nat.cast_nonneg (ksz lab j)) hnR.le]
    have hh := mul_le_mul_of_nonneg_left hprod hζ.le
    have ht0 : (0 : ℝ) ≤ t i j := Nat.cast_nonneg _
    nlinarith [hlow i j hij]

end CDRBicolour.KBicolor.PrescribedCounting
