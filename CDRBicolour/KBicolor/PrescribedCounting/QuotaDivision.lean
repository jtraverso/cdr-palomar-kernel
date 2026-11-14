/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.PrescribedCounting.TournamentSplit

/-! # Exact cross quotas after the residual congruences have been corrected -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical
variable {k : ℕ}

theorem divide_cross_quotas (h : ℕ) (b : Fin k → ℕ) (q : Fin k → Fin k → ℕ)
    (hdiag : ∀ i, q i i=0) (hdiv : ∀ i j, 3∣q i j)
    (hpair : ∀ i j, i≠j → q i j+q j i=3*(h*(b i*b j)))
    (hrow : ∀ i, ∑ j, q i j=3*(h*(b i*b i))) :
    ∃ y : Fin h → Fin k → Fin k → ℕ,
      (∀ t, Pattern.IsTour b (y t)) ∧ (∀ i j, ∑ t, 3*y t i j=q i j) := by
  let x : Fin k → Fin k → ℕ := fun i j => q i j/3
  have hmul : ∀ i j, 3*x i j=q i j := fun i j => Nat.mul_div_cancel' (hdiv i j)
  have hxdiag : ∀ i, x i i=0 := by intro i; simp [x,hdiag]
  have hxpair : ∀ i j, i≠j → x i j+x j i=h*(b i*b j) := by
    intro i j hij
    have hh := hpair i j hij
    rw [← hmul i j,← hmul j i] at hh
    omega
  have hxrow : ∀ i, ∑ j, x i j=h*(b i*b i) := by
    intro i
    have hh := hrow i
    simp_rw [← hmul i] at hh
    rw [← mul_sum] at hh
    omega
  obtain ⟨y,hy,hys⟩ := split_scaled_tournament h b x hxdiag hxpair hxrow
  refine ⟨y,hy,fun i j => ?_⟩
  rw [← mul_sum,hys,hmul]

end CDRBicolour.KBicolor.PrescribedCounting
