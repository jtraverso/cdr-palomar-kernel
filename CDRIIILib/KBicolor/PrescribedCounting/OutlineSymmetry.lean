/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRIIILib.KBicolor.Pattern.Outline

/-! # Why cross-table type counts have a genuine factor of three -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical
variable {k : ℕ}

theorem sum_two_supported (f : Fin k → ℕ) {a b : Fin k} (hab : a≠b)
    (hz : ∀ z, z≠a → z≠b → f z=0) : ∑ z, f z=f a+f b := by
  have hh : ∑ z ∈ ({a,b}:Finset (Fin k)), f z=∑ z, f z := by
    apply sum_subset (subset_univ _)
    intro z _ hz'
    simp only [mem_insert,mem_singleton,not_or] at hz'
    exact hz z hz'.1 hz'.2
  rw [sum_pair hab] at hh
  exact hh.symm

theorem bicoloured_outline_symmetric (b : Fin k → ℕ) (M : Fin k → Fin k → Fin k → ℕ)
    (h₁ : ∀ r c, ∑ s, M r c s=b r*b c)
    (h₂ : ∀ r s, ∑ c, M r c s=b r*b s)
    (h₃ : ∀ c s, ∑ r, M r c s=b c*b s)
    (h₀ : ∀ r c s, ¬Pattern.bic r c s → M r c s=0)
    {X Y : Fin k} (hXY : X≠Y) :
    M X X Y=M X Y X ∧ M X X Y=M Y X X ∧
      M X X Y+M X Y X+M Y X X=3*M X X Y := by
  have hp : M X Y X+M X Y Y=b X*b Y := by
    rw [← h₁ X Y]
    symm
    apply sum_two_supported _ hXY
    intro z hzX hzY
    apply h₀
    simp only [Pattern.bic]
    tauto
  have hq : M X X Y+M X Y Y=b X*b Y := by
    rw [← h₂ X Y]
    symm
    apply sum_two_supported _ hXY
    intro z hzX hzY
    apply h₀
    simp only [Pattern.bic]
    tauto
  have hr : M X X Y+M Y X Y=b X*b Y := by
    rw [← h₃ X Y]
    symm
    apply sum_two_supported _ hXY
    intro z hzX hzY
    apply h₀
    simp only [Pattern.bic]
    tauto
  have hs : M Y X X+M Y X Y=b Y*b X := by
    rw [← h₁ Y X]
    symm
    apply sum_two_supported _ hXY
    intro z hzX hzY
    apply h₀
    simp only [Pattern.bic]
    tauto
  rw [Nat.mul_comm (b Y) (b X)] at hs
  omega

end CDRBicolour.KBicolor.PrescribedCounting
