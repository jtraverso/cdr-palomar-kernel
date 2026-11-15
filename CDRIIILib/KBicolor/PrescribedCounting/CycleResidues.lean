/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib.Tactic

/-! # Two unit switches per cycle coordinate suffice modulo three -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.PrescribedCounting
open Finset Classical

theorem residue_switch_numbers {J : Type*} (r t : J → ℤ) :
    ∃ N : J → ℕ, (∀ i, N i≤2) ∧ ∀ i, 3∣(r i-(N i:ℤ)-t i) := by
  let N : J → ℕ := fun i => ((r i-t i)%3).toNat
  have hN : ∀ i, ((N i:ℕ):ℤ)=(r i-t i)%3 := by
    intro i
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  refine ⟨N,fun i => ?_,fun i => ?_⟩
  · have hh := Int.emod_lt_of_pos (r i-t i) (by norm_num : (0:ℤ)<3)
    have hzero := Int.emod_nonneg (r i-t i) (by norm_num : (3:ℤ)≠0)
    have hhN := hN i
    omega
  · rw [hN]
    apply Int.dvd_of_emod_eq_zero
    omega

theorem all_entries_divisible_of_cycle_entries {k : ℕ} (o : Fin k)
    (z : Fin k → Fin k → ℤ) (hdiag : ∀ i, z i i=0)
    (hanti : ∀ i j, z i j= -z j i) (hrow : ∀ i, ∑ j, z i j=0)
    (hfree : ∀ i j, i≠o → j≠o → i≠j → 3∣z i j) :
    ∀ i j, 3∣z i j := by
  have hroot : ∀ i, i≠o → 3∣z i o := by
    intro i hio
    have hs : 3∣∑ j ∈ univ.erase o, z i j := by
      apply dvd_sum
      intro j hj
      have hjo : j≠o := (mem_erase.mp hj).1
      by_cases hij : i=j
      · subst j; simp [hdiag]
      · exact hfree i j hio hjo hij
    have he : z i o + ∑ j ∈ univ.erase o, z i j=0 := by
      rw [add_sum_erase _ _ (mem_univ o),hrow]
    have hz : z i o= -(∑ j ∈ univ.erase o, z i j) := by linarith
    rw [hz]
    exact dvd_neg.mpr hs
  intro i j
  by_cases hij : i=j
  · subst j; simp [hdiag]
  by_cases hio : i=o
  · subst i
    rw [hanti]
    exact dvd_neg.mpr (hroot j (Ne.symm hij))
  by_cases hjo : j=o
  · subst j; exact hroot i hio
  exact hfree i j hio hjo hij

end CDRBicolour.KBicolor.PrescribedCounting
