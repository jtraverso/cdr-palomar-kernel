/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.PaperIII.Bridge

/-!
# The seed from Gale's feasibility theorem (integer data)

For an integer split `c` of `v` with the divisibility identity, put `t = a - 1/2` and
`F X Y = 2M · c X · c Y · t X Y`. The seed equations become: `F` antisymmetric, net outflow
`d X = M · c X · (3 c X - v - 2)` (`Σ d = 0` by divisibility), and the bound `a ≥ 1/M` becomes
`F ≤ (M - 2) c X c Y`. By Gale (integer version, `GaleInt`) such `F` exists iff every set of
classes `S` satisfies `Σ_S d ≤ Σ_{S × Sᶜ} (M - 2) c X c Y`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.PaperIII

open Finset CDRBicolour.KBicolor

/-- **Seed from Gale.** -/
theorem seed_of_gale (hG : GaleInt) {k : ℕ} (c : Fin k → ℕ) {v M : ℕ} (hM : 3 ≤ M)
    (hc1 : ∀ X, 1 ≤ c X) (hs : ∑ X, c X = v)
    (hq : 3 * ∑ X, ((c X : ℤ)) ^ 2 = (v : ℤ) ^ 2 + 2 * v)
    (hcut : ∀ S : Finset (Fin k), ∑ X ∈ S, (M : ℤ) * c X * (3 * c X - v - 2) ≤
      ∑ X ∈ S, ∑ Y ∈ Sᶜ, ((M : ℤ) - 2) * c X * c Y) :
    ∃ a, SeedData c (1 / (M : ℝ)) a := by
  classical
  set d : Fin k → ℤ := fun X => (M : ℤ) * c X * (3 * c X - v - 2) with hd
  set cap : Fin k → Fin k → ℤ := fun X Y => ((M : ℤ) - 2) * c X * c Y with hcap
  have hcap0 : ∀ X Y, 0 ≤ cap X Y := fun X Y => by
    simp only [hcap]; have : (2 : ℤ) ≤ M := by exact_mod_cast (by omega : 2 ≤ M)
    positivity
  have hsZ : ∑ X, (c X : ℤ) = v := by exact_mod_cast hs
  have hd0 : ∑ X, d X = 0 := by
    simp only [hd]
    have : ∑ X, (M : ℤ) * c X * (3 * c X - v - 2) =
        (M : ℤ) * (3 * ∑ X, ((c X : ℤ)) ^ 2 - (v + 2) * ∑ X, (c X : ℤ)) := by
      rw [mul_sum, Finset.mul_sum, ← sum_sub_distrib, mul_sum]
      exact sum_congr rfl fun X _ => by ring
    rw [this, hq, hsZ]; ring
  obtain ⟨f, hanti, hle, hrow⟩ := (hG (Fin k) cap hcap0 d hd0).2 hcut
  have hf0 : ∀ X, f X X = 0 := fun X => by have := hanti X X; linarith
  have hcR : ∀ X, (0 : ℝ) < c X := fun X => by exact_mod_cast (hc1 X)
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  refine ⟨fun X Y => 1 / 2 + (f X Y : ℝ) / (2 * M * c X * c Y), fun X Y _ => ?_,
    fun X Y h => ?_, fun X => ?_⟩
  · have := hanti X Y
    have h1 : (f Y X : ℝ) = -(f X Y : ℝ) := by rw [this]; push_cast; ring
    simp only
    rw [h1]
    have := hcR X; have := hcR Y
    field_simp; ring
  · -- `a X Y = 1/2 - f Y X / (2 M c c) ≥ 1/2 - (M - 2)/(2M) = 1/M`
    have hYX : (f Y X : ℝ) ≤ ((M : ℝ) - 2) * c Y * c X := by
      have := hle Y X; simp only [hcap] at this; exact_mod_cast this
    have h1 : (f X Y : ℝ) = -(f Y X : ℝ) := by rw [hanti X Y]; push_cast; ring
    simp only
    rw [h1]
    have hX := hcR X; have hY := hcR Y
    have key : -(f Y X : ℝ) / (2 * M * c X * c Y) ≥ -(((M : ℝ) - 2) / (2 * M)) := by
      rw [ge_iff_le, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hX hY]
    have : (1 : ℝ) / M = 1 / 2 - ((M : ℝ) - 2) / (2 * M) := by field_simp; ring
    rw [this]; linarith
  · -- rows
    have hX := hcR X
    have e : ∀ Y ∈ univ.filter (fun Y => Y ≠ X),
        (c Y : ℝ) * (1 / 2 + (f X Y : ℝ) / (2 * M * c X * c Y)) =
          (c Y : ℝ) / 2 + (f X Y : ℝ) / (2 * M * c X) := by
      intro Y _; have := hcR Y; field_simp
    rw [sum_congr rfl e, sum_add_distrib, ← sum_div, ← sum_div, Finset.filter_ne',
      Finset.sum_erase_eq_sub (mem_univ X), Finset.sum_erase_eq_sub (mem_univ X)]
    have hrowR : ∑ Y, (f X Y : ℝ) = (d X : ℝ) := by exact_mod_cast hrow X
    have hsR : ∑ Y, (c Y : ℝ) = v := by exact_mod_cast hs
    rw [hrowR, hsR, show ((f X X : ℤ) : ℝ) = 0 by rw [hf0 X]; simp]
    simp only [hd]; push_cast
    field_simp
    ring

end CDRBicolour.PaperIII
