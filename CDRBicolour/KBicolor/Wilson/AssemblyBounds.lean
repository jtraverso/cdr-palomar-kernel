/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.OptimizedLocalSeed

/-!
# Uniform constants for summing the Wilson local seeds

The diffuse constant is independent of the host order and of its pattern size.
The floor lemma supplies explicit sufficient sizes for the existing inverse.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset

def globalSeedConstant (g η δ : ℝ) : ℝ :=
  max (4/η) (g*(g+1)*(4/δ+η/(2*g)))

def localInverseConstant {k : ℕ} (o : Fin k) (R : ℝ) : ℝ :=
  (#(Trip o) : ℝ)*(400*R^5*R*(1+4*R^2))

theorem global_seed_constant_bounds {g x y η δ n N : ℝ}
    (hg : 1 ≤ g) (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x)
    (hη : 0 < η) (hδ : 0 < δ) (hn : 0 < n)
    (hmass : g*x+y=1) (hN : N=(x+y)*n) :
    0 < globalSeedConstant g η δ ∧
      1/(globalSeedConstant g η δ*n) ≤ η/(2*g*N) ∧
      g*max ((4/δ+η/(2*g))/N) 0 ≤ globalSeedConstant g η δ/n := by
  have hg0 : 0 < g := by linarith
  have hN0 : 0 < N := by rw [hN]; positivity
  have hC0 : 0 < globalSeedConstant g η δ :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hH0 : 0 < 4/δ+η/(2*g) := by positivity
  have hηC : 4 ≤ η*globalSeedConstant g η δ := by
    have hh := le_max_left (4/η) (g*(g+1)*(4/δ+η/(2*g)))
    change 4 ≤ η*max (4/η) (g*(g+1)*(4/δ+η/(2*g)))
    nlinarith [(div_le_iff₀ hη).mp hh]
  have hNupper : g*N ≤ 2*n := by
    rw [hN]
    have hh : g*(x+y) ≤ 2 := by
      nlinarith [mul_nonneg hg0.le (sub_nonneg.mpr hyx)]
    nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hh)]
  have hNlower : n ≤ (g+1)*N := by
    rw [hN]
    have hh : 1 ≤ (g+1)*(x+y) := by nlinarith [mul_nonneg hg0.le hy]
    nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hh)]
  refine ⟨hC0,?_,?_⟩
  · apply (div_le_div_iff₀ (mul_pos hC0 hn) (by positivity : 0 < 2*g*N)).mpr
    nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hηC)]
  · rw [max_eq_left (by positivity : 0 ≤ (4/δ+η/(2*g))/N),← mul_div_assoc]
    apply (div_le_div_iff₀ hN0 hn).mpr
    have hCH : g*(g+1)*(4/δ+η/(2*g)) ≤ globalSeedConstant g η δ := le_max_right _ _
    nlinarith [mul_nonneg hN0.le (sub_nonneg.mpr hCH),
      mul_nonneg (mul_pos hg0 hH0).le (sub_nonneg.mpr hNlower)]

theorem scaled_group_discrepancy {m c N t n ξ : ℝ} (hN : 0 < N) (hn : 0 < n)
    (ht : 0 ≤ t) (hclose : |m/N-c/n| ≤ ξ) :
    |m*t-(N*t/n)*c| ≤ N*t*ξ := by
  have hid : m*t-(N*t/n)*c = (N*t)*(m/N-c/n) := by field_simp <;> ring
  rw [hid,abs_mul,abs_of_nonneg (mul_nonneg hN.le ht)]
  exact mul_le_mul_of_nonneg_left hclose (mul_nonneg hN.le ht)

def inverseFloorMinimum (δ : ℝ) : ℕ := max 512 ⌈64*(8/δ)^3⌉₊

theorem inverse_floor_parameters {δ B : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 8)
    (hsize : 2*((inverseFloorMinimum δ : ℝ)+1) ≤ δ*B) :
    let m : ℕ := ⌊δ*B/2⌋₊
    1 ≤ 8/δ ∧ 512 ≤ m ∧ 64*(8/δ)^3 ≤ m ∧
      (m : ℝ) ≤ δ*B/2 ∧ 2*B ≤ (8/δ)*m := by
  intro m
  have hM512 : 512 ≤ inverseFloorMinimum δ := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ inverseFloorMinimum δ := by positivity
  have hDB : 0 ≤ δ*B/2 := by linarith
  have hfloor : (m : ℝ) ≤ δ*B/2 := Nat.floor_le hDB
  have hM : inverseFloorMinimum δ ≤ m := (Nat.le_floor_iff hDB).mpr (by linarith)
  have hm512 : 512 ≤ m := hM512.trans hM
  have hR : 1 ≤ 8/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hmR : 64*(8/δ)^3 ≤ m := calc
    _ ≤ ((⌈64*(8/δ)^3⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    _ ≤ (inverseFloorMinimum δ : ℝ) := by
      exact_mod_cast (show ⌈64*(8/δ)^3⌉₊ ≤ inverseFloorMinimum δ from le_max_right _ _)
    _ ≤ (m : ℝ) := by exact_mod_cast hM
  have hfloorgap : δ*B/2 < (m : ℝ)+1 := Nat.lt_floor_add_one _
  have hM512R : (512 : ℝ) ≤ inverseFloorMinimum δ := by exact_mod_cast hM512
  have hquarter : δ*B/4 ≤ (m : ℝ) := by linarith
  have hbal : 2*B ≤ (8/δ)*m := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hδ).mpr
    linarith
  exact ⟨hR,hm512,hmR,hfloor,hbal⟩

end CDRBicolour.KBicolor.Wilson
