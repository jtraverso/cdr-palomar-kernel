/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Tactic

/-! # Choosing a linear-size dyadic reserved block -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.LatinPasch

theorem exists_dyadic_size (a : ℝ) (ha : 0 < a) (R : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ r : ℕ, R ≤ r ∧ a*n/2 < (2^r : ℕ) ∧ ((2^r : ℕ) : ℝ) ≤ a*n := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((2:ℝ)^R/a)
  refine ⟨N,fun n hn => ?_⟩
  have hna : (2:ℝ)^R < a*n := by
    have hNN : (N:ℝ) ≤ n := by exact_mod_cast hn
    have := (div_lt_iff₀ ha).mp hN
    nlinarith
  have hpow1 : (1:ℝ) ≤ 2^R := one_le_pow₀ (by norm_num)
  obtain ⟨r,hr,hnext⟩ := exists_nat_pow_near (le_trans hpow1 hna.le) (show (1:ℝ)<2 by norm_num)
  have hR : R ≤ r := by
    by_contra hlt
    have hp : (2:ℝ)^(r+1) ≤ 2^R := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  refine ⟨r,hR,?_,?_⟩
  · rw [pow_succ] at hnext
    norm_cast at hr ⊢
    exact (by push_cast; linarith : a*(n:ℝ)/2 < ((2^r:ℕ):ℝ))
  · exact_mod_cast hr

end CDRBicolour.KBicolor.LatinPasch
