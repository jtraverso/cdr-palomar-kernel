/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module
public import CDRBicolour.KBicolor.LatinMixedAverage

/-! # The quadratic mixed error is smaller than the cubic internal gap -/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CDRBicolour.KBicolor.LatinPasch

theorem mixed_budget_small {a P : ℝ} {n m : ℕ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hP : 0 < P) (hn : 0 < n) (hm : 2 ≤ m)
    (hsize : a*n/2 ≤ m) (hlarge : 4096*P < a^5*n) :
    mixedBudget n m < (m:ℝ)^3/(4*P) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ)< m := by linarith
  have hden : ((m*(m-1):ℕ):ℝ) = (m:ℝ)*((m:ℝ)-1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1≤ m), Nat.cast_one]
  have hd0 : (0:ℝ)<(m:ℝ)*((m:ℝ)-1) := mul_pos hm0 (by linarith)
  have hs2 : (a*(n:ℝ)/2)^2 ≤ (m:ℝ)^2 := by gcongr
  have hs3 : (a*(n:ℝ)/2)^3 ≤ (m:ℝ)^3 := by gcongr
  have hfirst : 27*(n:ℝ)^3/m ≤ 54*(n:ℝ)^2/a := by
    apply (div_le_div_iff₀ hm0 ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsize (sq_nonneg (n:ℝ))]
  have hsecond : 6*(n:ℝ)^4/((m:ℝ)*((m:ℝ)-1)) ≤ 48*(n:ℝ)^2/a^2 := by
    apply (div_le_div_iff₀ hd0 (sq_pos_of_pos ha)).mpr
    have hd : a^2*(n:ℝ)^2 ≤ 8*((m:ℝ)*((m:ℝ)-1)) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hd (sq_nonneg (n:ℝ))]
  have hsum : mixedBudget n m ≤ 102*(n:ℝ)^2/a^2 := by
    unfold mixedBudget
    rw [hden]
    have he : 54*(n:ℝ)^2/a ≤ 54*(n:ℝ)^2/a^2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    calc
      _ ≤ 54*(n:ℝ)^2/a + 48*(n:ℝ)^2/a^2 := add_le_add hfirst hsecond
      _ ≤ 54*(n:ℝ)^2/a^2 + 48*(n:ℝ)^2/a^2 := add_le_add he (le_refl _)
      _ = _ := by ring
  have hg : 102*(n:ℝ)^2/a^2 < a^3*(n:ℝ)^3/(32*P) := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos ha) (by positivity : 0<32*P)).mpr
    have hh : 3264*P < a^5*(n:ℝ) := by linarith
    have hh' := mul_lt_mul_of_pos_right hh (sq_pos_of_pos hnR)
    nlinarith only [hh']
  have hgap : a^3*(n:ℝ)^3/(32*P) ≤ (m:ℝ)^3/(4*P) := by
    apply (div_le_div_iff₀ (by positivity : 0<32*P) (by positivity : 0<4*P)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hs3 hP.le]
  exact hsum.trans_lt (hg.trans_le hgap)

end CDRBicolour.KBicolor.LatinPasch
