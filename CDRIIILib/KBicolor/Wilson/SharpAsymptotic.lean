/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.SharpCounting
public import CDRIIILib.KBicolor.Counting

/-!
# Matching sharp bounds for robust k-colour profiles

Wilson supplies the lower bound and the existing Linial-Luria theorem supplies
the upper bound. Both bounds refer to the same fixed labelled profile.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset

theorem sharp_counting {k : ℕ} (hk : 4 ≤ k) {δ η ε : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n →
      Odd n → (∀ X Y, X ≠ Y → Even (ksz lab X*ksz lab Y)) →
      3*∑ X,ksz lab X*(ksz lab X-1)=n*(n-1) →
      (∀ X,δ*n ≤ ksz lab X) → (∃ a,SeedData (ksz lab) η a) →
      0 < kCount lab ∧
      (1/6-ε)*(n : ℝ)^2*Real.log n ≤ Real.log (kCount lab) ∧
      Real.log (kCount lab) ≤ (1/6+ε)*(n : ℝ)^2*Real.log n := by
  let ε' := min ε (1/12)
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'12 : ε' ≤ 1/12 := min_le_right _ _
  obtain ⟨nL,hL⟩ := sharp_counting_lower hk hδ hη hε'
  refine ⟨max nL 360004,fun n lab hn hodd heven hdiv hcls hseed => ?_⟩
  have hnL : nL ≤ n := (le_max_left _ _).trans hn
  have hnlarge : 360004 ≤ n := (le_max_right _ _).trans hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos hnR
  have hcoef : 0 < 1/6-ε' := by linarith
  have hlo := hL n lab hnL hodd heven hdiv hcls hseed
  have hlogpos : 0 < Real.log (kCount lab) :=
    lt_of_lt_of_le (mul_pos (mul_pos hcoef (sq_pos_of_pos hnpos)) hlog) hlo
  have hcount : 0 < kCount lab := by
    by_contra hc
    have hz : kCount lab=0 := Nat.eq_zero_of_not_pos hc
    simp only [hz,Nat.cast_zero,Real.log_zero] at hlogpos
    exact (lt_irrefl (0 : ℝ)) hlogpos
  refine ⟨hcount,?_,?_⟩
  · refine le_trans ?_ hlo
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 1/6-ε ≤ 1/6-ε') (sq_nonneg _)) hlog.le
  · exact log_upper_of hε (by exact_mod_cast hnlarge) (Nat.cast_nonneg _)
      (kCount_upper lab (by omega))

end CDRBicolour.KBicolor.Wilson
