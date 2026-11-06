/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# The explicit rational union bound for the balanced selector

With `N = 4k` auxiliaries per side, at most `k` ports per side, `20` rounds and
`M = ⌊(N+k)/2⌋ + 1`, for every `1 ≤ s ≤ M`

  `C(N+l, s) · C(N, s-1) · ((s-1)/N)^(20 s) ≤ (1/4)^s`,

hence the sum over `1 ≤ s ≤ M` is `≤ 1/3`.  The proof uses `C(m,s) ≤ m^s/s!`,
`s^s/s! ≤ e^s < 3^s`, `(s-1)/N ≤ 3/4` and the rational check `(5/4)·9·(3/4)^18 ≤ 1/4`.
-/

namespace SelBound

open Finset

/-- The window bound `M = ⌊(4k+k)/2⌋ + 1`. -/
def window (k : ℕ) : ℕ := (4 * k + k) / 2 + 1

lemma pow_div_factorial_le_three_pow (s : ℕ) :
    (s : ℝ) ^ s / (s.factorial : ℝ) ≤ 3 ^ s := by
  have h1 := Real.pow_div_factorial_le_exp (s : ℝ) (Nat.cast_nonneg s) s
  have h2 : Real.exp (s : ℝ) ≤ 3 ^ s := by
    rw [← Real.exp_one_rpow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le
      (by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith) s
  exact h1.trans h2

lemma rational_check : (5 / 4 : ℝ) * 9 * (3 / 4) ^ 18 ≤ 1 / 4 := by norm_num

theorem term_le (k l s : ℕ) (hk : 1 ≤ k) (hl : l ≤ k) (hs1 : 1 ≤ s) (hsM : s ≤ window k) :
    ((4 * k + l).choose s : ℝ) * ((4 * k).choose (s - 1) : ℝ) *
      (((s - 1 : ℕ) : ℝ) / (4 * k)) ^ (20 * s) ≤ (1 / 4) ^ s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold window at hsM
  have hK : (0 : ℝ) < 4 * k := by positivity
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  -- `t ≤ 5k/2`, so `t/(4k) ≤ 3/4` and `(t+1)/(4k) ≤ 1`
  have ht2 : 2 * t ≤ 5 * k := by omega
  have ht2R : 2 * (t : ℝ) ≤ 5 * k := by exact_mod_cast ht2
  have hq34 : (t : ℝ) / (4 * k) ≤ 3 / 4 := by
    rw [div_le_iff₀ hK]; nlinarith
  have hq0 : (0 : ℝ) ≤ (t : ℝ) / (4 * k) := by positivity
  have hsK : ((t + 1 : ℕ) : ℝ) / (4 * k) ≤ 1 := by
    rw [div_le_iff₀ hK]; push_cast; nlinarith
  have hqs : (t : ℝ) / (4 * k) ≤ ((t + 1 : ℕ) : ℝ) / (4 * k) := by
    apply div_le_div_of_nonneg_right _ hK.le; push_cast; linarith
  -- binomial bounds
  have hc1 : ((4 * k + l).choose (t + 1) : ℝ) ≤ ((5 * k : ℕ) : ℝ) ^ (t + 1) / (t + 1).factorial := by
    have := Nat.choose_le_choose (t + 1) (show 4 * k + l ≤ 5 * k by omega)
    exact (Nat.cast_le.mpr this).trans (Nat.choose_le_pow_div (t + 1) (5 * k))
  have hc2 : ((4 * k).choose t : ℝ) ≤ ((4 * k : ℕ) : ℝ) ^ t / t.factorial :=
    Nat.choose_le_pow_div t (4 * k)
  -- power bound
  set q : ℝ := (t : ℝ) / (4 * k) with hq
  set p : ℝ := ((t + 1 : ℕ) : ℝ) / (4 * k) with hp
  have hp0 : 0 ≤ p := by positivity
  have hpow : q ^ (20 * (t + 1)) ≤ (p ^ 2) ^ (t + 1) * ((3 / 4) ^ 18) ^ (t + 1) := by
    rw [← mul_pow, pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    calc q ^ 20 = q ^ 2 * q ^ 18 := by ring
      _ ≤ p ^ 2 * (3 / 4) ^ 18 := by
        apply mul_le_mul (pow_le_pow_left₀ hq0 hqs 2) (pow_le_pow_left₀ hq0 hq34 18)
          (by positivity) (by positivity)
  -- assemble
  have hfac : ((t + 1).factorial : ℝ) = (t + 1 : ℝ) * t.factorial := by
    push_cast [Nat.factorial_succ]; ring
  have hF : (0 : ℝ) < t.factorial := by exact_mod_cast Nat.factorial_pos t
  have hss := pow_div_factorial_le_three_pow (t + 1)
  set s : ℝ := ((t + 1 : ℕ) : ℝ) with hs
  have hs0 : (0 : ℝ) < s := by positivity
  have hsF : (0 : ℝ) < ((t + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  -- the key identity
  have hid : ((5 * k : ℕ) : ℝ) ^ (t + 1) / (t + 1).factorial *
      (((4 * k : ℕ) : ℝ) ^ t / t.factorial) * ((p ^ 2) ^ (t + 1) * ((3 / 4) ^ 18) ^ (t + 1)) =
      (5 / 4 : ℝ) ^ (t + 1) * (s ^ (t + 1) / (t + 1).factorial) ^ 2 * p *
        ((3 / 4) ^ 18) ^ (t + 1) := by
    rw [hp]
    have hfac' : (t.factorial : ℝ) = ((t + 1).factorial : ℝ) / s := by
      rw [hfac, hs]; push_cast; field_simp
    rw [hfac']
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    push_cast
    simp only [div_pow, mul_pow, ← pow_mul]
    field_simp
    ring
  have hfin : (5 / 4 : ℝ) ^ (t + 1) * (s ^ (t + 1) / (t + 1).factorial) ^ 2 * p *
      ((3 / 4) ^ 18) ^ (t + 1) ≤ (1 / 4) ^ (t + 1) := by
    have h3 : (s ^ (t + 1) / (t + 1).factorial) ^ 2 ≤ (9 : ℝ) ^ (t + 1) := by
      have h0 : 0 ≤ s ^ (t + 1) / ((t + 1).factorial : ℝ) := by positivity
      calc (s ^ (t + 1) / (t + 1).factorial) ^ 2 ≤ ((3 : ℝ) ^ (t + 1)) ^ 2 :=
            pow_le_pow_left₀ h0 hss 2
        _ = (9 : ℝ) ^ (t + 1) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    calc (5 / 4 : ℝ) ^ (t + 1) * (s ^ (t + 1) / (t + 1).factorial) ^ 2 * p *
          ((3 / 4) ^ 18) ^ (t + 1)
        ≤ (5 / 4 : ℝ) ^ (t + 1) * 9 ^ (t + 1) * 1 * ((3 / 4) ^ 18) ^ (t + 1) := by
          gcongr
      _ = ((5 / 4 : ℝ) * 9 * (3 / 4) ^ 18) ^ (t + 1) := by rw [mul_one, mul_pow, mul_pow]
      _ ≤ (1 / 4) ^ (t + 1) := pow_le_pow_left₀ (by norm_num) rational_check _
  calc ((4 * k + l).choose (t + 1) : ℝ) * ((4 * k).choose t : ℝ) * q ^ (20 * (t + 1))
      ≤ ((5 * k : ℕ) : ℝ) ^ (t + 1) / (t + 1).factorial *
        (((4 * k : ℕ) : ℝ) ^ t / t.factorial) *
        ((p ^ 2) ^ (t + 1) * ((3 / 4) ^ 18) ^ (t + 1)) := by
        gcongr
    _ = _ := hid
    _ ≤ _ := hfin

theorem sum_term_le (k l : ℕ) (hk : 1 ≤ k) (hl : l ≤ k) :
    ∑ s ∈ Icc 1 (window k), ((4 * k + l).choose s : ℝ) * ((4 * k).choose (s - 1) : ℝ) *
      (((s - 1 : ℕ) : ℝ) / (4 * k)) ^ (20 * s) ≤ 1 / 3 := by
  calc _ ≤ ∑ s ∈ Icc 1 (window k), (1 / 4 : ℝ) ^ s := by
        apply sum_le_sum; intro s hs
        rw [mem_Icc] at hs
        exact term_le k l s hk hl hs.1 hs.2
    _ ≤ 1 / 3 := by
        have : ∀ m : ℕ, ∑ s ∈ Icc 1 m, (1 / 4 : ℝ) ^ s = (1 - (1 / 4) ^ m) / 3 := by
          intro m
          induction m with
          | zero => simp
          | succ m ih =>
            rw [Finset.sum_Icc_succ_top (by omega), ih]; ring
        rw [this]
        have : (0 : ℝ) ≤ (1 / 4) ^ window k := by positivity
        linarith

end SelBound
