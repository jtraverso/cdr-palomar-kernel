/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Pseudorandom.Numerics12
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Numerical lemmas for Theorem 1.3 -/

@[expose] public section

namespace Pseudorandom

open Finset

/-- `p^{\underline{ℓ}} / p^ℓ ≥ 1 - ℓ²/p` and `p^{\underline{ℓ}} ≤ p^ℓ`. -/
theorem descFactorial_ratio (p : ℕ) (hp : 0 < p) :
    ∀ ℓ : ℕ, ℓ ≤ p → (1 - (ℓ : ℝ) ^ 2 / p) * (p : ℝ) ^ ℓ ≤ p.descFactorial ℓ ∧
      (p.descFactorial ℓ : ℝ) ≤ (p : ℝ) ^ ℓ := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  intro ℓ
  induction ℓ with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [Nat.descFactorial_succ]
    have hsub : ((p - n : ℕ) : ℝ) = p - n := by rw [Nat.cast_sub (by omega)]
    push_cast
    rw [hsub]
    have hpn : (0 : ℝ) ≤ p - n := by
      have : (n : ℝ) + 1 ≤ p := by exact_mod_cast hn
      linarith
    have hD0 : (0 : ℝ) ≤ p.descFactorial n := Nat.cast_nonneg _
    constructor
    · -- (1 - (n+1)²/p) p^{n+1} ≤ (p - n) * D
      have hpow : (0 : ℝ) ≤ (p : ℝ) ^ n := by positivity
      have key : (1 - ((n : ℝ) + 1) ^ 2 / p) * (p : ℝ) ^ (n + 1) ≤
          (p - n) * ((1 - (n : ℝ) ^ 2 / p) * (p : ℝ) ^ n) := by
        rw [pow_succ (p : ℝ) n]
        have e1 : (1 - ((n : ℝ) + 1) ^ 2 / p) * ((p : ℝ) ^ n * p) =
            (p - ((n : ℝ) + 1) ^ 2) * (p : ℝ) ^ n := by field_simp
        have e2 : (p - n) * ((1 - (n : ℝ) ^ 2 / p) * (p : ℝ) ^ n) =
            ((p - n) * (p - (n : ℝ) ^ 2) / p) * (p : ℝ) ^ n := by field_simp
        rw [e1, e2]
        apply mul_le_mul_of_nonneg_right _ hpow
        rw [le_div_iff₀ hpR]
        nlinarith [sq_nonneg (n : ℝ)]
      have := mul_le_mul_of_nonneg_left h1 hpn
      push_cast at this ⊢
      linarith
    · rw [pow_succ]
      have : (p : ℝ) - n ≤ p := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      calc ((p : ℝ) - n) * p.descFactorial n ≤ p * (p : ℝ) ^ n :=
            mul_le_mul this h2 hD0 hpR.le
        _ = (p : ℝ) ^ n * p := by ring

/-- Product of numbers in `[0,1]` each at least `1 - fᵢ`. -/
theorem mul_ge_one_sub {a b f g : ℝ} (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (ha : 1 - f ≤ a) (hb : 1 - g ≤ b) : 1 - (f + g) ≤ a * b := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)]

/-- The main factor `((1-ν)/(1+2ξ))^ℓ · p^{\underline ℓ}/p^ℓ` is in `[1 - f, 1]`. -/
theorem main_factor_bounds (ℓ p : ℕ) (hp : 0 < p) (hℓp : ℓ ≤ p) {ν ξ : ℝ} (hν0 : 0 ≤ ν)
    (hν1 : ν ≤ 1) (hξ0 : 0 ≤ ξ) :
    1 - (ℓ * ν + 2 * ℓ * ξ + (ℓ : ℝ) ^ 2 / p) ≤
        ((1 - ν) / (1 + 2 * ξ)) ^ ℓ * ((p.descFactorial ℓ : ℝ) / (p : ℝ) ^ ℓ) ∧
      ((1 - ν) / (1 + 2 * ξ)) ^ ℓ * ((p.descFactorial ℓ : ℝ) / (p : ℝ) ^ ℓ) ≤ 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpl : (0 : ℝ) < (p : ℝ) ^ ℓ := by positivity
  obtain ⟨hd1, hd2⟩ := descFactorial_ratio p hp ℓ hℓp
  set R := (p.descFactorial ℓ : ℝ) / (p : ℝ) ^ ℓ with hR
  have hR1 : R ≤ 1 := by rw [hR, div_le_one hpl]; exact hd2
  have hR0 : 0 ≤ R := by positivity
  have hRlo : 1 - (ℓ : ℝ) ^ 2 / p ≤ R := by rw [hR, le_div_iff₀ hpl]; exact hd1
  set u := (1 - ν) / (1 + 2 * ξ) with hu
  have hu0 : 0 ≤ u := by rw [hu]; apply div_nonneg <;> linarith
  have hu1 : u ≤ 1 := by rw [hu, div_le_one (by linarith)]; linarith
  have hul : 1 - (ℓ * ν + 2 * ℓ * ξ) ≤ u ^ ℓ := by
    -- u ≥ (1 - ν)(1 - 2ξ)
    have h1 : (1 - ν) * (1 - 2 * ξ) ≤ u := by
      rw [hu, le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg hξ0 hξ0, mul_nonneg hν0 hξ0]
    by_cases hξ2 : 2 * ξ ≤ 1
    · have h2 : 1 - ℓ * ν ≤ (1 - ν) ^ ℓ := by
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -ν by linarith) ℓ
        simpa [sub_eq_add_neg] using this
      have h3 : 1 - ℓ * (2 * ξ) ≤ (1 - 2 * ξ) ^ ℓ := by
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(2 * ξ) by linarith) ℓ
        simpa [sub_eq_add_neg] using this
      have h4 : ((1 - ν) * (1 - 2 * ξ)) ^ ℓ ≤ u ^ ℓ :=
        pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) h1 ℓ
      rw [mul_pow] at h4
      have h5 := mul_ge_one_sub (pow_le_one₀ (by linarith) (by linarith))
        (pow_le_one₀ (by linarith) (by linarith)) h2 h3
      nlinarith
    · push_neg at hξ2
      have : (1 : ℝ) ≤ ℓ * (2 * ξ) ∨ ℓ = 0 := by
        rcases Nat.eq_zero_or_pos ℓ with h | h
        · right; exact h
        · left
          have : (1 : ℝ) ≤ ℓ := by exact_mod_cast h
          nlinarith
      rcases this with h | h
      · have : 0 ≤ u ^ ℓ := pow_nonneg hu0 ℓ
        nlinarith [mul_nonneg (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ) hν0]
      · subst h; simp
  constructor
  · have := mul_ge_one_sub (pow_le_one₀ hu0 hu1) hR1 hul hRlo
    linarith
  · calc u ^ ℓ * R ≤ 1 * 1 := mul_le_mul (pow_le_one₀ hu0 hu1) hR1 hR0 zero_le_one
      _ = 1 := by ring

/-- The final comparison for Theorem 1.3. -/
theorem final_estimate13 {M SD A0 m Wn Fm Err t ξ e f : ℝ} (hWn : 0 < Wn) (hA0 : 0 ≤ A0)
    (hm : 0 ≤ m) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hf0 : 0 ≤ f)
    (hSD : |SD - A0| ≤ ξ * A0) (hmA : m * A0 = Fm * Wn) (hF1 : Fm ≤ 1) (hFf : 1 - f ≤ Fm)
    (hlo : m * SD - t < M) (hup : M < m * SD + Err + t) (ht : t = e * Wn / 2)
    (hErr : Err ≤ e * Wn / 4) (hξe : ξ ≤ e / 4) (hξf : ξ + f ≤ e / 2) :
    |M - Wn| ≤ e * Wn := by
  rw [abs_le] at hSD
  have h1 : m * SD ≤ m * ((1 + ξ) * A0) := mul_le_mul_of_nonneg_left (by linarith) hm
  have h2 : m * ((1 - ξ) * A0) ≤ m * SD := mul_le_mul_of_nonneg_left (by linarith) hm
  have e1 : m * ((1 + ξ) * A0) = (1 + ξ) * (Fm * Wn) := by rw [← hmA]; ring
  have e2 : m * ((1 - ξ) * A0) = (1 - ξ) * (Fm * Wn) := by rw [← hmA]; ring
  rw [e1] at h1
  rw [e2] at h2
  have h3 : (1 + ξ) * (Fm * Wn) ≤ (1 + ξ) * Wn := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  have h4 : (1 - ξ) * ((1 - f) * Wn) ≤ (1 - ξ) * (Fm * Wn) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hξ0 hf0, mul_nonneg (mul_nonneg hξ0 hf0) hWn.le]
  · nlinarith

end Pseudorandom
