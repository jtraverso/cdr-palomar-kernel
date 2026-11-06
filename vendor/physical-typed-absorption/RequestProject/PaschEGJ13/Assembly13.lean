/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Pseudorandom.Assembly12
public import RequestProject.PaschEGJ13.TupleConvert
public import RequestProject.PaschEGJ13.Numerics13
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Assembling the proof of Theorem 1.3

`core_1_3` carries out Steps 1–3 for a fixed (large) `Δ` satisfying the numerical conditions
collected in `Facts13`. The nibble theorem enters as the hypothesis `hnib`.
-/

@[expose] public section

namespace Pseudorandom

open Finset

/-- The constant in the union bound. -/
noncomputable def nc13 (r L : ℕ) : ℝ := 256 * (r : ℝ) ^ 2 * (8 * (L : ℝ)) ^ (4 * L)

/-- The numerical conditions on `Δ`. -/
structure Facts13 (r L : ℕ) (δ ε a b ρ κ σ D₀ D : ℝ) : Prop where
  h1 : 2 ≤ D
  h2 : (2 * D ^ b) ^ (r - 1) ≤ D ^ (1 - a)
  h3 : 2 * (2 * D ^ b) ^ (r - 1) * D ^ (a - δ) ≤ D ^ ε
  h4 : D ^ (-(2 * ε)) ≤ 1 / 2
  h5 : 128 * (r + 1) * (2 * D ^ b) ^ (2 * r) * D ^ ε ≤ D ^ (δ - 4 * ε)
  h6 : nc13 r L * D ^ (2 * L + 2) * Real.exp (2 * D ^ (ε ^ 2) - D ^ ε / 64) < 1
  h7 : D₀ ≤ D ^ a / 2
  h8 : D ^ ε ≤ (D ^ a / 2) ^ κ
  h9 : D ^ (ε ^ 2) ≤ (D ^ a / 2) ^ σ
  h10 : L * (D ^ a / 2) ^ (-ρ) + (2 * L + 1) * D ^ (-(2 * ε)) + L ^ 2 * D ^ (-b) ≤ D ^ (-ε) / 2
  h11 : 1 ≤ D ^ a / 2
  h12 : 1024 * (r * L + 1) * L ^ 2 * (2 * D ^ b) ^ (2 * r * L) * D ^ ε ≤ D ^ (δ - 4 * ε)
  h13 : 24 * L ^ 3 * (L + 1 + D ^ (ε ^ 2)) ≤ D ^ (2 * ε)
  h14 : 64 * L ^ 2 * D ^ ε ≤ D ^ (2 * ε)
  h15 : 2 * D ^ (1 - a) * D ^ (2 * ε) ≤ D
  h16 : 2 * L ^ 2 ≤ D ^ b
  h17 : 144 * L ^ (4 * L + 2) * D ^ ε ≤ 64 * D ^ (2 * ε)
  h18 : 64 * L ^ (3 * L + 1) * D ^ (a - b) ≤ D ^ (-ε)
  h19 : 4 * D ^ a ≤ D ^ b
  h20 : 4 * D ^ (-(2 * ε)) ≤ D ^ (-ε)


/-- Lower bound for a Bernstein exponent `s² / (2A(R+s))`. -/
theorem expo_lb {s s₀ A R Y₀ : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hs1 : s ≤ 1) (hA : 0 < A)
    (hR : 0 ≤ R) (h : 2 * A * (R + 1) * Y₀ ≤ s₀ ^ 2) : Y₀ ≤ s ^ 2 / (2 * A * (R + s)) := by
  have hs0 : 0 < s := lt_of_lt_of_le hs₀ hs
  rw [le_div_iff₀ (by positivity)]
  have h1 : s₀ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hs₀.le hs 2
  by_cases hY : Y₀ ≤ 0
  · have : 0 ≤ s ^ 2 := by positivity
    have : Y₀ * (2 * A * (R + s)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hY (by positivity)
    linarith
  · push_neg at hY
    have h2 : 2 * A * Y₀ * (R + s) ≤ 2 * A * Y₀ * (R + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have : Y₀ * (2 * A * (R + s)) = 2 * A * Y₀ * (R + s) := by ring
    have : 2 * A * (R + 1) * Y₀ = 2 * A * Y₀ * (R + 1) := by ring
    linarith

/-- The constant `(8L)^{4L}` dominates the combinatorial factors. -/
theorem big_const_bounds {L : ℕ} (hL : 1 ≤ L) :
    (4 : ℝ) ≤ (8 * (L : ℝ)) ^ (4 * L) ∧
    2 * (L : ℝ) * 2 ^ L ≤ (8 * (L : ℝ)) ^ (4 * L) ∧
    2 * (L : ℝ) * 8 ^ L * (L : ℝ) ^ L ≤ (8 * (L : ℝ)) ^ (4 * L) := by
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h8 : (1 : ℝ) ≤ 8 * L := by linarith
  have hZ : (8 * (L : ℝ)) ^ (L + 1) ≤ (8 * (L : ℝ)) ^ (4 * L) := pow_le_pow_right₀ h8 (by omega)
  have hexp : (8 * (L : ℝ)) ^ (L + 1) = 8 * L * (8 ^ L * (L : ℝ) ^ L) := by
    rw [pow_succ, mul_pow]; ring
  have h3 : 2 * (L : ℝ) * 8 ^ L * (L : ℝ) ^ L ≤ (8 * (L : ℝ)) ^ (L + 1) := by
    rw [hexp]
    have : 0 ≤ (8 : ℝ) ^ L * (L : ℝ) ^ L := by positivity
    nlinarith
  have h2L : (2 : ℝ) ^ L ≤ 8 ^ L * (L : ℝ) ^ L := by
    calc (2 : ℝ) ^ L ≤ 8 ^ L := pow_le_pow_left₀ (by norm_num) (by norm_num) L
      _ ≤ 8 ^ L * (L : ℝ) ^ L := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hLR)
  have h88 : (1 : ℝ) ≤ 8 ^ L * (L : ℝ) ^ L := (one_le_pow₀ (by norm_num)).trans h2L
  refine ⟨?_, ?_, h3.trans hZ⟩
  · have : (4 : ℝ) ≤ 2 * (L : ℝ) * 8 ^ L * (L : ℝ) ^ L := by
      have : (8 : ℝ) ≤ 8 ^ L := by
        calc (8 : ℝ) = 8 ^ 1 := by norm_num
          _ ≤ 8 ^ L := pow_le_pow_right₀ (by norm_num) hL
      have : (1 : ℝ) ≤ (L : ℝ) ^ L := one_le_pow₀ hLR
      nlinarith
    linarith [h3.trans hZ]
  · have : 2 * (L : ℝ) * 2 ^ L ≤ 2 * (L : ℝ) * 8 ^ L * (L : ℝ) ^ L := by
      rw [mul_assoc (2 * (L : ℝ))]
      exact mul_le_mul_of_nonneg_left h2L (by positivity)
    linarith [h3.trans hZ]

/-- A monomial bound used in the union bounds. -/
theorem union_term_le {r L : ℕ} (hr : 2 ≤ r) {D E c : ℝ} (hD : 2 ≤ D) (hE : 1 ≤ E) (hc0 : 0 ≤ c)
    (hc : c ≤ (8 * (L : ℝ)) ^ (4 * L)) {m : ℕ} (hm : m ≤ 2 * L + 2) (k : ℕ) (hk : k ≤ 2) :
    c * (r : ℝ) ^ k * D ^ m * E ≤ (r : ℝ) ^ 2 * (8 * (L : ℝ)) ^ (4 * L) * D ^ (2 * L + 2) * (E * E) := by
  have hrR : (1 : ℝ) ≤ r := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have h1 : (r : ℝ) ^ k ≤ (r : ℝ) ^ 2 := pow_le_pow_right₀ hrR hk
  have h2 : D ^ m ≤ D ^ (2 * L + 2) := pow_le_pow_right₀ (by linarith) hm
  have h3 : E ≤ E * E := by nlinarith
  calc c * (r : ℝ) ^ k * D ^ m * E = (r : ℝ) ^ k * c * D ^ m * E := by ring
    _ ≤ (r : ℝ) ^ 2 * (8 * (L : ℝ)) ^ (4 * L) * D ^ (2 * L + 2) * (E * E) := by
        gcongr

end Pseudorandom
