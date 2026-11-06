/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.Core13
public import RequestProject.Pseudorandom.Eventually12
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # The numerical conditions of Theorem 1.3 hold for all large `Δ` -/

@[expose] public section

namespace Pseudorandom

open Filter

/-- All numerical conditions `Facts13` hold for large `Δ`. -/
theorem eventually_facts13 (r L : ℕ) (hr : 2 ≤ r) (hL : 1 ≤ L) {δ ε a b ρ κ σ : ℝ} (D₀ : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (ha : 0 < a)
    (e2 : b * ((r - 1 : ℕ) : ℝ) < 1 - a) (e3 : b * ((r - 1 : ℕ) : ℝ) + (a - δ) < ε)
    (e5 : b * ((2 * r : ℕ) : ℝ) + ε < δ - 4 * ε) (e8 : ε < a * κ) (e9 : ε ^ 2 < a * σ)
    (e10 : ε < a * ρ) (e12 : b * ((2 * r * L : ℕ) : ℝ) + ε < δ - 4 * ε)
    (e15 : 2 * ε < a) (e18 : a + ε < b) :
    ∀ᶠ D : ℝ in atTop, Facts13 r L δ ε a b ρ κ σ D₀ D := by
  have hε2 : ε ^ 2 < ε := by nlinarith
  have hε2pos : 0 < ε ^ 2 := by positivity
  have hb : 0 < b := by linarith
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hnc : 0 < nc13 r L := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    unfold nc13; positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_mul_rpow_le_rpow e2 (2 ^ (r - 1)),
    eventually_mul_rpow_le_rpow e3 (2 * 2 ^ (r - 1)),
    eventually_const_le_rpow (by positivity : (0 : ℝ) < 2 * ε) 2,
    eventually_mul_rpow_le_rpow e5 (128 * (r + 1) * 2 ^ (2 * r)),
    eventually_rpow_le_mul_rpow (c := 1 / 512) hε2 (by norm_num),
    eventually_const_le_rpow hε (512 * Real.log (nc13 r L)),
    eventually_mul_log_le_rpow hε (512 * (2 * L + 2)),
    eventually_const_le_rpow ha (2 * D₀),
    eventually_mul_rpow_le_rpow e8 (2 ^ κ),
    eventually_mul_rpow_le_rpow e9 (2 ^ σ),
    eventually_mul_rpow_le_rpow (show -(a * ρ) < -ε by linarith) (6 * L * 2 ^ ρ),
    eventually_mul_rpow_le_rpow (show -(2 * ε) < -ε by linarith) (6 * (2 * L + 1)),
    eventually_mul_rpow_le_rpow (show -b < -ε by linarith) (6 * L ^ 2),
    eventually_const_le_rpow ha 2,
    eventually_mul_rpow_le_rpow e12 (1024 * (r * L + 1) * L ^ 2 * 2 ^ (2 * r * L)),
    eventually_const_le_rpow (by positivity : (0 : ℝ) < 2 * ε) (2 * (24 * L ^ 3 * (L + 1))),
    eventually_mul_rpow_le_rpow (show ε ^ 2 < 2 * ε by linarith) (2 * (24 * L ^ 3)),
    eventually_mul_rpow_le_rpow (show ε < 2 * ε by linarith) (64 * L ^ 2),
    eventually_mul_rpow_le_rpow (show 1 - a + 2 * ε < 1 by linarith) 2,
    eventually_const_le_rpow hb (2 * L ^ 2),
    eventually_mul_rpow_le_rpow (show ε < 2 * ε by linarith) (144 * L ^ (4 * L + 2) / 64),
    eventually_mul_rpow_le_rpow (show a - b < -ε by linarith) (64 * L ^ (3 * L + 1)),
    eventually_mul_rpow_le_rpow (show a < b by linarith) 4,
    eventually_mul_rpow_le_rpow (show -(2 * ε) < -ε by linarith) 4]
    with D hD2 f2 f3 f4 f5 f6a f6b f6c f7 f8 f9 f10a f10b f10c f11 f12 f13a f13b f14 f15 f16
      f17 f18 f19 f20
  have hD0 : 0 < D := by linarith
  have hDε : 0 < D ^ ε := Real.rpow_pos_of_pos hD0 _
  refine ⟨hD2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [two_mul_rpow_pow hD0]; exact f2
  · rw [two_mul_rpow_pow hD0, mul_assoc (2 : ℝ), mul_assoc, ← Real.rpow_add hD0, ← mul_assoc]
    exact f3
  · rw [Real.rpow_neg hD0.le, inv_eq_one_div, div_le_div_iff₀ (Real.rpow_pos_of_pos hD0 _)
      (by norm_num)]
    linarith
  · rw [two_mul_rpow_pow hD0]
    calc 128 * (r + 1) * (2 ^ (2 * r) * D ^ (b * ((2 * r : ℕ) : ℝ))) * D ^ ε =
        128 * (r + 1) * 2 ^ (2 * r) * D ^ (b * ((2 * r : ℕ) : ℝ) + ε) := by
          rw [Real.rpow_add hD0]; ring
      _ ≤ _ := f5
  · -- the union bound
    have hlog : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
    have hsum : Real.log (nc13 r L) + (2 * L + 2) * Real.log D +
        (2 * D ^ (ε ^ 2) - D ^ ε / 64) < 0 := by
      have : (2 * L + 2) * Real.log D ≤ D ^ ε / 512 := by linarith
      have : Real.log (nc13 r L) ≤ D ^ ε / 512 := by linarith
      have : D ^ (ε ^ 2) ≤ D ^ ε / 512 := by linarith
      linarith
    have : nc13 r L * D ^ (2 * L + 2) * Real.exp (2 * D ^ (ε ^ 2) - D ^ ε / 64) =
        Real.exp (Real.log (nc13 r L) + (2 * L + 2) * Real.log D +
          (2 * D ^ (ε ^ 2) - D ^ ε / 64)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hnc,
        show (2 * (L : ℝ) + 2) * Real.log D = Real.log (D ^ (2 * L + 2)) by
          rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (by positivity)]
    rw [this]
    calc _ < Real.exp 0 := Real.exp_lt_exp.mpr hsum
      _ = 1 := Real.exp_zero
  · linarith
  · rw [rpow_div_two_rpow hD0, le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _), mul_comm]
    exact f8
  · rw [rpow_div_two_rpow hD0, le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _), mul_comm]
    exact f9
  · have e : (D ^ a / 2) ^ (-ρ) = 2 ^ ρ * D ^ (-(a * ρ)) := by
      rw [rpow_div_two_rpow hD0, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul,
        mul_comm, mul_neg]
    rw [e]
    have : (L : ℝ) * (2 ^ ρ * D ^ (-(a * ρ))) = 6 * L * 2 ^ ρ * D ^ (-(a * ρ)) / 6 := by ring
    rw [this]
    have : (2 * (L : ℝ) + 1) * D ^ (-(2 * ε)) = 6 * (2 * L + 1) * D ^ (-(2 * ε)) / 6 := by ring
    rw [this]
    have : (L : ℝ) ^ 2 * D ^ (-b) = 6 * L ^ 2 * D ^ (-b) / 6 := by ring
    rw [this]
    linarith
  · linarith
  · rw [two_mul_rpow_pow hD0]
    calc 1024 * (r * (L : ℝ) + 1) * L ^ 2 * (2 ^ (2 * r * L) *
          D ^ (b * ((2 * r * L : ℕ) : ℝ))) * D ^ ε =
        1024 * (r * L + 1) * L ^ 2 * 2 ^ (2 * r * L) *
          D ^ (b * ((2 * r * L : ℕ) : ℝ) + ε) := by
          rw [Real.rpow_add hD0]; ring
      _ ≤ _ := f12
  · linarith
  · exact f14
  · have e : D ^ (1 - a) * D ^ (2 * ε) = D ^ (1 - a + 2 * ε) := (Real.rpow_add hD0 _ _).symm
    rw [mul_assoc, e]
    simpa using f15
  · exact f16
  · linarith
  · exact f18
  · exact f19
  · exact f20

end Pseudorandom
