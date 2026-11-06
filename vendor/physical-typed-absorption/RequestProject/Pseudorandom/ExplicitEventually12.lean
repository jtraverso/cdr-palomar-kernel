/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.Pseudorandom.ExplicitAsymptotics
public import RequestProject.Pseudorandom.Eventually12
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
noncomputable section
namespace Pseudorandom.Explicit
open Pseudorandom

def facts12Cut (r : ℕ) (δ ε a b ρ κ σ D₀ : ℝ) : ℝ :=
  max 2 (max (powerCut ((1-a)-b*((r-1:ℕ):ℝ)) (2^(r-1)))
    (max (powerCut (ε-(b*((r-1:ℕ):ℝ)+(a-δ))) (2*2^(r-1)))
    (max (powerCut (2*ε) 2)
    (max (powerCut ((δ-4*ε)-(b*((2*r:ℕ):ℝ)+ε)) (128*(r+1)*2^(2*r)))
    (max (powerCut (ε-ε^2) 512)
    (max (powerCut ε (512*Real.log (64*r^2)))
    (max (logCut ε 1024)
    (max (powerCut a (2*D₀))
    (max (powerCut (a*κ-ε) (2^κ))
    (max (powerCut (a*σ-ε^2) (2^σ))
    (max (powerCut ((-ε)-(-(a*ρ))) (4*2^ρ))
    (max (powerCut ((-ε)-(-(2*ε))) 16) (powerCut a 2)))))))))))))

theorem facts12_explicit (r : ℕ) (hr : 2 ≤ r) {δ ε a b ρ κ σ : ℝ} (D₀ : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (ha : 0 < a)
    (e2 : b * ((r - 1 : ℕ) : ℝ) < 1 - a) (e3 : b * ((r - 1 : ℕ) : ℝ) + (a - δ) < ε)
    (e5 : b * ((2 * r : ℕ) : ℝ) + ε < δ - 4 * ε) (e8 : ε < a * κ) (e9 : ε ^ 2 < a * σ)
    (e10 : ε < a * ρ) :
    ∀ D : ℝ, facts12Cut r δ ε a b ρ κ σ D₀ ≤ D → Facts12 r δ ε a b ρ κ σ D₀ D := by
  intro D hD
  have hε2 : ε^2 < ε := by nlinarith
  have bounds : 2 ≤ D ∧
      powerCut ((1-a)-b*((r-1:ℕ):ℝ)) (2^(r-1)) ≤ D ∧
      powerCut (ε-(b*((r-1:ℕ):ℝ)+(a-δ))) (2*2^(r-1)) ≤ D ∧
      powerCut (2*ε) 2 ≤ D ∧
      powerCut ((δ-4*ε)-(b*((2*r:ℕ):ℝ)+ε)) (128*(r+1)*2^(2*r)) ≤ D ∧
      powerCut (ε-ε^2) 512 ≤ D ∧ powerCut ε (512*Real.log (64*r^2)) ≤ D ∧
      logCut ε 1024 ≤ D ∧ powerCut a (2*D₀) ≤ D ∧
      powerCut (a*κ-ε) (2^κ) ≤ D ∧ powerCut (a*σ-ε^2) (2^σ) ≤ D ∧
      powerCut ((-ε)-(-(a*ρ))) (4*2^ρ) ≤ D ∧
      powerCut ((-ε)-(-(2*ε))) 16 ≤ D ∧ powerCut a 2 ≤ D := by
    simpa only [facts12Cut,max_le_iff] using hD
  rcases bounds with ⟨hD2,h2,h3,h4,h5,h6a,h6b,h6c,h7,h8,h9,h10a,h10b,h11⟩
  have f2 := mul_rpow_le_rpow e2 h2
  have f3 := mul_rpow_le_rpow e3 h3
  have f4 := const_le_rpow (by positivity : 0 < 2*ε) h4
  have f5 := mul_rpow_le_rpow e5 h5
  have f6a : D^(ε^2) ≤ (1/512)*D^ε :=
    rpow_le_mul_rpow hε2 (by norm_num) (by simpa using h6a)
  have f6b := const_le_rpow hε h6b
  have f6c := mul_log_le_rpow hε h6c
  have f7 := const_le_rpow ha h7
  have f8 := mul_rpow_le_rpow e8 h8
  have f9 := mul_rpow_le_rpow e9 h9
  have f10a := mul_rpow_le_rpow (show -(a*ρ) < -ε by linarith) h10a
  have f10b := mul_rpow_le_rpow (show -(2*ε) < -ε by linarith) h10b
  have f11 := const_le_rpow ha h11
  have hD0 : 0 < D := by linarith
  have hDε : 0 < D ^ ε := Real.rpow_pos_of_pos hD0 _
  refine ⟨hD2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    have hsum : Real.log (64 * r ^ 2) + 2 * Real.log D + (2 * D ^ (ε ^ 2) - D ^ ε / 64) < 0 := by
      have : 2 * Real.log D ≤ D ^ ε / 512 := by linarith
      have : Real.log (64 * r ^ 2) ≤ D ^ ε / 512 := by linarith
      have : D ^ (ε ^ 2) ≤ D ^ ε / 512 := by linarith
      linarith
    have hr0 : (0 : ℝ) < 64 * r ^ 2 := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr
      positivity
    have : 64 * r ^ 2 * D ^ 2 * Real.exp (2 * D ^ (ε ^ 2) - D ^ ε / 64) =
        Real.exp (Real.log (64 * r ^ 2) + 2 * Real.log D + (2 * D ^ (ε ^ 2) - D ^ ε / 64)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hr0, show 2 * Real.log D = Real.log (D ^ 2)
        by rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
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
    rw [e]; linarith
  · linarith

#print axioms facts12_explicit
end Pseudorandom.Explicit
