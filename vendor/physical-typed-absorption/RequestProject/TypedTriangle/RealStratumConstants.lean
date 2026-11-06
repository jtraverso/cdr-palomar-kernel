/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.RealStratumBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Stratum

/-- The real recurrence is compatible with a quadratic number of physical
rounds: eta, tau and the size threshold are fixed BEFORE the host order. -/
theorem real_stratum_budget_constants (A c γ κ : ℝ) (L : ℕ)
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hγ : 0 < γ) (hκ : 0 < κ) :
    ∃ η τ : ℝ, 0 < η ∧ 0 < τ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      A*(1+τ*(n:ℝ)^2)*(L+1)*(1+A*η*c/γ)^(L+1) < (⌊κ*(n:ℝ)^2⌋₊:ℝ) := by
  let η := γ/(1+A*c)
  have hden : 0 < 1+A*c := by positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hr : A*η*c/γ ≤ 1 := by
    have heq : A*η*c/γ = (A*c)/(1+A*c) := by dsimp [η]; field_simp
    rw [heq]
    exact (div_le_iff₀ hden).mpr (by linarith)
  let D := max 1 (A*(L+1)*2^(L+1))
  have hD : 1 ≤ D := le_max_left _ _
  have hDpos : 0 < D := by linarith
  let τ := κ/(4*D)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  refine ⟨η,τ,hη,hτ,max 1 ⌈(4*D+2)/κ⌉₊,?_⟩
  intro n hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hceil : (4*D+2)/κ ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  have hbig : 4*D+2 ≤ κ*(n:ℝ)^2 := by
    have hh := (div_le_iff₀ hκ).mp hceil
    nlinarith
  have hpow : (1+A*η*c/γ)^(L+1) ≤ (2:ℝ)^(L+1) := by
    apply pow_le_pow_left₀ (by positivity) (by linarith)
  have hbase : 0 ≤ A*(L+1:ℝ) := by positivity
  have hcoef : A*(L+1)*(1+A*η*c/γ)^(L+1) ≤ D :=
    (mul_le_mul_of_nonneg_left hpow hbase).trans (le_max_right _ _)
  have hbound : A*(1+τ*(n:ℝ)^2)*(L+1)*(1+A*η*c/γ)^(L+1) ≤
      D*(1+τ*(n:ℝ)^2) := by
    have hh := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ 1+τ*(n:ℝ)^2)
    nlinarith only [hh]
  have hDt : D*τ = κ/4 := by dsimp [τ]; field_simp
  have hfloor := Nat.sub_one_lt_floor (κ*(n:ℝ)^2)
  have hsmall : D*(1+τ*(n:ℝ)^2) ≤ κ*(n:ℝ)^2-1 := by
    nlinarith [hDt]
  exact hbound.trans_lt (hsmall.trans_lt hfloor)
end TypedTriangle.Stratum
