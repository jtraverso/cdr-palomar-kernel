/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexStructuredFutureBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Vortex

/-- Sizes and protection budgets for the same sampled, prepared and resource
windows. All variables are real cardinalities, so this applies directly after
casting the finite-set cardinality identities. -/
theorem relative_window_budgets
    (n raw cut full future resources β q ρ ηBank γStock : ℝ)
    (hn : 0 < n) (hq : 0 < q) (hq32 : q ≤ 1 / 32)
    (hβ : 0 ≤ β) (hβ8 : β ≤ 1 / 8)
    (hRawLow : (3 / 4 : ℝ) * q * n ≤ raw)
    (hRawUp : raw ≤ (5 / 4 : ℝ) * q * n)
    (hCut0 : 0 ≤ cut) (hCut : cut ≤ β * raw)
    (hFull : full = raw - cut)
    (hFuture0 : 0 ≤ future) (hFuture : future ≤ 2 * q * full)
    (hResources : resources = full - future)
    (hρ : 2 * q ≤ ρ) (hBank : q ≤ ηBank / 16)
    (hStock : q ≤ γStock / 8) :
    q * n / 2 ≤ full ∧ full < 2 * q * n ∧
      q * n / 4 ≤ resources ∧
      cut + future ≤ (β + 2 * q) * raw ∧
      future ≤ ρ * full ∧ future ≤ (ηBank / 2) * resources ∧
      future ≤ γStock * n := by
  have hqn : 0 < q * n := mul_pos hq hn
  have hRaw0 : 0 ≤ raw := by nlinarith
  have hCut8 := hCut.trans (mul_le_mul_of_nonneg_right hβ8 hRaw0)
  have hFullRaw : full ≤ raw := by linarith
  have hFullLow : q * n / 2 ≤ full := by nlinarith
  have hFull0 : 0 ≤ full := by nlinarith
  have hFullUp : full < 2 * q * n := by nlinarith
  have hFutureSmall : future ≤ full / 16 := by
    have hs := mul_le_mul_of_nonneg_right hq32 hFull0
    nlinarith
  have hResourceLow : q * n / 4 ≤ resources := by nlinarith
  have hResource0 : 0 ≤ resources := by nlinarith
  have hFullResources : full ≤ 2 * resources := by linarith
  have hCutFuture : cut + future ≤ (β + 2 * q) * raw := by
    have hf := mul_le_mul_of_nonneg_left hFullRaw (by positivity : 0 ≤ 2 * q)
    nlinarith
  have hFutureρ : future ≤ ρ * full :=
    hFuture.trans (mul_le_mul_of_nonneg_right hρ hFull0)
  have hBank0 : 0 ≤ ηBank := by linarith
  have hFutureBank : future ≤ (ηBank / 2) * resources := by
    have hb := mul_le_mul_of_nonneg_right hBank hFull0
    have hr := mul_le_mul_of_nonneg_left hFullResources hBank0
    have hbr := mul_nonneg hBank0 hResource0
    nlinarith
  have hRawN : raw ≤ n := by
    have hs := mul_le_mul_of_nonneg_right hq32 hn.le
    nlinarith
  have hFutureStock : future ≤ γStock * n := by
    have hf := mul_le_mul_of_nonneg_left (hFullRaw.trans hRawN)
      (by positivity : 0 ≤ 2 * q)
    have hs := mul_le_mul_of_nonneg_right hStock hn.le
    nlinarith
  exact ⟨hFullLow,hFullUp,hResourceLow,hCutFuture,hFutureρ,hFutureBank,hFutureStock⟩

#print axioms relative_window_budgets
end TypedTriangle.Vortex
