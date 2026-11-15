/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.Wilson.LocalBalance

/-!
# Exactifying the local Wilson seed with the k-colour bounded inverse

This correction lemma applies to arbitrary target edge loads, including the
local loads 1 and 1/g. Given an approximate seed and the exact compatibility
condition, a defect of norm at most ε changes each triangle weight by at most
Kε/n. The construction of the approximate local seed remains a separate step.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Refined

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

theorem exactify_local_seed (lab : V → Fin k) {K lo hi ε : ℝ}
    (B : BRIG lab (bicF k) (wlk lab) K) (hn : 0 < Fintype.card V)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hsmall : K * ε ≤ lo / 2)
    (μ₀ : Finset V → ℝ) (τ : E0 V → ℝ)
    (hτ : ellG' (wlk lab) τ = 0)
    (hμ : ∀ T ∈ triG lab (bicF k),
      lo / Fintype.card V ≤ μ₀ T ∧ μ₀ T ≤ hi / Fintype.card V)
    (hdef : ‖τ - MincG lab (bicF k) μ₀‖ ≤ ε) :
    ∃ φ : Finset V → ℝ, MincG lab (bicF k) φ = τ ∧
      ∀ T ∈ triG lab (bicF k), lo / (2 * Fintype.card V) ≤ φ T ∧
        φ T ≤ (hi + lo / 2) / Fintype.card V := by
  let d := τ - MincG lab (bicF k) μ₀
  have hell : ellG' (wlk lab) d = 0 := by
    rw [show d = τ - MincG lab (bicF k) μ₀ from rfl, map_sub, hτ,
      gell_M (fun T hT => wlk_tri lab hT), sub_self]
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hcorr : ∀ T, |B.Φ d T| ≤ lo / (2 * Fintype.card V) := by
    intro T
    calc
      _ ≤ K / Fintype.card V * ‖d‖ := B.bound d hell T
      _ ≤ K / Fintype.card V * ε :=
        mul_le_mul_of_nonneg_left hdef (div_nonneg hK hnR.le)
      _ = (K * ε) / Fintype.card V := by ring
      _ ≤ (lo / 2) / Fintype.card V := div_le_div_of_nonneg_right hsmall hnR.le
      _ = _ := by ring
  refine ⟨μ₀ + B.Φ d, ?_, fun T hT => ?_⟩
  · rw [map_add, B.exact d hell]
    ext e
    simp only [Pi.add_apply, d, Pi.sub_apply]
    ring
  · obtain ⟨hl, hu⟩ := hμ T hT
    have hc := abs_le.mp (hcorr T)
    simp only [Pi.add_apply]
    constructor
    · have he : lo / Fintype.card V = 2 * (lo / (2 * Fintype.card V)) := by ring
      linarith
    · have he : (hi + lo / 2) / Fintype.card V =
        hi / Fintype.card V + lo / (2 * Fintype.card V) := by ring
      linarith

end CDRBicolour.KBicolor.Wilson
