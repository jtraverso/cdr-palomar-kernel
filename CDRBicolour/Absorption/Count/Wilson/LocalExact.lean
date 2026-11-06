/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Count.Wilson.Approx

/-!
# Optimal counting constant, part 6: the exact local seed (item 4)

`local_seed`: on the local copy of a piece, `φ = μ₀ + Φ(τ − M μ₀)` with `Φ` the bounded inverse of
`bri_of_balanced` (`ℓ(τ − M μ₀) = ℓ(τ) = 0` by `ell_tau`) has edge sums exactly `τ` and weights in
`[1/(4 g x), 3/x]` on the allowed triangles, `x = 2t`, once `8 · 52000 · g (4 + D) ≤ m`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Count.Wilson

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption

variable {la lb lc t g : ℕ}

theorem filter_card_le_three {V : Type*} [DecidableEq V] {T : Finset V} (hT : #T = 3)
    (p : V → Prop) [DecidablePred p] : #(T.filter p) ≤ 3 :=
  (card_filter_le _ _).trans hT.le

/-- **The exact local seed.** -/
theorem local_seed (hg : 1 ≤ g) (ht0 : 0 < t) (ht : t ≤ min la (min lb lc))
    (hy1 : xx t / 4 ≤ yy la lb lc t) (hy2 : yy la lb lc t ≤ xx t) {D : ℝ}
    (hD : ∀ k l, |rr la lb lc t k - rr la lb lc t l| ≤ D)
    (hid : ((la : ℝ) - t) ^ 2 + ((lb : ℝ) - t) ^ 2 + ((lc : ℝ) - t) ^ 2 -
      ((la : ℝ) - t) * ((lb : ℝ) - t) - ((la : ℝ) - t) * ((lc : ℝ) - t) -
      ((lb : ℝ) - t) * ((lc : ℝ) - t) =
      3 * g * t + ((la : ℝ) - t) + ((lb : ℝ) - t) + ((lc : ℝ) - t))
    {m0 : ℕ} (hm0 : ∀ k, m0 ≤ csz (col3 la lb lc) k) (h512 : 512 ≤ m0)
    (hbal : la + lb + lc ≤ 4 * m0)
    (hsmall : 8 * 52000 * (g : ℝ) * (4 + D) ≤ ((la + lb + lc : ℕ) : ℝ)) :
    ∃ φ : Finset (Fin (la + lb + lc)) → ℝ,
      (∀ T ∈ tri (col3 la lb lc), 1 / (4 * g * xx t) ≤ φ T ∧ φ T ≤ 3 / xx t) ∧
      ∀ e : E0 (Fin (la + lb + lc)), Minc (col3 la lb lc) φ e = tau' g t e.1 := by
  obtain ⟨B⟩ := bri_of_balanced (lab := col3 la lb lc) hm0 h512 (by simpa using hbal)
  set μ := mu0 la lb lc t g with hμ
  set τf : E0 (Fin (la + lb + lc)) → ℝ := fun e => tau' g t e.1 with hτf
  set d := τf - Minc (col3 la lb lc) μ with hd
  have hgpos : (1 : ℕ) ≤ g := hg
  have hell : ell (col3 la lb lc) d = 0 := by
    rw [hd, map_sub, ell_M, sub_zero]
    exact ell_tau (by omega) ht hid
  set x := xx t with hx
  have hx0 : 0 < x := by simp only [x, xx]; positivity
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD 0 0)
  have hdn : ‖d‖ ≤ 2 / x * (4 + D) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun e => ?_
    rw [Real.norm_eq_abs, hd, Pi.sub_apply, abs_sub_comm]
    exact mu0_deficit hg ht0 ht hy1 hy2 hD e
  set M : ℝ := ((la + lb + lc : ℕ) : ℝ) with hM
  have hM0 : 0 < M := by
    have hp : (0 : ℝ) ≤ 8 * 52000 * (g : ℝ) * D := by positivity
    have e : 8 * 52000 * (g : ℝ) * (4 + D) = 8 * 52000 * (g : ℝ) * 4 + 8 * 52000 * (g : ℝ) * D := by
      ring
    have : (0 : ℝ) < 8 * 52000 * g * 4 := by positivity
    linarith
  have hcorr : ∀ T, |B.Φ d T| ≤ 1 / (4 * g * x) := by
    intro T
    have h1 := B.bound d hell T
    rw [Fintype.card_fin] at h1
    calc |B.Φ d T| ≤ 52000 / M * ‖d‖ := h1
      _ ≤ 52000 / M * (2 / x * (4 + D)) := by gcongr
      _ ≤ 1 / (4 * g * x) := by
          have hgp : (0 : ℝ) < g := by linarith
          rw [show 52000 / M * (2 / x * (4 + D)) =
              8 * 52000 * (g : ℝ) * (4 + D) / M * (1 / (4 * g * x)) by field_simp; ring]
          exact mul_le_of_le_one_left (by positivity) ((div_le_one hM0).2 hsmall)
  refine ⟨μ + B.Φ d, fun T hT => ?_, fun e => ?_⟩
  · have hT3 : #T = 3 := (mem_tri.1 hT).1
    obtain ⟨l, u⟩ := wK_bounds hg hx0 hy1 hy2 _ (filter_card_le_three hT3 fun v => IsRes t v)
    have hc := abs_le.1 (hcorr T)
    have h4 : 1 / (4 * g * x) ≤ 1 / x := by
      apply one_div_le_one_div_of_le hx0
      nlinarith
    simp only [Pi.add_apply, hμ, mu0]
    have e2 : 1 / (2 * g * x) = 2 * (1 / (4 * g * x)) := by field_simp; ring
    constructor
    · rw [e2] at l; linarith [hc.1]
    · have : 3 / x = 2 / x + 1 / x := by ring
      rw [this]; linarith [hc.2]
  · rw [map_add, B.exact d hell, hd, Pi.add_apply, Pi.sub_apply]
    ring

end CDRBicolour.Absorption.Count.Wilson
