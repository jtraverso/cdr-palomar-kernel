/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.Eventually13
public import RequestProject.Pseudorandom.Theorem12
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Theorem 1.3 of Ehard–Glock–Joos (statement and proof)

**Theorem 1.3.** Suppose `δ ∈ (0,1)` and `r ∈ ℕ` with `r ≥ 2`, and let `ε := δ / (50 L² r²)`.
Then there exists `Δ₀` such that for all `Δ ≥ Δ₀` the following holds. Let `H` be an
`r`-uniform hypergraph with `Δ(H) ≤ Δ`, `Δ_c(H) ≤ Δ^{1-δ}` and `e(H) ≤ exp(Δ^{ε²})`. Suppose
that for each `ℓ ∈ [L]` we are given a set `W_ℓ` of clean `ℓ`-tuple weight functions on `E(H)`
of size at most `exp(Δ^{ε²})`, such that `ω(E(H)) ≥ ‖ω‖_k Δ^{k+δ}` for all `ω ∈ W_ℓ` and
`k ∈ [ℓ]`. Then there exists a matching `M` in `H` such that
`ω(M) = (1 ± Δ^{-ε}) ω(E(H)) / Δ^ℓ` for all `ℓ ∈ [L]` and `ω ∈ W_ℓ`.

Formalization choices:
* An `ℓ`-tuple weight function is a function `Finset (Finset V) → ℝ`; only its values on
  `ℓ`-subsets of `H` (i.e. on `H.powersetCard ℓ`) matter, and they must be `≥ 0`.
* `ω(X) = ∑_{S ⊆ X, |S| = ℓ} ω(S)` is `tweight ℓ ω X`, and
  `ω(T) = ∑_{T ⊆ S ⊆ E(H), |S| = ℓ} ω(S)` is `tdeg ℓ ω H T`.
* The family `W_ℓ` is an indexed family `W ℓ : ι ℓ → (Finset (Finset V) → ℝ)` over a finite
  type `ι ℓ` (repetitions are allowed, which only makes the statement more general).
* "clean": `ω(S) = 0` for every `ℓ`-set `S` of edges which is not a matching.
* The condition `ω(E(H)) ≥ ‖ω‖_k Δ^{k+δ}` is written tuple by tuple, and is required only of
  the weight functions for which the conclusion is claimed (this only makes the statement
  more general).
* `ω(M) = (1 ± Δ^{-ε}) ω(E(H))/Δ^ℓ` is written as
  `|ω(M) - ω(E(H))/Δ^ℓ| ≤ Δ^{-ε} ω(E(H))/Δ^ℓ`.
* We assume `L ≥ 1` (for `L = 0` there is nothing to prove).
-/

@[expose] public section

namespace Pseudorandom

open Finset

set_option maxHeartbeats 1000000 in
/-- **Theorem 1.3** (Ehard–Glock–Joos). -/
theorem theorem_1_3 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (r : ℕ) (hr : 2 ≤ r) (L : ℕ)
    (hL : 1 ≤ L) :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)),
      IsUniform H r →
      (∀ v, (degree H v : ℝ) ≤ Δ) →
      (∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ Δ ^ (1 - δ)) →
      (H.card : ℝ) ≤ Real.exp (Δ ^ ((δ / (50 * L ^ 2 * r ^ 2)) ^ 2)) →
      ∀ (ι : ℕ → Type) [∀ ℓ, Fintype (ι ℓ)] (W : (ℓ : ℕ) → ι ℓ → Finset (Finset V) → ℝ),
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ L →
        (Fintype.card (ι ℓ) : ℝ) ≤ Real.exp (Δ ^ ((δ / (50 * L ^ 2 * r ^ 2)) ^ 2))) →
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → ∀ k, ∀ S ∈ H.powersetCard ℓ, 0 ≤ W ℓ k S) →
      (∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → ∀ k, ∀ S ∈ H.powersetCard ℓ, W ℓ k S ≠ 0 → IsMatching S) →
      ∃ M ⊆ H, IsMatching M ∧ ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → ∀ k : ι ℓ,
        (∀ j, 1 ≤ j → j ≤ ℓ → ∀ T ∈ H.powersetCard j,
          tdeg ℓ (W ℓ k) H T * Δ ^ ((j : ℝ) + δ) ≤ tweight ℓ (W ℓ k) H) →
        |tweight ℓ (W ℓ k) M - tweight ℓ (W ℓ k) H / Δ ^ ℓ| ≤
          Δ ^ (-(δ / (50 * L ^ 2 * r ^ 2))) * (tweight ℓ (W ℓ k) H / Δ ^ ℓ) := by
  set ε : ℝ := δ / (50 * L ^ 2 * r ^ 2) with hεdef
  have hR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hR0 : (0 : ℝ) < r := by linarith
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hN : (0 : ℝ) < 50 * L ^ 2 * r ^ 2 := by positivity
  have hεδ : ε * (50 * L ^ 2 * r ^ 2) = δ := by rw [hεdef]; field_simp
  have hε : 0 < ε := by rw [hεdef]; positivity
  -- `c ε < δ` whenever `c < 50 L² r²`
  have key : ∀ c : ℝ, c ≤ 50 * L ^ 2 * r ^ 2 → c * ε ≤ δ := fun c hc => by
    rw [← hεδ, mul_comm ε]; exact mul_le_mul_of_nonneg_right hc hε.le
  have keylt : ∀ c : ℝ, c < 50 * L ^ 2 * r ^ 2 → c * ε < δ := fun c hc => by
    rw [← hεδ, mul_comm ε]; exact mul_lt_mul_of_pos_right hc hε
  have hLr : (2 : ℝ) ≤ L * r := by nlinarith
  have hL2 : (L : ℝ) ≤ L ^ 2 := by nlinarith
  have hε1 : ε < 1 := by
    have := keylt 1 (by nlinarith); linarith
  set a : ℝ := 10 * r * ε with ha
  set b : ℝ := 2 * L * a + 4 * ε with hb
  set ρ : ℝ := 3 / (20 * r) with hρ
  set σ : ℝ := 3 * ε / (20 * r) with hσ
  have ha0 : 0 < a := by positivity
  have hρ0 : 0 < ρ := by positivity
  have hσ0 : 0 ≤ σ := by positivity
  have haρ : a * ρ = 3 / 2 * ε := by rw [ha, hρ]; field_simp; ring
  have haσ : a * σ = 3 / 2 * ε ^ 2 := by rw [ha, hσ]; field_simp; ring
  have hbε : b = (20 * L * r + 4) * ε := by rw [hb, ha]; ring
  have hr1 : ((r - 1 : ℕ) : ℝ) = r - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hr2 : ((2 * r : ℕ) : ℝ) = 2 * r := by push_cast; ring
  have hr3 : ((2 * r * L : ℕ) : ℝ) = 2 * r * L := by push_cast; ring
  have hsum : (2 * r + 4) * ρ + ρ + σ < 1 := by
    have : (2 * r + 4) * ρ + ρ + σ = (6 * r + 15 + 3 * ε) / (20 * r) := by
      rw [hρ, hσ]; field_simp; ring
    rw [this, div_lt_one (by positivity)]
    linarith
  have hb1 : b ≤ 1 := by
    rw [hbε]
    have := key (20 * L * r + 4) (by nlinarith)
    linarith
  have ha5 : 5 * ε ≤ a := by
    have := mul_le_mul_of_nonneg_right (show (5 : ℝ) ≤ 10 * r by linarith) hε.le
    rw [ha]; linarith
  have hp1 : (L : ℝ) * r ^ 2 ≤ L ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_right hL2 (by positivity)
  have hp2 : (r : ℝ) ≤ L ^ 2 * r ^ 2 := by nlinarith
  obtain ⟨D₀, hD₀⟩ := Nibble.nibble_marginal r hr hρ0 hρ0.le hσ0 hsum
  have e2 : b * ((r - 1 : ℕ) : ℝ) < 1 - a := by
    rw [hr1, hbε, ha]
    have := keylt ((20 * L * r + 4) * (r - 1) + 10 * r) (by nlinarith)
    linarith
  have e3 : b * ((r - 1 : ℕ) : ℝ) + (a - δ) < ε := by
    rw [hr1, hbε, ha]
    have := keylt ((20 * L * r + 4) * (r - 1) + 10 * r - 1) (by linarith)
    linarith
  have e5 : b * ((2 * r : ℕ) : ℝ) + ε < δ - 4 * ε := by
    rw [hr2, hbε]
    have := keylt ((20 * L * r + 4) * (2 * r) + 5) (by nlinarith)
    linarith
  have e12 : b * ((2 * r * L : ℕ) : ℝ) + ε < δ - 4 * ε := by
    rw [hr3, hbε]
    have := keylt ((20 * L * r + 4) * (2 * r * L) + 5) (by nlinarith)
    linarith
  have e8 : ε < a * ρ := by rw [haρ]; linarith
  have e9 : ε ^ 2 < a * σ := by
    rw [haσ]; have : 0 < ε ^ 2 := by positivity
    linarith
  have e15 : 2 * ε < a := by rw [ha]; nlinarith
  have e18 : a + ε < b := by rw [hbε, ha]; nlinarith
  obtain ⟨Δ₀, hΔ₀⟩ := Filter.eventually_atTop.mp (eventually_facts13 r L hr hL D₀ hε hε1 ha0
    e2 e3 e5 e8 e9 e8 e12 e15 e18)
  refine ⟨Δ₀, fun Δ hΔ V _ _ H huni hdeg hcod hcard ι _ W hι hW0 hclean => ?_⟩
  exact core_1_3 r L hr hL δ ε a b ρ ρ σ D₀ hε ha0 hb hb1 ha5 hρ0.le hρ0.le hσ0
    (fun D hD V _ _ H => hD₀ D hD V H) Δ (hΔ₀ Δ hΔ) V H huni hdeg hcod hcard ι W hι hW0 hclean

end Pseudorandom
