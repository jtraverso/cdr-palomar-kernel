/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Constantes numéricas del enrutamiento, fijadas ANTES del host (V17, §2)

Dado `α > 0` y `h : ℕ`, se construyen explícitamente

* `compConst α = max 1 ⌈1/α⌉₊` (la constante `C` del conteo de filas activas),
* `routeD α = 12 C²`,
* `routeδ α h = min (α / (8 P)) (1 / C)` con `P = 2 ^ (h choose 2)`,
* `routeN0 α h = ⌈(8 + 4 h P) / α⌉₊ + 1`,

y se prueba (`routeConsts_spec`) que `C ≥ 1`, `δ > 0`, `C δ ≤ 4`, `D ≥ 1`, `12 C² ≤ D + 1`,
y para todo `n ≥ n₀` y todo natural `a ≤ δ n`:

* `a + 2 < α n`,
* `(a + h) · 2^(h choose 2) ≤ α/2 · n`,
* `0 < n`.

Ninguna de estas constantes depende del host, de sus etiquetas, de `n`, de `x` ni del conjunto
de borrado. Sólo se usa Mathlib.
-/

noncomputable section

namespace TypedTriangle.RoutingConstants

/-- `P = 2^(h choose 2)`. -/
def powP (h : ℕ) : ℕ := 2 ^ (h.choose 2)

lemma one_le_powP (h : ℕ) : 1 ≤ powP h := Nat.one_le_two_pow

/-- La constante uniforme del conteo de componentes: `C = max 1 ⌈1/α⌉₊`. -/
def compConst (α : ℝ) : ℕ := max 1 ⌈1 / α⌉₊

lemma one_le_compConst (α : ℝ) : 1 ≤ compConst α := le_max_left _ _

lemma inv_le_compConst (α : ℝ) : 1 / α ≤ (compConst α : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)

/-- `D = 12 C²`. -/
def routeD (α : ℝ) : ℕ := 12 * compConst α ^ 2

/-- `δ = min (α/(8P)) (1/C)`. -/
def routeδ (α : ℝ) (h : ℕ) : ℝ := min (α / (8 * powP h)) (1 / compConst α)

/-- `n₀ = ⌈(8 + 4hP)/α⌉₊ + 1`. -/
def routeN0 (α : ℝ) (h : ℕ) : ℕ := ⌈(8 + 4 * h * (powP h : ℝ)) / α⌉₊ + 1

lemma routeδ_pos {α : ℝ} (hα : 0 < α) (h : ℕ) : 0 < routeδ α h := by
  have hP : (0 : ℝ) < powP h := by exact_mod_cast one_le_powP h
  have hC : (0 : ℝ) < compConst α := by exact_mod_cast one_le_compConst α
  exact lt_min (by positivity) (by positivity)

lemma compConst_mul_routeδ_le (α : ℝ) (h : ℕ) : (compConst α : ℝ) * routeδ α h ≤ 4 := by
  have hC : (0 : ℝ) < compConst α := by exact_mod_cast one_le_compConst α
  calc (compConst α : ℝ) * routeδ α h ≤ compConst α * (1 / compConst α) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
    _ = 1 := by field_simp
    _ ≤ 4 := by norm_num

lemma one_le_routeD (α : ℝ) : 1 ≤ routeD α := by
  have := one_le_compConst α
  unfold routeD; nlinarith

lemma routeD_spec (α : ℝ) : 12 * compConst α ^ 2 ≤ routeD α + 1 := by
  unfold routeD; omega

lemma routeN0_pos (α : ℝ) (h : ℕ) : 0 < routeN0 α h := Nat.succ_pos _

/-- Para `n ≥ n₀`: `α n > 8 + 4 h P`. -/
lemma alpha_mul_gt {α : ℝ} (hα : 0 < α) (h : ℕ) {n : ℕ} (hn : routeN0 α h ≤ n) :
    8 + 4 * h * (powP h : ℝ) < α * n := by
  have h1 : (8 + 4 * h * (powP h : ℝ)) / α ≤ ⌈(8 + 4 * h * (powP h : ℝ)) / α⌉₊ := Nat.le_ceil _
  have h2 : ((⌈(8 + 4 * h * (powP h : ℝ)) / α⌉₊ : ℕ) : ℝ) + 1 ≤ n := by
    have hn' : ⌈(8 + 4 * h * (powP h : ℝ)) / α⌉₊ + 1 ≤ n := hn
    exact_mod_cast hn'
  have h3 : (8 + 4 * h * (powP h : ℝ)) / α < n := by linarith
  rw [div_lt_iff₀ hα] at h3
  linarith

/-- Las dos ventanas numéricas, para `n ≥ n₀` y `a ≤ δ n` natural. -/
theorem routeWindows {α : ℝ} (hα : 0 < α) (h : ℕ) {n : ℕ} (hn : routeN0 α h ≤ n) {a : ℕ}
    (ha : (a : ℝ) ≤ routeδ α h * n) :
    (a : ℝ) + 2 < α * n ∧ ((a : ℝ) + h) * (2 : ℝ) ^ (h.choose 2) ≤ α / 2 * n := by
  have hP1 : (1 : ℝ) ≤ powP h := by exact_mod_cast one_le_powP h
  have hP : (0 : ℝ) < powP h := by linarith
  have hgt := alpha_mul_gt hα h hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha' : (a : ℝ) ≤ α / (8 * powP h) * n :=
    ha.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
  have haP : (a : ℝ) * powP h ≤ α * n / 8 := by
    calc (a : ℝ) * powP h ≤ (α / (8 * powP h) * n) * powP h :=
          mul_le_mul_of_nonneg_right ha' hP.le
      _ = α * n / 8 := by field_simp
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have haa : (a : ℝ) ≤ a * powP h := le_mul_of_one_le_right ha0 hP1
  have hPcast : (2 : ℝ) ^ (h.choose 2) = powP h := by simp [powP]
  have hhP : 0 ≤ (h : ℝ) * powP h := mul_nonneg hh0 hP.le
  refine ⟨by linarith, ?_⟩
  rw [hPcast]
  nlinarith

/-- **Constantes del enrutamiento fijadas antes del host.** -/
theorem routeConsts_spec {α : ℝ} (hα : 0 < α) (h : ℕ) :
    1 ≤ compConst α ∧ 0 < routeδ α h ∧ (compConst α : ℝ) * routeδ α h ≤ 4 ∧
      1 ≤ routeD α ∧ 12 * compConst α ^ 2 ≤ routeD α + 1 ∧
      ∀ n : ℕ, routeN0 α h ≤ n → 0 < n ∧ ∀ a : ℕ, (a : ℝ) ≤ routeδ α h * n →
        (a : ℝ) + 2 < α * n ∧ ((a : ℝ) + h) * (2 : ℝ) ^ (h.choose 2) ≤ α / 2 * n :=
  ⟨one_le_compConst α, routeδ_pos hα h, compConst_mul_routeδ_le α h, one_le_routeD α,
    routeD_spec α, fun _ hn => ⟨lt_of_lt_of_le (routeN0_pos α h) hn,
      fun _ ha => routeWindows hα h hn ha⟩⟩

/-- Forma existencial: `C, D, δ, n₀` elegidos antes de todo host, con `C = compConst α`. -/
theorem exists_routeConsts {α : ℝ} (hα : 0 < α) (h : ℕ) :
    ∃ C D : ℕ, ∃ δ : ℝ, ∃ n₀ : ℕ, C = compConst α ∧
      1 ≤ C ∧ 0 < δ ∧ (C : ℝ) * δ ≤ 4 ∧ 1 ≤ D ∧ 12 * C ^ 2 ≤ D + 1 ∧
      ∀ n : ℕ, n₀ ≤ n → 0 < n ∧ ∀ a : ℕ, (a : ℝ) ≤ δ * n →
        (a : ℝ) + 2 < α * n ∧ ((a : ℝ) + h) * (2 : ℝ) ^ (h.choose 2) ≤ α / 2 * n :=
  ⟨compConst α, routeD α, routeδ α h, routeN0 α h, rfl, routeConsts_spec hα h⟩

end TypedTriangle.RoutingConstants
