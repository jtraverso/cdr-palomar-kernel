/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# V27 — constants of the core selector layer, fixed before the host

From the V25 constants `t` (odd route length) and `ε` (route robustness):

* `selA t = 200 t + 8` (the per-root auxiliary factor `|W_v| ≤ A·|N_X(v)|`);
* `selEps ε A = e² / (10⁴·A)`, `e = min ε 1` (the admissible degree scale `r, b ≤ εS·n`);
* `selQ ε A r = ⌈4·A·r / e⌉₊ + 1` (the auxiliary-use counter; a function of `r` only).

`selector_window`: if `r, b ≤ εS·n` and `e·n ≥ 200`, then the two windows of the core layer
hold: the vertex window (saturation `A·r·n/q ≤ e·n/4`, paid by the total `A·r·n` positions)
fits the route budget `⌊εn⌋`, and the forbidden edge degree `b + 61r + 60q + 60 ≤ εn`.
-/

namespace S07V27

/-- the per-root auxiliary factor -/
def selA (t : ℕ) : ℕ := 200 * t + 8

/-- the degree scale of the layer -/
noncomputable def selEps (ε : ℝ) (A : ℕ) : ℝ := (min ε 1) ^ 2 / (10 ^ 4 * A)

/-- the auxiliary-use counter -/
noncomputable def selQ (ε : ℝ) (A r : ℕ) : ℕ := ⌈4 * (A : ℝ) * r / min ε 1⌉₊ + 1

lemma selEps_pos {ε : ℝ} (hε : 0 < ε) {A : ℕ} (hA : 0 < A) : 0 < selEps ε A := by
  unfold selEps
  have : 0 < min ε 1 := lt_min hε one_pos
  positivity

lemma selQ_pos (ε : ℝ) (A r : ℕ) : 0 < selQ ε A r := by unfold selQ; omega

/-- **The windows of the core layer hold with the fixed constants.** -/
theorem selector_window {ε : ℝ} (hε : 0 < ε) {t A n r b : ℕ} (hA : 200 * t + 8 ≤ A)
    (hr : (r : ℝ) ≤ selEps ε A * n) (hb : (b : ℝ) ≤ selEps ε A * n)
    (hn : 200 ≤ min ε 1 * n) :
    r + b + A * r * n / selQ ε A r + (A + 1) * r + 10 * r + (t - 1) * (200 * r) ≤
      ⌊ε * n⌋₊ ∧
    ((b + 61 * r + 60 * selQ ε A r + 60 : ℕ) : ℝ) ≤ ε * n := by
  set e := min ε 1 with he
  have he0 : 0 < e := lt_min hε one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  have hA8 : (8 : ℝ) ≤ A := by exact_mod_cast (show 8 ≤ A by omega)
  have hA0 : (0 : ℝ) < A := by linarith
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set q := selQ ε A r with hqdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast selQ_pos ε A r
  -- `q ≥ 4Ar/e` and `q ≤ 4Ar/e + 2`
  have hx0 : 0 ≤ 4 * (A : ℝ) * r / e := by positivity
  have hqlo : 4 * (A : ℝ) * r / e ≤ q := by
    rw [hqdef, selQ]; push_cast
    have := Nat.le_ceil (4 * (A : ℝ) * r / e); linarith
  have hqhi : (q : ℝ) ≤ 4 * (A : ℝ) * r / e + 2 := by
    rw [hqdef, selQ]; push_cast
    have := Nat.ceil_lt_add_one hx0; linarith
  -- `A·r ≤ e²n/10⁴`, `r, b ≤ e n/(8·10⁴)`
  have hεS : selEps ε A * n = e ^ 2 * n / (10 ^ 4 * A) := by
    rw [selEps]; ring
  have hAr : (A : ℝ) * r ≤ e ^ 2 * n / 10 ^ 4 := by
    have := mul_le_mul_of_nonneg_left hr hA0.le
    rw [hεS] at this
    calc (A : ℝ) * r ≤ A * (e ^ 2 * n / (10 ^ 4 * A)) := this
      _ = e ^ 2 * n / 10 ^ 4 := by field_simp
  have hee : e ^ 2 * n ≤ e * n := by
    have : e ^ 2 ≤ e := by nlinarith
    exact mul_le_mul_of_nonneg_right this hN
  have hsmall : ∀ x : ℕ, (x : ℝ) ≤ selEps ε A * n → (x : ℝ) ≤ e * n / (8 * 10 ^ 4) := by
    intro x hx
    rw [hεS] at hx
    have h1 : e ^ 2 * n / (10 ^ 4 * A) ≤ e ^ 2 * n / (10 ^ 4 * 8) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    have h2 : e ^ 2 * n / (10 ^ 4 * 8) ≤ e * n / (8 * 10 ^ 4) := by
      rw [mul_comm (10 ^ 4 : ℝ) 8]
      exact div_le_div_of_nonneg_right hee (by positivity)
    linarith
  have hr' := hsmall r hr
  have hb' := hsmall b hb
  have hArn : (A : ℝ) * r * n / q ≤ e * n / 4 := by
    rw [div_le_iff₀ hq0]
    have h1 : 4 * (A : ℝ) * r ≤ e * q := by
      have := hqlo; rw [div_le_iff₀ he0] at this; linarith
    nlinarith
  constructor
  · apply Nat.le_floor
    have hD : ((A * r * n / q : ℕ) : ℝ) ≤ e * n / 4 :=
      (Nat.cast_div_le).trans (by push_cast; exact hArn)
    have ht1 : ((t - 1 : ℕ) : ℝ) * (200 * r) ≤ A * r := by
      have : (t - 1) * (200 * r) ≤ A * r := by
        calc (t - 1) * (200 * r) = (200 * (t - 1)) * r := by ring
          _ ≤ A * r := Nat.mul_le_mul_right _ (by omega)
      exact_mod_cast this
    push_cast
    nlinarith
  · have h4 : 4 * (A : ℝ) * r / e ≤ 4 * e * n / 10 ^ 4 := by
      rw [div_le_iff₀ he0]
      nlinarith
    push_cast
    nlinarith

end S07V27
