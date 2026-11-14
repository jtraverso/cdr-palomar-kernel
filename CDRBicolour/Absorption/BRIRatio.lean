/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.BRIFinal

/-!
# The bounded right inverse for unbalanced classes

`bri_of_balanced` assumes `n ≤ 4m` (every class at least a quarter of the points). The balance
enters only through inequalities `n ≤ C m²` and `n³ ≤ C m⁴`, which persist for `n ≤ R m` once
`m ≥ 64 R³`. Here `R ≥ 1` is arbitrary:

* `chain_bounds_A`: the chain weights with `a ≤ A M`;
* `abs_xU_le_R`, `abs_Gc_le_R`, `abs_Phi0_le_R`: `|Φ₀ d T| ≤ 200 R⁵ ‖d‖ / n` on `ker ℓ`;
* `norm_err_le_R`: the error `I − M Φ₀` halves norms on `ker ℓ`;
* `bri_of_ratio`: a bounded right inverse with `K = 400 R⁵`.

Used to glue bounded right inverses of three-class sub-hosts of a `k`-class host whose classes
are not balanced (geometric profiles).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption

open Finset TypedTriangle CDRBicolour.Prefix

/-- **The chain weights are bounded** (`a ≤ A M`). -/
theorem chain_bounds_A {a b c M B A : ℝ} (G : Fin 3 → Fin 3 → ℝ) (hM : 2 ≤ M) (hA : 0 ≤ A)
    (ha : M + 1 ≤ a) (hb : M + 1 ≤ b) (hc : M + 1 ≤ c) (ha' : a ≤ A * M)
    (hG : ∀ X Y, |G X Y| ≤ B) :
    |xAAB b G| ≤ B / M ∧ |xACC c G| ≤ B / M ∧ |xABB a b G| ≤ (1 + A) * B / M ∧
      |xBCC a b c G| ≤ (1 + A) * B / M ∧ |xBBC a b c G| ≤ (1 + A * (1 + A)) * B / M := by
  have hM0 : 0 < M := by linarith
  have hB : 0 ≤ B := (abs_nonneg _).trans (hG 0 0)
  have e1 : |xAAB b G| ≤ B / M := abs_div_le_of (hG 0 0) (by linarith) hM0
  have e2 : |xACC c G| ≤ B / M := abs_div_le_of (hG 0 2) (by linarith) hM0
  have hprod : ∀ {x y C : ℝ}, 0 ≤ x → x ≤ A * M → 0 ≤ C → |y| ≤ C * B / M →
      |x * y| ≤ A * C * B := by
    intro x y C hx hxM hC hy
    rw [abs_mul, abs_of_nonneg hx]
    calc x * |y| ≤ A * M * (C * B / M) := mul_le_mul hxM hy (abs_nonneg _) (by positivity)
      _ = A * C * B := by field_simp
  have e1' : |xAAB b G| ≤ 1 * B / M := by rw [one_mul]; exact e1
  have e2' : |xACC c G| ≤ 1 * B / M := by rw [one_mul]; exact e2
  have e3 : |xABB a b G| ≤ (1 + A) * B / M := by
    apply abs_div_le_of _ (by linarith) hM0
    calc |G 0 1 - (a - 1) * xAAB b G| ≤ |G 0 1| + |(a - 1) * xAAB b G| := abs_sub _ _
      _ ≤ B + A * 1 * B :=
          add_le_add (hG 0 1) (hprod (by linarith) (by linarith) zero_le_one e1')
      _ = (1 + A) * B := by ring
  have e4 : |xBCC a b c G| ≤ (1 + A) * B / M := by
    apply abs_div_le_of _ (by linarith) hM0
    calc |G 2 2 - a * xACC c G| ≤ |G 2 2| + |a * xACC c G| := abs_sub _ _
      _ ≤ B + A * 1 * B := add_le_add (hG 2 2) (hprod (by linarith) ha' zero_le_one e2')
      _ = (1 + A) * B := by ring
  have e5 : |xBBC a b c G| ≤ (1 + A * (1 + A)) * B / M := by
    apply abs_div_le_of _ (by linarith) hM0
    calc |G 1 1 - a * xABB a b G| ≤ |G 1 1| + |a * xABB a b G| := abs_sub _ _
      _ ≤ B + A * (1 + A) * B :=
          add_le_add (hG 1 1) (hprod (by linarith) ha' (by positivity) e3)
      _ = (1 + A * (1 + A)) * B := by ring
  exact ⟨e1, e2, e3, e4, e5⟩

/-- A polynomial inequality for the final constant. -/
theorem poly_R5 {R : ℝ} (hR : 1 ≤ R) :
    108 * R ^ 2 + 2 * R * (1 + 2 * R * (1 + 2 * R)) * (4 * R ^ 2 + 1) ≤ 200 * R ^ 5 := by
  have h1 : R ≤ R ^ 5 := by
    calc R = R ^ 1 := (pow_one R).symm
      _ ≤ R ^ 5 := pow_le_pow_right₀ hR (by norm_num)
  have h2 : R ^ 2 ≤ R ^ 5 := pow_le_pow_right₀ hR (by norm_num)
  have h3 : R ^ 3 ≤ R ^ 5 := pow_le_pow_right₀ hR (by norm_num)
  have h4 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR (by norm_num)
  have e : 108 * R ^ 2 + 2 * R * (1 + 2 * R * (1 + 2 * R)) * (4 * R ^ 2 + 1) =
      32 * R ^ 5 + 16 * R ^ 4 + 16 * R ^ 3 + 112 * R ^ 2 + 2 * R := by ring
  rw [e]
  linarith

section Ratio

variable {V : Type*} [Fintype V] [DecidableEq V] {lab : V → Fin 3}

theorem abs_xU_le_R {m : ℕ} {R : ℝ} (hR : 1 ≤ R) (hm : ∀ k, m ≤ csz lab k) (h3 : 3 ≤ m)
    (hbal : (Fintype.card V : ℝ) ≤ R * m) {B : ℝ} (G : Fin 3 → Fin 3 → ℝ)
    (hG : ∀ X Y, |G X Y| ≤ B) (mm : Multiset (Fin 3)) :
    |xU lab G mm| ≤ (1 + 2 * R * (1 + 2 * R)) * B / ((m : ℝ) - 1) := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast h3
  have hB : 0 ≤ B := (abs_nonneg _).trans (hG 0 0)
  have hx : ∀ k, (m : ℝ) ≤ csz lab k := fun k => by exact_mod_cast hm k
  have hcV : ∀ k, (csz lab k : ℝ) ≤ Fintype.card V := fun k => by
    have : csz lab k ≤ Fintype.card V := by
      unfold csz; exact (card_filter_le _ _).trans_eq card_univ
    exact_mod_cast this
  have hM : (2 : ℝ) ≤ (m : ℝ) - 1 := by linarith
  have hRm : R * m ≤ 2 * R * ((m : ℝ) - 1) := by nlinarith
  have ha' : (csz lab 0 : ℝ) ≤ 2 * R * ((m : ℝ) - 1) := by linarith [hcV 0]
  obtain ⟨e1, e2, e3, e4, e5⟩ := chain_bounds_A (a := (csz lab 0 : ℝ)) (b := (csz lab 1 : ℝ))
    (c := (csz lab 2 : ℝ)) G hM (by linarith) (by linarith [hx 0]) (by linarith [hx 1])
    (by linarith [hx 2]) ha' hG
  have hM0 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  set C : ℝ := 1 + 2 * R * (1 + 2 * R) with hC
  have hC1 : 1 ≤ C := by rw [hC]; nlinarith
  have hCA : 1 + 2 * R ≤ C := by rw [hC]; nlinarith
  have l1 : B / ((m : ℝ) - 1) ≤ C * B / ((m : ℝ) - 1) :=
    div_le_div_of_nonneg_right (by nlinarith) hM0.le
  have l7 : (1 + 2 * R) * B / ((m : ℝ) - 1) ≤ C * B / ((m : ℝ) - 1) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCA hB) hM0.le
  have l0 : (0 : ℝ) ≤ C * B / ((m : ℝ) - 1) := by
    apply div_nonneg _ hM0.le; nlinarith
  unfold xU
  split_ifs
  · exact e1.trans l1
  · simp [xAAC]; exact l0
  · exact e5
  · exact e3.trans l7
  · exact e2.trans l1
  · exact e4.trans l7
  · simp; exact l0

/-- The type values of `Φ₀` are bounded on `ker ℓ` (ratio `R`). -/
theorem abs_Gc_le_R {m : ℕ} {R : ℝ} (hR : 1 ≤ R) (hm : ∀ k, m ≤ csz lab k) (h512 : 512 ≤ m)
    (hmR : 64 * R ^ 3 ≤ m) (hbal : (Fintype.card V : ℝ) ≤ R * m) (d : E0 V → ℝ)
    (hd : ell lab d = 0) (X Y : Fin 3) :
    |Gc lab d X Y| ≤ (4 * R ^ 2 + 1) * ‖d‖ := by
  have h3 : 3 ≤ m := by omega
  have hcls : ∀ k, 3 ≤ csz lab k := fun k => (hm k).trans' h3
  have hmR' : (512 : ℝ) ≤ m := by exact_mod_cast h512
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hR0 : (0 : ℝ) ≤ R := by linarith
  set n : ℝ := (Fintype.card V : ℝ)
  set P : ℝ := ((m : ℝ) - 1) * ((m : ℝ) - 1)
  have hP : (m : ℝ) ^ 2 / 2 ≤ P := by simp only [P]; nlinarith
  have hPpos : 0 < P := lt_of_lt_of_le (by positivity) hP
  have hPe : ∀ e : E0 V, P ≤ #(pairsF lab (rep e).1 (rep e).2) := by
    intro e
    have := card_pairsF_ge hm (rep e).1 (rep e).2
    have h1 : 1 ≤ m := by omega
    have : ((m - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ) ≤ #(pairsF lab (rep e).1 (rep e).2) := by
      exact_mod_cast this
    rwa [Nat.cast_sub h1, Nat.cast_one] at this
  have hut : ∀ e : E0 V, |ut lab e X Y| ≤ 2 / P := by
    intro e
    unfold ut
    have hc : (0 : ℝ) < #(pairsF lab (rep e).1 (rep e).2) := lt_of_lt_of_le hPpos (hPe e)
    rw [abs_mul, abs_of_pos (by positivity)]
    have h2 : |(if matchQ lab (rep e).1 (rep e).2 X Y then (1 : ℝ) else 0) +
        (if matchQ lab (rep e).1 (rep e).2 Y X then 1 else 0)| ≤ 2 := by
      split_ifs <;> norm_num
    calc 1 / (#(pairsF lab (rep e).1 (rep e).2) : ℝ) * |_| ≤ 1 / P * 2 :=
          mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hPpos (hPe e)) h2 (abs_nonneg _)
            (by positivity)
      _ = 2 / P := by ring
  have hn2 : n ^ 2 ≤ R ^ 2 * (m : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ hn0 hbal 2; rwa [mul_pow] at this
  have hGfun : |Gfun lab d X Y| ≤ 4 * R ^ 2 * ‖d‖ := by
    unfold Gfun
    calc |∑ e, d e * ut lab e X Y| ≤ ∑ e, |d e * ut lab e X Y| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e : E0 V, ‖d‖ * (2 / P) := sum_le_sum fun e _ => by
          rw [abs_mul]
          exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm d e) (hut e)
            (abs_nonneg _) (norm_nonneg _)
      _ = Fintype.card (E0 V) * (‖d‖ * (2 / P)) := by rw [sum_const, nsmul_eq_mul, card_univ]
      _ ≤ n ^ 2 * (‖d‖ * (2 / P)) := mul_le_mul_of_nonneg_right card_E0_le (by positivity)
      _ ≤ 4 * R ^ 2 * ‖d‖ := by
          rw [show n ^ 2 * (‖d‖ * (2 / P)) = ‖d‖ * (2 * n ^ 2 / P) by ring]
          have : 2 * n ^ 2 / P ≤ 4 * R ^ 2 := by
            rw [div_le_iff₀ hPpos]
            have := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 4 * R ^ 2)
            nlinarith
          have := mul_le_mul_of_nonneg_left this (norm_nonneg d)
          linarith
  have hlam := abs_lam_le hcls hm h3 d hd
  have c2 : n ^ 2 * (2 * n / P) / (3 * (m : ℝ) ^ 2) ≤ 1 := by
    rw [div_le_iff₀ (by positivity), show n ^ 2 * (2 * n / P) = 2 * n ^ 3 / P by ring,
      div_le_iff₀ hPpos]
    have hn3 : n ^ 3 ≤ R ^ 3 * (m : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ hn0 hbal 3; rwa [mul_pow] at this
    have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ 3 := by positivity
    have h4 : 64 * R ^ 3 * (m : ℝ) ^ 3 ≤ (m : ℝ) ^ 4 := by
      have := mul_le_mul_of_nonneg_right hmR hm0; nlinarith
    have hPm : 1 * (3 * (m : ℝ) ^ 2) * ((m : ℝ) ^ 2 / 2) ≤ 1 * (3 * (m : ℝ) ^ 2) * P :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    nlinarith
  have hl : |lam lab d| ≤ ‖d‖ := by
    calc |lam lab d| ≤ ‖d‖ * n ^ 2 * (2 * n / P) / (3 * (m : ℝ) ^ 2) := hlam
      _ = ‖d‖ * (n ^ 2 * (2 * n / P) / (3 * (m : ℝ) ^ 2)) := by ring
      _ ≤ ‖d‖ * 1 := mul_le_mul_of_nonneg_left c2 (norm_nonneg _)
      _ = ‖d‖ := mul_one _
  have hfix : |Gfix X Y| ≤ 1 := by unfold Gfix; split_ifs <;> norm_num
  unfold Gc
  calc |Gfun lab d X Y - lam lab d * Gfix X Y| ≤ |Gfun lab d X Y| + |lam lab d * Gfix X Y| :=
        abs_sub _ _
    _ ≤ 4 * R ^ 2 * ‖d‖ + ‖d‖ * 1 := add_le_add hGfun (by
        rw [abs_mul]; exact mul_le_mul hl hfix (abs_nonneg _) (norm_nonneg _))
    _ = (4 * R ^ 2 + 1) * ‖d‖ := by ring

/-- **`Φ₀` is bounded on `ker ℓ`** (ratio `R`). -/
theorem abs_Phi0_le_R {m : ℕ} {R : ℝ} (hR : 1 ≤ R) (hm : ∀ k, m ≤ csz lab k) (h512 : 512 ≤ m)
    (hmR : 64 * R ^ 3 ≤ m) (hbal : (Fintype.card V : ℝ) ≤ R * m) (d : E0 V → ℝ)
    (hd : ell lab d = 0) (T : Finset V) :
    |Phi0 lab d T| ≤ 200 * R ^ 5 / Fintype.card V * ‖d‖ := by
  have h3 : 3 ≤ m := by omega
  have hmR' : (512 : ℝ) ≤ m := by exact_mod_cast h512
  have hx : (m : ℝ) ≤ csz lab 0 := by exact_mod_cast hm 0
  have hcV : (csz lab 0 : ℝ) ≤ Fintype.card V := by
    have : csz lab 0 ≤ Fintype.card V := by
      unfold csz; exact (card_filter_le _ _).trans_eq card_univ
    exact_mod_cast this
  have hnpos : (0 : ℝ) < Fintype.card V := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  set n : ℝ := (Fintype.card V : ℝ)
  have h1 := abs_Phi1_le hm h3 d T
  have h2 := abs_xU_le_R hR hm h3 hbal (Gc lab d) (abs_Gc_le_R hR hm h512 hmR hbal d hd)
    (T.val.map lab)
  have hsplit : Phi0 lab d T = Phi1 lab d T + xU lab (Gc lab d) (T.val.map lab) := rfl
  rw [hsplit]
  have hM0 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hnm : n ≤ R * m := hbal
  -- `m - 1 ≥ n / (2R)` and `(m - 1)² ≥ n² / (2R²)`
  have hM : n ≤ 2 * R * ((m : ℝ) - 1) := by nlinarith
  have hsq : n ^ 2 ≤ 2 * R ^ 2 * (((m : ℝ) - 1) * ((m : ℝ) - 1)) := by
    have hP : (m : ℝ) ^ 2 / 2 ≤ ((m : ℝ) - 1) * ((m : ℝ) - 1) := by nlinarith
    have hn2 : n ^ 2 ≤ R ^ 2 * (m : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ hnpos.le hnm 2; rwa [mul_pow] at this
    have := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 2 * R ^ 2)
    nlinarith
  have a1 : 54 * n * ‖d‖ / (((m : ℝ) - 1) * ((m : ℝ) - 1)) ≤ 108 * R ^ 2 / n * ‖d‖ := by
    rw [div_le_iff₀ (by positivity)]
    have : 108 * R ^ 2 / n * ‖d‖ * (((m : ℝ) - 1) * ((m : ℝ) - 1)) ≥
        108 * R ^ 2 / n * ‖d‖ * (n ^ 2 / (2 * R ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_iff₀ (by positivity)]; linarith
    have e : 108 * R ^ 2 / n * ‖d‖ * (n ^ 2 / (2 * R ^ 2)) = 54 * n * ‖d‖ := by
      field_simp; ring
    linarith
  set C : ℝ := 1 + 2 * R * (1 + 2 * R) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have a2 : C * ((4 * R ^ 2 + 1) * ‖d‖) / ((m : ℝ) - 1) ≤
      2 * R * C * (4 * R ^ 2 + 1) / n * ‖d‖ := by
    rw [div_le_iff₀ hM0]
    have : 2 * R * C * (4 * R ^ 2 + 1) / n * ‖d‖ * ((m : ℝ) - 1) ≥
        2 * R * C * (4 * R ^ 2 + 1) / n * ‖d‖ * (n / (2 * R)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_iff₀ (by positivity)]; linarith
    have e : 2 * R * C * (4 * R ^ 2 + 1) / n * ‖d‖ * (n / (2 * R)) =
        C * ((4 * R ^ 2 + 1) * ‖d‖) := by field_simp
    linarith
  have hpoly := poly_R5 hR
  calc |Phi1 lab d T + xU lab (Gc lab d) (T.val.map lab)|
      ≤ |Phi1 lab d T| + |xU lab (Gc lab d) (T.val.map lab)| := abs_add_le _ _
    _ ≤ 108 * R ^ 2 / n * ‖d‖ + 2 * R * C * (4 * R ^ 2 + 1) / n * ‖d‖ :=
        add_le_add (h1.trans a1) (h2.trans a2)
    _ = (108 * R ^ 2 + 2 * R * C * (4 * R ^ 2 + 1)) * (1 / n * ‖d‖) := by ring
    _ ≤ 200 * R ^ 5 * (1 / n * ‖d‖) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hC]; linarith
    _ = 200 * R ^ 5 / n * ‖d‖ := by ring

/-- **The error of `Φ₀` halves norms on `ker ℓ`** (ratio `R`). -/
theorem norm_err_le_R (hcls : ∀ k, 3 ≤ csz lab k) {m : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (hm : ∀ k, m ≤ csz lab k) (h512 : 512 ≤ m) (hmR : 64 * R ^ 3 ≤ m)
    (hbal : (Fintype.card V : ℝ) ≤ R * m) (d : E0 V → ℝ) (hd : ell lab d = 0) :
    ‖d - Minc lab (Phi0 lab d)‖ ≤ ‖d‖ / 2 := by
  have h3 : 3 ≤ m := by omega
  have hmR' : (512 : ℝ) ≤ m := by exact_mod_cast h512
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hx : ∀ k, (m : ℝ) ≤ csz lab k := fun k => by exact_mod_cast hm k
  have hS : S0 lab ≠ 0 := by
    have : 3 * (m : ℝ) ^ 2 ≤ S0 lab := by rw [S0_eq]; nlinarith [hx 0, hx 1, hx 2]
    have : (0 : ℝ) < S0 lab := lt_of_lt_of_le (by positivity) this
    exact this.ne'
  set n : ℝ := (Fintype.card V : ℝ)
  set P : ℝ := ((m : ℝ) - 1) * ((m : ℝ) - 1)
  have hP : (m : ℝ) ^ 2 / 2 ≤ P := by simp only [P]; nlinarith
  have hPpos : 0 < P := lt_of_lt_of_le (by positivity) hP
  have hR3 : R ≤ R ^ 3 := by
    calc R = R ^ 1 := (pow_one R).symm
      _ ≤ R ^ 3 := pow_le_pow_right₀ hR (by norm_num)
  have c1 : 8 * n / P ≤ 1 / 4 := by
    rw [div_le_iff₀ hPpos]
    have h64 : 64 * R ≤ m := by linarith
    have : 64 * R * (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    nlinarith
  have c2 : n ^ 2 * (2 * n / P) / (3 * (m : ℝ) ^ 2) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity), show n ^ 2 * (2 * n / P) = 2 * n ^ 3 / P by ring,
      div_le_iff₀ hPpos]
    have hn3 : n ^ 3 ≤ R ^ 3 * (m : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ hn0 hbal 3; rwa [mul_pow] at this
    have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ 3 := by positivity
    have h4 : 64 * R ^ 3 * (m : ℝ) ^ 3 ≤ (m : ℝ) ^ 4 := by
      have := mul_le_mul_of_nonneg_right hmR hm0; nlinarith
    have hPm : 1 / 4 * (3 * (m : ℝ) ^ 2) * ((m : ℝ) ^ 2 / 2) ≤
        1 / 4 * (3 * (m : ℝ) ^ 2) * P := mul_le_mul_of_nonneg_left hP (by positivity)
    nlinarith
  have hlam := abs_lam_le hcls hm h3 d hd
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun f => ?_
  rw [Real.norm_eq_abs]
  show |d f - Minc lab (Phi0 lab d) f| ≤ _
  rw [err_eq hcls hS]
  have hloc := abs_local_le hcls hm h3 d f
  have hfix : |Gfix (lab (rep f).1) (lab (rep f).2)| ≤ 1 := by
    unfold Gfix; split_ifs <;> norm_num
  have hl2 : |lam lab d * Gfix (lab (rep f).1) (lab (rep f).2)| ≤ ‖d‖ * (1 / 4) := by
    rw [abs_mul]
    calc |lam lab d| * |Gfix _ _| ≤ |lam lab d| * 1 :=
          mul_le_mul_of_nonneg_left hfix (abs_nonneg _)
      _ ≤ ‖d‖ * n ^ 2 * (2 * n / P) / (3 * (m : ℝ) ^ 2) := by rw [mul_one]; exact hlam
      _ = ‖d‖ * (n ^ 2 * (2 * n / P) / (3 * (m : ℝ) ^ 2)) := by ring
      _ ≤ ‖d‖ * (1 / 4) := mul_le_mul_of_nonneg_left c2 (norm_nonneg _)
  have hl1 : ‖d‖ * (8 * n / P) ≤ ‖d‖ * (1 / 4) := mul_le_mul_of_nonneg_left c1 (norm_nonneg _)
  calc _ ≤ |∑ e, d e * (avgW lab e f - ut lab e (lab (rep f).1) (lab (rep f).2))| +
        |lam lab d * Gfix (lab (rep f).1) (lab (rep f).2)| := abs_add_le _ _
    _ ≤ ‖d‖ * (1 / 4) + ‖d‖ * (1 / 4) := add_le_add (hloc.trans hl1) hl2
    _ = ‖d‖ / 2 := by ring

/-- **The bounded right inverse for unbalanced classes**: `K = 400 R⁵`. -/
theorem bri_of_ratio {m : ℕ} {R : ℝ} (hR : 1 ≤ R) (hm : ∀ k, m ≤ csz lab k) (h512 : 512 ≤ m)
    (hmR : 64 * R ^ 3 ≤ m) (hbal : (Fintype.card V : ℝ) ≤ R * m) :
    Nonempty (BRI lab (400 * R ^ 5)) := by
  have h3 : 3 ≤ m := by omega
  have hcls : ∀ k, 3 ≤ csz lab k := fun k => (hm k).trans' h3
  have hex : ∀ k : Fin 3, ∃ u, lab u = k := by
    intro k
    have := hm k
    unfold csz at this
    obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < #(univ.filter fun v => lab v = k))
    exact ⟨u, (mem_filter.mp hu).2⟩
  obtain ⟨u, hu⟩ := hex 0
  obtain ⟨v, hv⟩ := hex 1
  have huv : u ≠ v := fun h => by rw [h, hv] at hu; exact absurd hu (by decide)
  let e0 : E0 V := ⟨s(u, v), by simpa using huv⟩
  let δ0 : E0 V → ℝ := Pi.single e0 1
  have hδ : ell lab δ0 = 1 := by
    simp only [ell, LinearMap.coe_mk, AddHom.coe_mk, δ0]
    rw [Finset.sum_eq_single e0]
    · simp [e0, wl, hu, hv]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · intro h; exact absurd (mem_univ e0) h
  let W : Submodule ℝ (E0 V → ℝ) := LinearMap.ker (ell lab)
  let F : (E0 V → ℝ) →ₗ[ℝ] (E0 V → ℝ) := Minc lab ∘ₗ Phi0 lab
  have hFW : ∀ x ∈ W, F x ∈ W := fun x _ => LinearMap.mem_ker.mpr (ell_M _)
  have hcontr : ∀ x ∈ W, ‖x‖ ≤ 2 * ‖F x‖ := by
    intro x hx
    have h1 := norm_err_le_R hcls hR hm h512 hmR hbal x (LinearMap.mem_ker.mp hx)
    have h2 : ‖x‖ - ‖F x‖ ≤ ‖x - F x‖ := norm_sub_norm_le _ _
    have : ‖x - F x‖ = ‖x - Minc lab (Phi0 lab x)‖ := rfl
    linarith
  let f : W →ₗ[ℝ] W := F.restrict hFW
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : F x = 0 := congrArg Subtype.val hx
    have := hcontr x x.2
    rw [h0, norm_zero, mul_zero] at this
    exact Subtype.ext (norm_le_zero_iff.mp this)
  let eqv : W ≃ₗ[ℝ] W :=
    LinearEquiv.ofBijective f ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let g : (E0 V → ℝ) →ₗ[ℝ] (E0 V → ℝ) := LinearMap.id - (ell lab).smulRight δ0
  have hg : ∀ d, g d ∈ W := by
    intro d
    apply LinearMap.mem_ker.mpr
    simp only [g, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub,
      map_smul, hδ, smul_eq_mul, mul_one, sub_self]
  let proj : (E0 V → ℝ) →ₗ[ℝ] W := LinearMap.codRestrict W g hg
  have hproj : ∀ d, ell lab d = 0 → ((proj d : W) : E0 V → ℝ) = d := by
    intro d hd
    simp [proj, g, hd]
  have hFx : ∀ y : W, F ((eqv.symm y : W) : E0 V → ℝ) = (y : E0 V → ℝ) := by
    intro y
    have := congrArg Subtype.val (eqv.apply_symm_apply y)
    exact this
  refine ⟨⟨Phi0 lab ∘ₗ W.subtype ∘ₗ eqv.symm.toLinearMap ∘ₗ proj, fun d hd => ?_,
    fun d hd T => ?_⟩⟩
  · show F ((eqv.symm (proj d) : W) : E0 V → ℝ) = d
    rw [hFx, hproj d hd]
  · set x : E0 V → ℝ := ((eqv.symm (proj d) : W) : E0 V → ℝ)
    have hxW : x ∈ W := (eqv.symm (proj d)).2
    have hFd : F x = d := by simp only [x]; rw [hFx, hproj d hd]
    have hxn : ‖x‖ ≤ 2 * ‖d‖ := by rw [← hFd]; exact hcontr x hxW
    have hb := abs_Phi0_le_R hR hm h512 hmR hbal x (LinearMap.mem_ker.mp hxW) T
    show |Phi0 lab x T| ≤ 400 * R ^ 5 / Fintype.card V * ‖d‖
    calc |Phi0 lab x T| ≤ 200 * R ^ 5 / Fintype.card V * ‖x‖ := hb
      _ ≤ 200 * R ^ 5 / Fintype.card V * (2 * ‖d‖) :=
          mul_le_mul_of_nonneg_left hxn (by positivity)
      _ = 400 * R ^ 5 / Fintype.card V * ‖d‖ := by ring

end Ratio

end CDRBicolour.Absorption
