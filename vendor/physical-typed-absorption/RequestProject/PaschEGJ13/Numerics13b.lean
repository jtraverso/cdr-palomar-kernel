/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.Assembly13
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Further numerical lemmas for Step 3 of Theorem 1.3 -/

@[expose] public section

namespace Pseudorandom

open Finset

theorem expo_alg {u K E p z c t : ℝ} (hu : 0 < u) (hK : 1 ≤ K) (hE : 1 ≤ E) (hp : 0 < p)
    (hz : 1 ≤ z) (hpE : E ^ 2 * z ^ 4 ≤ p) (hc0 : 0 < c) (hc : c ≤ 4 * K * u * E / p)
    (ht : t = u / (2 * z)) (hK2 : 144 * K ^ 2 * z ≤ 64 * z ^ 2) :
    z / 64 ≤ t ^ 2 / (2 * (p * c ^ 2 + c * t)) := by
  have hz0 : 0 < z := by linarith
  have hz4 : 0 < z ^ 4 := by positivity
  have ht0 : 0 < t := by rw [ht]; positivity
  have hEp : E * z ^ 4 ≤ p := by nlinarith
  have hE2 : E ^ 2 / p ≤ 1 / z ^ 4 := by
    rw [div_le_div_iff₀ hp hz4]; linarith
  have hE1 : E / p ≤ 1 / z ^ 4 := by
    rw [div_le_div_iff₀ hp hz4]; linarith
  have h1 : p * c ^ 2 ≤ 16 * K ^ 2 * u ^ 2 / z ^ 4 := by
    have : c ^ 2 ≤ (4 * K * u * E / p) ^ 2 := pow_le_pow_left₀ hc0.le hc 2
    calc p * c ^ 2 ≤ p * (4 * K * u * E / p) ^ 2 := by gcongr
      _ = 16 * K ^ 2 * u ^ 2 * (E ^ 2 / p) := by field_simp; ring
      _ ≤ 16 * K ^ 2 * u ^ 2 * (1 / z ^ 4) := by gcongr
      _ = _ := by ring
  have h2 : c * t ≤ 2 * K ^ 2 * u ^ 2 / z ^ 4 := by
    have hzi : 1 / z ≤ 1 := by rw [div_le_one hz0]; exact hz
    have hKK : K ≤ K ^ 2 := by nlinarith
    calc c * t ≤ (4 * K * u * E / p) * t := by gcongr
      _ = 2 * K * u ^ 2 * (E / p) * (1 / z) := by rw [ht]; field_simp; ring
      _ ≤ 2 * K ^ 2 * u ^ 2 * (1 / z ^ 4) * 1 := by gcongr
      _ = _ := by ring
  have hden : 0 < 2 * (p * c ^ 2 + c * t) := by positivity
  rw [le_div_iff₀ hden]
  have h3 : 2 * (p * c ^ 2 + c * t) ≤ 36 * K ^ 2 * u ^ 2 / z ^ 4 := by
    have : 36 * K ^ 2 * u ^ 2 / z ^ 4 =
        2 * (16 * K ^ 2 * u ^ 2 / z ^ 4 + 2 * K ^ 2 * u ^ 2 / z ^ 4) := by ring
    rw [this]; linarith
  have h4 : z / 64 * (36 * K ^ 2 * u ^ 2 / z ^ 4) ≤ t ^ 2 := by
    rw [ht, div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < u ^ 2 * z ^ 5 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hK2 (le_of_lt this)]
  calc z / 64 * (2 * (p * c ^ 2 + c * t)) ≤ z / 64 * (36 * K ^ 2 * u ^ 2 / z ^ 4) := by gcongr
    _ ≤ _ := h4

/-- The influence constant `c = ℓ p^{ℓ-1} B` in closed form. -/
theorem c13_eq {p q P tw : ℝ} (ℓ r : ℕ) (hℓ : 1 ≤ ℓ) (hp : 0 < p) (hq : 0 < q)
    (hpr : p ^ r = p * P) (hP : 0 < P) :
    ℓ * p ^ (ℓ - 1) * (2 * (ℓ : ℝ) ^ ℓ * (2 * ((ℓ : ℝ) ^ ℓ * (1 / p) ^ (r * ℓ)) * tw *
      (1 / q) ^ ℓ)) = 4 * (ℓ : ℝ) ^ (2 * ℓ + 1) * tw / (p * (q * P) ^ ℓ) := by
  have h1 : p ^ (r * ℓ) = p ^ ℓ * P ^ ℓ := by rw [pow_mul, hpr, mul_pow]
  have h2 : p ^ ℓ = p * p ^ (ℓ - 1) := by rw [← pow_succ']; congr 1; omega
  rw [one_div_pow, one_div_pow, h1, mul_pow, h2]
  field_simp
  ring

theorem c13_le {p q P Δ a tw : ℝ} (ℓ : ℕ) (hp : 0 < p) (hq : 0 < q) (hP : 0 < P)
    (hQ : Δ ^ (1 - a) ≤ q * P) (hΔ : 0 < Δ) (htw : 0 ≤ tw) (K : ℝ) (hK : 0 ≤ K) :
    4 * K * tw / (p * (q * P) ^ ℓ) ≤ 4 * K * (tw / Δ ^ ℓ) * (Δ ^ a) ^ ℓ / p := by
  have hD : Δ ^ ℓ = (Δ ^ (1 - a)) ^ ℓ * (Δ ^ a) ^ ℓ := by
    rw [← mul_pow, ← Real.rpow_add hΔ]; simp
  have h0 : 0 < Δ ^ (1 - a) := Real.rpow_pos_of_pos hΔ _
  have hDa : 0 < Δ ^ a := Real.rpow_pos_of_pos hΔ _
  have h3 : (Δ ^ (1 - a)) ^ ℓ ≤ (q * P) ^ ℓ := pow_le_pow_left₀ h0.le hQ ℓ
  have h4 : tw / (q * P) ^ ℓ ≤ (tw / Δ ^ ℓ) * (Δ ^ a) ^ ℓ := by
    calc tw / (q * P) ^ ℓ ≤ tw / (Δ ^ (1 - a)) ^ ℓ :=
          div_le_div_of_nonneg_left htw (by positivity) h3
      _ = _ := by rw [hD]; field_simp
  calc 4 * K * tw / (p * (q * P) ^ ℓ) = 4 * K * (tw / (q * P) ^ ℓ) / p := by field_simp
    _ ≤ 4 * K * ((tw / Δ ^ ℓ) * (Δ ^ a) ^ ℓ) / p := by gcongr
    _ = _ := by ring

/-- The exponent of the Step 3 concentration bound is at least `Δ^ε/64`. -/
theorem step3_expo {Δ ε a b p c t u : ℝ} (ℓ L : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ L) (hΔ : 1 ≤ Δ)
    (hε : 0 < ε) (ha : 0 ≤ a) (hb : b = 2 * L * a + 4 * ε) (hp : Δ ^ b ≤ p) (hu : 0 < u)
    (hc0 : 0 < c) (hc : c ≤ 4 * (ℓ : ℝ) ^ (2 * ℓ + 1) * u * (Δ ^ a) ^ ℓ / p)
    (ht : t = Δ ^ (-ε) * u / 2)
    (h17 : 144 * (L : ℝ) ^ (4 * L + 2) * Δ ^ ε ≤ 64 * Δ ^ (2 * ε)) :
    Δ ^ ε / 64 ≤ t ^ 2 / (2 * (p * c ^ 2 + c * t)) := by
  have hΔ0 : 0 < Δ := by linarith
  have hz : 1 ≤ Δ ^ ε := Real.one_le_rpow hΔ hε.le
  have hDa : 1 ≤ Δ ^ a := Real.one_le_rpow hΔ ha
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  have hp0 : 0 < p := lt_of_lt_of_le (Real.rpow_pos_of_pos hΔ0 _) hp
  refine expo_alg hu (one_le_pow₀ hℓR) (one_le_pow₀ hDa) hp0 hz ?_ hc0 hc ?_ ?_
  · have e : Δ ^ b = (Δ ^ a) ^ (L * 2) * (Δ ^ ε) ^ 4 := by
      rw [hb, Real.rpow_add hΔ0, ← Real.rpow_natCast, ← Real.rpow_natCast (Δ ^ ε),
        ← Real.rpow_mul hΔ0.le, ← Real.rpow_mul hΔ0.le]
      congr 1 <;> congr 1 <;> push_cast <;> ring
    rw [← pow_mul]
    refine le_trans ?_ (e ▸ hp)
    gcongr
    all_goals exact hDa
  · rw [ht, Real.rpow_neg hΔ0.le]; field_simp
  · have e : (Δ ^ ε) ^ 2 = Δ ^ (2 * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hΔ0.le]; push_cast; ring_nf
    rw [e, ← pow_mul]
    have : (ℓ : ℝ) ^ ((2 * ℓ + 1) * 2) ≤ (L : ℝ) ^ (4 * L + 2) := by
      calc (ℓ : ℝ) ^ ((2 * ℓ + 1) * 2) ≤ (L : ℝ) ^ ((2 * ℓ + 1) * 2) := by gcongr
        _ ≤ (L : ℝ) ^ (4 * L + 2) :=
            pow_le_pow_right₀ (by exact_mod_cast (hℓ1.trans hℓL)) (by omega)
    nlinarith [Real.rpow_pos_of_pos hΔ0 ε]

theorem sum_range_pow_le {X : ℝ} (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hX : 1 ≤ X) :
    ∑ k ∈ range ℓ, X ^ k * (k : ℝ) ^ ℓ ≤ (ℓ : ℝ) ^ (ℓ + 1) * X ^ (ℓ - 1) := by
  calc ∑ k ∈ range ℓ, X ^ k * (k : ℝ) ^ ℓ ≤ ∑ _k ∈ range ℓ, X ^ (ℓ - 1) * (ℓ : ℝ) ^ ℓ := by
        refine sum_le_sum fun k hk => ?_
        have hk' := mem_range.mp hk
        gcongr
        all_goals first | exact hX | omega
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul, pow_succ]; ring

/-- The error term of Step 3 is at most `e · ω(H)/Δ^ℓ / 4`. -/
theorem err13 {Δ a b e p q P x tw Err : ℝ} (ℓ L r : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ L) (hΔ : 1 ≤ Δ)
    (hp : Δ ^ b ≤ p) (hq : 0 < q) (hP : 0 < P) (hpr : p ^ r = p * P) (hQ : Δ ^ (1 - a) ≤ q * P)
    (hx0 : 0 ≤ x) (hx : x ≤ q * P / Δ) (hX : 1 ≤ x * p) (htw : 0 ≤ tw)
    (hErr : Err ≤ (2 * (ℓ : ℝ) ^ ℓ * (2 * ((ℓ : ℝ) ^ ℓ * (1 / p) ^ (r * ℓ)) * tw * (1 / q) ^ ℓ)) *
      ∑ k ∈ range ℓ, (x / q) ^ k * ((p * q) ^ k * (k : ℝ) ^ ℓ))
    (h18 : 64 * (L : ℝ) ^ (3 * L + 1) * Δ ^ (a - b) ≤ e) :
    Err ≤ e * (tw / Δ ^ ℓ) / 4 := by
  have hΔ0 : 0 < Δ := by linarith
  have hp0 : 0 < p := lt_of_lt_of_le (Real.rpow_pos_of_pos hΔ0 _) hp
  have hQ0 : 0 < q * P := by positivity
  have hs : ∑ k ∈ range ℓ, (x / q) ^ k * ((p * q) ^ k * (k : ℝ) ^ ℓ) ≤
      (ℓ : ℝ) ^ (ℓ + 1) * (x * p) ^ (ℓ - 1) := by
    refine le_trans (le_of_eq ?_) (sum_range_pow_le ℓ hℓ1 hX)
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, ← mul_pow]; congr 2; field_simp
  have hB : 2 * (ℓ : ℝ) ^ ℓ * (2 * ((ℓ : ℝ) ^ ℓ * (1 / p) ^ (r * ℓ)) * tw * (1 / q) ^ ℓ) =
      4 * (ℓ : ℝ) ^ (2 * ℓ) * tw / (p ^ ℓ * (q * P) ^ ℓ) := by
    have h1 : p ^ (r * ℓ) = p ^ ℓ * P ^ ℓ := by rw [pow_mul, hpr, mul_pow]
    rw [one_div_pow, one_div_pow, h1, mul_pow]
    field_simp
    ring
  have hB0 : 0 ≤ 4 * (ℓ : ℝ) ^ (2 * ℓ) * tw / (p ^ ℓ * (q * P) ^ ℓ) := by positivity
  have hxl : x ^ (ℓ - 1) ≤ (q * P) ^ (ℓ - 1) / Δ ^ (ℓ - 1) := by
    rw [← div_pow]; exact pow_le_pow_left₀ hx0 hx _
  have hpl : p ^ ℓ = p * p ^ (ℓ - 1) := by rw [← pow_succ']; congr 1; omega
  have hQl : (q * P) ^ ℓ = (q * P) * (q * P) ^ (ℓ - 1) := by rw [← pow_succ']; congr 1; omega
  have hDl : Δ ^ ℓ = Δ * Δ ^ (ℓ - 1) := by rw [← pow_succ']; congr 1; omega
  have hDab : Δ / (p * (q * P)) ≤ Δ ^ (a - b) := by
    have e1 : Δ ^ (a - b) = Δ / (Δ ^ b * Δ ^ (1 - a)) := by
      rw [← Real.rpow_add hΔ0, eq_div_iff (by positivity), ← Real.rpow_add hΔ0]
      ring_nf; simp
    rw [e1]
    apply div_le_div_of_nonneg_left hΔ0.le (by positivity)
    exact mul_le_mul hp hQ (by positivity) hp0.le
  have hLl : (ℓ : ℝ) ^ (3 * ℓ + 1) ≤ (L : ℝ) ^ (3 * L + 1) := by
    calc (ℓ : ℝ) ^ (3 * ℓ + 1) ≤ (L : ℝ) ^ (3 * ℓ + 1) := by gcongr
      _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast (hℓ1.trans hℓL)) (by omega)
  have hW : 0 ≤ tw / Δ ^ ℓ := by positivity
  have h18W := mul_le_mul_of_nonneg_right h18 hW
  have hnn : 0 ≤ (L : ℝ) ^ (3 * L + 1) * (tw / Δ ^ ℓ) * Δ ^ (a - b) :=
    mul_nonneg (mul_nonneg (by positivity) hW) (Real.rpow_pos_of_pos hΔ0 _).le
  calc Err ≤ 4 * (ℓ : ℝ) ^ (2 * ℓ) * tw / (p ^ ℓ * (q * P) ^ ℓ) *
        ((ℓ : ℝ) ^ (ℓ + 1) * (x * p) ^ (ℓ - 1)) := by
        rw [← hB]; exact hErr.trans (mul_le_mul_of_nonneg_left hs (hB ▸ hB0))
    _ = 4 * (ℓ : ℝ) ^ (3 * ℓ + 1) * tw * x ^ (ℓ - 1) / (p * (q * P) ^ ℓ) := by
        rw [mul_pow, hpl]; field_simp; ring
    _ ≤ 4 * (ℓ : ℝ) ^ (3 * ℓ + 1) * tw * ((q * P) ^ (ℓ - 1) / Δ ^ (ℓ - 1)) /
        (p * (q * P) ^ ℓ) := by gcongr
    _ = 4 * (ℓ : ℝ) ^ (3 * ℓ + 1) * (tw / Δ ^ ℓ) * (Δ / (p * (q * P))) := by
        rw [hQl, hDl]; field_simp
    _ ≤ 4 * (L : ℝ) ^ (3 * L + 1) * (tw / Δ ^ ℓ) * Δ ^ (a - b) := by gcongr
    _ ≤ e * (tw / Δ ^ ℓ) / 4 := by nlinarith

/-- The main term identity of Step 3. -/
theorem main13 {p q P Δ ξ ν Dt tw d : ℝ} (ℓ r : ℕ) (hp : 0 < p) (hq : 0 < q) (hP : 0 < P)
    (hΔ : 0 < Δ) (hpr : p ^ r = p * P) (hqDt : q * Dt = (1 + 2 * ξ) * Δ / P)
    (hξ : 0 ≤ ξ) :
    ((1 - ν) / Dt / q) ^ ℓ * (tw * (d * (1 / p) ^ (r * ℓ))) =
      ((1 - ν) / (1 + 2 * ξ)) ^ ℓ * (d / p ^ ℓ) * (tw / Δ ^ ℓ) := by
  have h1 : p ^ (r * ℓ) = p ^ ℓ * P ^ ℓ := by rw [pow_mul, hpr, mul_pow]
  have h2 : (1 - ν) / Dt / q = (1 - ν) * P / ((1 + 2 * ξ) * Δ) := by
    rw [div_div, mul_comm Dt q, hqDt]; field_simp
  rw [h2, one_div_pow, h1, div_pow, div_pow, mul_pow, mul_pow]
  field_simp

/-- `x p ≥ 1` in Step 3. -/
theorem xp13 {x p Q Δ a b ν ξ : ℝ} (hΔ : 0 < Δ) (hν : ν ≤ 1 / 2) (hξ0 : 0 ≤ ξ) (hξ : ξ ≤ 1 / 2)
    (hQ0 : 0 < Q) (hx : x = (1 - ν) / ((1 + 2 * ξ) * (Δ / Q))) (hQ : Δ ^ (1 - a) ≤ Q)
    (hp : Δ ^ b ≤ p) (h19 : 4 * Δ ^ a ≤ Δ ^ b) : 1 ≤ x * p := by
  have hD : Δ ^ (1 - a) * Δ ^ a = Δ := by rw [← Real.rpow_add hΔ]; simp
  have h0 : 0 < Δ ^ (1 - a) := Real.rpow_pos_of_pos hΔ _
  have hDa : 0 < Δ ^ a := Real.rpow_pos_of_pos hΔ _
  rw [hx, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have e : (1 + 2 * ξ) * (Δ / Q) = (1 + 2 * ξ) * Δ / Q := by ring
  rw [e, ← hD]
  have h3 : (1 + 2 * ξ) * (Δ ^ (1 - a) * Δ ^ a) / Q ≤ 2 * Δ ^ a := by
    rw [div_le_iff₀ hQ0]
    have : (1 + 2 * ξ) ≤ 2 := by linarith
    have : (1 + 2 * ξ) * (Δ ^ (1 - a) * Δ ^ a) ≤ 2 * (Q * Δ ^ a) := by
      have := mul_le_mul_of_nonneg_right hQ hDa.le
      nlinarith
    linarith
  have h4 : 2 * Δ ^ a ≤ (1 - ν) * p := by nlinarith
  linarith

/-- One term of the failure probability of Step 2. -/
theorem pib2_term {p q Δ tw Dd s gg Y₀ : ℝ} (ℓ L : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ L) (hp1 : 1 ≤ p)
    (hq1 : 1 ≤ q) (hpD : p ≤ 2 * Δ) (hqD : q ≤ 2 * Δ) (htw : 0 < tw) (hDd : 0 < Dd)
    (hs : 12 * (ℓ : ℝ) ^ 2 * Dd * Y₀ ≤ s) (hgg : 24 * (ℓ : ℝ) ^ 2 * Y₀ ≤ gg) :
    (p * q) ^ ℓ * ((ℓ : ℝ) ^ ℓ * (2 ^ ℓ * Real.exp (-(2 * s * tw * (1 / q) ^ ℓ /
      (24 * (ℓ : ℝ) ^ 2 * (tw * Dd / q ^ ℓ)))) + Real.exp (-(gg / (24 * (ℓ : ℝ) ^ 2))))) ≤
      (4 * Δ ^ 2) ^ L * ((L : ℝ) ^ L * (2 ^ L + 1)) * Real.exp (-Y₀) := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
  have hℓR1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  have hℓ : (ℓ : ℝ) ≤ L := by exact_mod_cast hℓL
  have hq0 : 0 < q := by linarith
  have e1 : Real.exp (-(2 * s * tw * (1 / q) ^ ℓ / (24 * (ℓ : ℝ) ^ 2 * (tw * Dd / q ^ ℓ)))) ≤
      Real.exp (-Y₀) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    have eq : 2 * s * tw * (1 / q) ^ ℓ / (24 * (ℓ : ℝ) ^ 2 * (tw * Dd / q ^ ℓ)) =
        s / (12 * (ℓ : ℝ) ^ 2 * Dd) := by
      rw [one_div_pow]; field_simp; ring
    rw [eq, le_div_iff₀ (by positivity)]
    linarith
  have e2 : Real.exp (-(gg / (24 * (ℓ : ℝ) ^ 2))) ≤ Real.exp (-Y₀) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hpq : (p * q) ^ ℓ ≤ (4 * Δ ^ 2) ^ L := by
    have h1 : (1 : ℝ) ≤ p * q := one_le_mul_of_one_le_of_one_le hp1 hq1
    have h2 : p * q ≤ 4 * Δ ^ 2 := by
      calc p * q ≤ (2 * Δ) * (2 * Δ) := mul_le_mul hpD hqD (by linarith) (by linarith)
        _ = 4 * Δ ^ 2 := by ring
    calc (p * q) ^ ℓ ≤ (p * q) ^ L := pow_le_pow_right₀ h1 hℓL
      _ ≤ (4 * Δ ^ 2) ^ L := pow_le_pow_left₀ (by linarith) h2 L
  have hll : (ℓ : ℝ) ^ ℓ ≤ (L : ℝ) ^ L :=
    (pow_le_pow_left₀ hℓ0.le hℓ _).trans (pow_le_pow_right₀ (by linarith) hℓL)
  have h2l : (2 : ℝ) ^ ℓ ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hℓL
  have hin : (2 : ℝ) ^ ℓ * Real.exp (-(2 * s * tw * (1 / q) ^ ℓ /
      (24 * (ℓ : ℝ) ^ 2 * (tw * Dd / q ^ ℓ)))) + Real.exp (-(gg / (24 * (ℓ : ℝ) ^ 2))) ≤
      (2 ^ L + 1) * Real.exp (-Y₀) := by
    have := mul_le_mul h2l e1 (by positivity) (by positivity)
    linarith
  calc _ ≤ (4 * Δ ^ 2) ^ L * ((L : ℝ) ^ L * ((2 ^ L + 1) * Real.exp (-Y₀))) := by
        gcongr
    _ = _ := by ring

end Pseudorandom
