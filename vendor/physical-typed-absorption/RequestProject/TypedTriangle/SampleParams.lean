/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.ComponentSample

@[expose] public section

/-!
# G1-Z, §4.3 de la guía V6 — Parámetros del muestreo sin elección circular

Variante geométrica: `η_j = 2^{-j}`, `L_j = ⌈2/(κη_j)⌉`, `Q_j = ⌈9L_j/(κη_jε)⌉ + m₀`, y bloque final
`b_j = L_c (j + t)`, con `L_c` tal que `(1−c/2)^{L_c} ≤ 1/16` y `t` tal que `A·16^{-t} ≤ ε/3`.
Entonces

* `L(1−κη)^Q ≤ ε/9` (por `(1−p)^m ≤ 1/(1+mp)`),
* `LQ + q ≤ A·8^j`, de modo que `(LQ+q)(1−c+η)^b ≤ A·8^j·16^{-j-t} ≤ ε/3`,
* `bη = L_c(j+t)2^{-j} ≤ ε/3` para `j` grande.

Todos los parámetros dependen sólo de `c, κ, ε, q, m₀`, y se fijan antes de cualquier grafo.
-/

open Finset Filter Topology

noncomputable section
open Classical

namespace TypedTriangle

/-- Cota del crecimiento. -/
lemma growth_term_le {p ε : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hε : 0 < ε) {L Q : ℕ}
    (hQ : 9 * L / (p * ε) ≤ Q) : L * (1 - p) ^ Q ≤ ε / 9 := by
  have h1 := one_sub_pow_le_inv hp0.le hp1 Q
  have hpos : 0 < 1 + Q * p := by positivity
  have hL : (0 : ℝ) ≤ L := by positivity
  calc (L : ℝ) * (1 - p) ^ Q ≤ L * (1 / (1 + Q * p)) := mul_le_mul_of_nonneg_left h1 hL
    _ ≤ ε / 9 := by
      rw [mul_one_div, div_le_div_iff₀ hpos (by norm_num)]
      have : 9 * L ≤ Q * (p * ε) := by
        rwa [div_le_iff₀ (by positivity)] at hQ
      nlinarith

/-- Cota del bloque final. -/
lemma final_term_le {ε η : ℝ} {Lc t j : ℕ} (hε : 0 < ε)
    (hj2 : (j : ℝ) * η ≤ ε / (6 * (Lc + 1))) (hj3 : η ≤ ε / (6 * (Lc + 1) * (t + 1))) :
    ((Lc * (j + t) : ℕ) : ℝ) * η ≤ ε / 3 := by
  push_cast
  have hLc0 : (0 : ℝ) ≤ Lc := by positivity
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have e1 : (Lc : ℝ) * (j * η) ≤ Lc * (ε / (6 * (Lc + 1))) :=
    mul_le_mul_of_nonneg_left hj2 hLc0
  have e2 : (Lc : ℝ) * t * η ≤ Lc * t * (ε / (6 * (Lc + 1) * (t + 1))) :=
    mul_le_mul_of_nonneg_left hj3 (by positivity)
  have e3 : (Lc : ℝ) * (ε / (6 * (Lc + 1))) ≤ ε / 6 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have e4 : (Lc : ℝ) * t * (ε / (6 * (Lc + 1) * (t + 1))) ≤ ε / 6 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (Lc : ℝ) * t ≤ (Lc + 1) * (t + 1) := by nlinarith
    nlinarith
  have : (Lc : ℝ) * (j + t) * η = Lc * (j * η) + Lc * t * η := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- **Elección de parámetros del lema muestral.** -/
theorem sample_params {c κ ε : ℝ} (q m0 : ℕ) (hc : 0 < c) (hc1 : c ≤ 1) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hε : 0 < ε) :
    ∃ (L Q b : ℕ) (η : ℝ), 0 < η ∧ η ≤ c / 2 ∧ 1 < L * (κ * η) ∧ m0 ≤ Q ∧
      L * (1 - κ * η) ^ Q + (L * Q + q) * (1 - c + η) ^ b + b * η ≤ ε := by
  set r : ℝ := 1 - c / 2
  have hr0 : 0 ≤ r := by simp only [r]; linarith
  have hr1 : r < 1 := by simp only [r]; linarith
  obtain ⟨Lc, hLc⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / 16 by norm_num) hr1
  set A : ℝ := 3 / κ * (27 / (κ ^ 2 * ε) + 1 + m0) + q
  have hA : 0 < A := by positivity
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / (3 * A) by positivity)
    (show (1 : ℝ) / 16 < 1 by norm_num)
  -- `j` grande
  have ev1 : ∀ᶠ j : ℕ in atTop, ((1 : ℝ) / 2) ^ j ≤ c / 2 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
      (ge_mem_nhds (by positivity))
  have ev2 : ∀ᶠ j : ℕ in atTop, (j : ℝ) * ((1 : ℝ) / 2) ^ j ≤ ε / (6 * (Lc + 1)) :=
    (tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)).eventually
      (ge_mem_nhds (by positivity))
  have ev3 : ∀ᶠ j : ℕ in atTop, ((1 : ℝ) / 2) ^ j ≤ ε / (6 * (Lc + 1) * (t + 1)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
      (ge_mem_nhds (by positivity))
  obtain ⟨j, hj1, hj2, hj3⟩ := (ev1.and (ev2.and ev3)).exists
  set η : ℝ := ((1 : ℝ) / 2) ^ j
  set u : ℝ := (2 : ℝ) ^ j
  have hηu : η * u = 1 := by simp only [η, u]; rw [← mul_pow]; norm_num
  have hη0 : 0 < η := by positivity
  have hu1 : 1 ≤ u := one_le_pow₀ (by norm_num)
  have hη1 : η ≤ 1 := by nlinarith
  have hκη : 0 < κ * η := by positivity
  have hκη1 : κ * η ≤ 1 := by nlinarith
  set L : ℕ := ⌈2 / (κ * η)⌉₊
  set Q : ℕ := ⌈9 * L / (κ * η * ε)⌉₊ + m0
  set b : ℕ := Lc * (j + t)
  refine ⟨L, Q, b, η, hη0, hj1, ?_, by simp [Q], ?_⟩
  · have := Nat.le_ceil (2 / (κ * η))
    rw [div_le_iff₀ hκη] at this
    linarith
  -- cotas de `L` y `Q` en términos de `u = 2^j`
  have h1κη : 1 / (κ * η) = u / κ := by
    field_simp
    nlinarith
  have hL2 : (L : ℝ) ≤ 3 * u / κ := by
    have h := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 / (κ * η) by positivity)).le
    have : 2 / (κ * η) = 2 * (u / κ) := by rw [← h1κη]; ring
    have hu' : 1 ≤ u / κ := by rw [le_div_iff₀ hκ]; linarith
    have e3 : 3 * u / κ = 3 * (u / κ) := by ring
    linarith
  have hQe : (Q : ℝ) = (⌈9 * L / (κ * η * ε)⌉₊ : ℝ) + m0 := by simp only [Q]; push_cast; rfl
  have hQ1 : 9 * L / (κ * η * ε) ≤ Q := by
    have := Nat.le_ceil (9 * L / (κ * η * ε))
    rw [hQe]; linarith [(by positivity : (0 : ℝ) ≤ m0)]
  have hQ2 : (Q : ℝ) ≤ (27 / (κ ^ 2 * ε) + 1 + m0) * u ^ 2 := by
    have h := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 9 * L / (κ * η * ε) by positivity)).le
    have e : 9 * (L : ℝ) / (κ * η * ε) ≤ 27 / (κ ^ 2 * ε) * u ^ 2 := by
      have : 9 * (L : ℝ) / (κ * η * ε) = 9 * L * (u / κ) / ε := by
        rw [← h1κη]; field_simp
      rw [this]
      calc 9 * (L : ℝ) * (u / κ) / ε ≤ 9 * (3 * u / κ) * (u / κ) / ε := by gcongr
        _ = 27 / (κ ^ 2 * ε) * u ^ 2 := by field_simp; ring
    have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
    rw [hQe]
    nlinarith [(by positivity : (0 : ℝ) ≤ m0)]
  -- primer término
  have hT1 := growth_term_le hκη hκη1 hε hQ1
  -- segundo término
  have hLQq : (L : ℝ) * Q + q ≤ A * u ^ 3 := by
    have hq : (q : ℝ) ≤ q * u ^ 3 := by
      have : 1 ≤ u ^ 3 := one_le_pow₀ hu1
      nlinarith [(by positivity : (0 : ℝ) ≤ q)]
    have hLQ : (L : ℝ) * Q ≤ 3 / κ * (27 / (κ ^ 2 * ε) + 1 + m0) * u ^ 3 := by
      calc (L : ℝ) * Q ≤ (3 * u / κ) * ((27 / (κ ^ 2 * ε) + 1 + m0) * u ^ 2) := by gcongr
        _ = _ := by ring
    have hAe : A = 3 / κ * (27 / (κ ^ 2 * ε) + 1 + m0) + q := rfl
    calc (L : ℝ) * Q + q ≤ 3 / κ * (27 / (κ ^ 2 * ε) + 1 + m0) * u ^ 3 + q * u ^ 3 := by linarith
      _ = A * u ^ 3 := by rw [hAe]; ring
  have hbase : 1 - c + η ≤ r := by simp only [r]; linarith
  have hbase0 : 0 ≤ 1 - c + η := by linarith
  have hpowb : (1 - c + η) ^ b ≤ ((1 : ℝ) / 16) ^ (j + t) := by
    calc (1 - c + η) ^ b ≤ r ^ b := pow_le_pow_left₀ hbase0 hbase b
      _ = (r ^ Lc) ^ (j + t) := by rw [← pow_mul]
      _ ≤ ((1 : ℝ) / 16) ^ (j + t) := pow_le_pow_left₀ (pow_nonneg hr0 _) hLc.le _
  have hT2 : ((L : ℝ) * Q + q) * (1 - c + η) ^ b ≤ ε / 3 := by
    have hu3 : u ^ 3 * ((1 : ℝ) / 16) ^ j = η := by
      simp only [u, η]; rw [← pow_mul, mul_comm j 3, pow_mul, ← mul_pow]; norm_num
    calc ((L : ℝ) * Q + q) * (1 - c + η) ^ b ≤ (A * u ^ 3) * ((1 : ℝ) / 16) ^ (j + t) := by
          gcongr
      _ = A * η * ((1 : ℝ) / 16) ^ t := by rw [pow_add, ← hu3]; ring
      _ ≤ A * 1 * (ε / (3 * A)) := by gcongr
      _ = ε / 3 := by field_simp
  -- tercer término
  have hT3 : (b : ℝ) * η ≤ ε / 3 := final_term_le hε hj2 hj3
  linarith

universe u

open Sampler in
/-- **Lema muestral de una componente, con parámetros uniformes.** Para `c, κ ∈ (0,1]`,
`ε > 0`, un número `q` de marcados y un mínimo `m₀` de valores por bloque, hay `L, Q, b`
(dependientes sólo de esos datos) tales que, para todo grafo `J` y toda componente `K` no vacía,
cerrada, de grado mínimo `≥ cN` y con expansión `ExpandOn J K c κ`, y todos marcados `M p`
(`≤ q`, función del prefijo), el suceso bueno falla en a lo sumo una fracción `ε` de las
muestras. -/
theorem component_sample {c κ ε : ℝ} (q m0 : ℕ) (hc : 0 < c) (hc1 : c ≤ 1) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hε : 0 < ε) :
    ∃ L Q b : ℕ, 1 ≤ L ∧ m0 ≤ Q ∧ ∀ {Ω : Type u} [Fintype Ω] (J : SimpleGraph Ω) (K : Finset Ω),
      K.Nonempty → NbrClosed J K → MinDegOn J K c → ExpandOn J K c κ →
      ∀ M : (Fin L → Fin Q → Ω) → Finset Ω, (∀ p, (M p).card ≤ q) →
      ((univ.filter (fun x : (Fin L → Fin Q → Ω) × (Fin b → Ω) =>
        ¬ SampleGood J K (M x.1) (pvals x.1) (pvals x.1 ∪ fvals x.2))).card : ℝ) ≤
        ε * Fintype.card ((Fin L → Fin Q → Ω) × (Fin b → Ω)) := by
  obtain ⟨L, Q, b, η, hη0, hηc, hL, hQ, hsum⟩ := sample_params q m0 hc hc1 hκ hκ1 hε
  have hη1 : η ≤ 1 := by linarith
  have hκη : κ * η ≤ c / 2 := by nlinarith
  have hL1 : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · simp [h0] at hL; linarith
    · exact h0
  refine ⟨L, Q, b, hL1, hQ, fun J K hne hK hdeg hexp M hMq => ?_⟩
  refine (card_not_sampleGood_le hK hdeg hexp hne hη0 hη1 (by linarith) (by nlinarith) hL M
    hMq).trans ?_
  exact mul_le_mul_of_nonneg_right hsum (by positivity)

end TypedTriangle
