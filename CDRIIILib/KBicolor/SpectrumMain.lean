/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.KBicolor.SpectrumExact
public import Mathlib.NumberTheory.Bertrand

/-!
# Theorem S: the exact type spectrum of `k`-bicolourings, in the interior

`kbicolour_types_exact`: fix `k ≥ 3`, `0 < δ ≤ 1` and `ε > 0`. For every large admissible
labelling with classes of size `≥ δ n` and every integer type-count target `t` satisfying the
linear identities `2 (t_XY + t_YX) = c_X c_Y`, `2 Σ_{Y ≠ X} t_XY = c_X (c_X − 1)` with all
`t_XY ≥ ε n²`, there is a `k`-bicoloured Steiner triple system (an allowed decomposition of the
complete host) with **exactly** `t_XY` blocks of type `XXY` for all `X ≠ Y`.

Proof: copies of the trade on the triples `(o, Y, Z)` (a prime `m ≈ λ n`, `exists_place`); a
residual seed of `K_n − L` with exact masses `t − B + m²/2` on the cycle coordinates
(`residual_seed_exact`); Theorem T with monitors on `K_n − L` (H2–H4 residual); the right number
of copies in `T₁` (`exact_from_packing`).
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor

open Finset TypedTriangle CDRBicolour.Absorption CDRBicolour.Absorption.Exact
  CDRBicolour.Absorption.Refined

variable {k : ℕ}

/-! ### Shifting a target along circulations -/

/-- A target shifted by `Σ_j s_j · circ_j`. -/
def tsh (o : Fin k) (t₀ : Fin k → Fin k → ℝ) (s : Coord o → ℝ) (A B : Fin k) : ℝ :=
  t₀ A B + ∑ j : Coord o, s j * circ o j.1.1 j.1.2 A B

theorem tsh_pair (o : Fin k) (t₀ : Fin k → Fin k → ℝ) (s : Coord o → ℝ) (A B : Fin k) :
    tsh o t₀ s A B + tsh o t₀ s B A = t₀ A B + t₀ B A := by
  unfold tsh
  have : ∑ j : Coord o, s j * circ o j.1.1 j.1.2 A B +
      ∑ j : Coord o, s j * circ o j.1.1 j.1.2 B A = 0 := by
    rw [← sum_add_distrib]
    exact sum_eq_zero fun j _ => by rw [← mul_add, circ_antisymm, mul_zero]
  linarith

theorem tsh_row (o : Fin k) (t₀ : Fin k → Fin k → ℝ) (s : Coord o → ℝ) (A : Fin k) :
    ∑ B ∈ univ.filter (fun B => B ≠ A), tsh o t₀ s A B =
      ∑ B ∈ univ.filter (fun B => B ≠ A), t₀ A B := by
  unfold tsh
  rw [sum_add_distrib, sum_comm]
  have : ∑ j : Coord o, ∑ B ∈ univ.filter (fun B => B ≠ A),
      s j * circ o j.1.1 j.1.2 A B = 0 := by
    refine sum_eq_zero fun j _ => ?_
    rw [← mul_sum, circ_row_zero j.2.2.1 j.2.2.2 (ne_of_lt j.2.1), mul_zero]
  rw [this, add_zero]

theorem tsh_coord (o : Fin k) (t₀ : Fin k → Fin k → ℝ) (s : Coord o → ℝ) (i : Coord o) :
    tsh o t₀ s i.1.1 i.1.2 = t₀ i.1.1 i.1.2 + s i := by
  unfold tsh
  simp_rw [circ_coord i, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq]
  simp

theorem tsh_low (o : Fin k) (t₀ : Fin k → Fin k → ℝ) (s : Coord o → ℝ) {S : ℝ}
    (hs : ∀ j, |s j| ≤ S) (A B : Fin k) :
    t₀ A B - 3 * Fintype.card (Coord o) * S ≤ tsh o t₀ s A B := by
  unfold tsh
  have h : ∀ j : Coord o, -(3 * S) ≤ s j * circ o j.1.1 j.1.2 A B := by
    intro j
    have hc := abs_circ_le o j.1.1 j.1.2 A B
    have h1 : |s j * circ o j.1.1 j.1.2 A B| ≤ S * 3 := by
      rw [abs_mul]
      exact mul_le_mul (hs j) hc (abs_nonneg _) ((abs_nonneg _).trans (hs j))
    rw [abs_le] at h1
    linarith
  have : -(3 * Fintype.card (Coord o) * S) ≤ ∑ j : Coord o, s j * circ o j.1.1 j.1.2 A B := by
    calc -(3 * Fintype.card (Coord o) * S) = ∑ _j : Coord o, -(3 * S) := by
          rw [sum_const, card_univ, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum fun j _ => h j
  linarith

set_option maxRecDepth 100000 in
theorem card_T0m : T0m.card = 9 := by decide +kernel

theorem Bn_le {n m : ℕ} [NeZero m] (lab : Fin n → Fin k) (o : Fin k) (P : Place lab (Coord o) m)
    (hPτ : P.τ = tau3 o) (i : Coord o) : Bn lab o P i ≤ 9 * m ^ 2 := by
  unfold Bn
  rw [hPτ, Fintype.sum_prod_type]
  have h : ∀ j : Coord o, ∑ q : ZMod m × ZMod m, mcnt (tau3 o j) T0m i.1.1 i.1.2 ≤
      if j = i then 9 * m ^ 2 else 0 := by
    intro j
    by_cases hj : j = i
    · rw [if_pos hj]
      calc ∑ q : ZMod m × ZMod m, mcnt (tau3 o j) T0m i.1.1 i.1.2
          ≤ ∑ _q : ZMod m × ZMod m, 9 := sum_le_sum fun q _ => by
            unfold mcnt; exact (card_filter_le _ _).trans card_T0m.le
        _ = 9 * m ^ 2 := by
            rw [sum_const, card_univ, Fintype.card_prod, ZMod.card, smul_eq_mul]; ring
    · rw [if_neg hj]
      simp [mcnt_tau3_zero o hj]
  calc ∑ j : Coord o, ∑ q : ZMod m × ZMod m, mcnt (tau3 o j) T0m i.1.1 i.1.2
      ≤ ∑ j : Coord o, (if j = i then 9 * m ^ 2 else 0) := sum_le_sum fun j _ => h j
    _ = 9 * m ^ 2 := by rw [sum_ite_eq']; simp

/-! ### Clean-context arithmetic -/

theorem ar_place {Jc lam n mp δ c : ℝ} (hJ : 0 ≤ Jc) (hl : 0 ≤ lam) (hn : 0 ≤ n)
    (hmp : mp ≤ 2 * lam * n) (h18 : 18 * (Jc + 1) * lam ≤ δ) (hc : δ * n ≤ c) :
    9 * Jc * mp ≤ c := by
  have h1 := mul_le_mul_of_nonneg_left hmp (by positivity : (0 : ℝ) ≤ 9 * Jc)
  have h2 : 18 * Jc * lam * n ≤ 18 * (Jc + 1) * lam * n := by
    have := mul_nonneg hl hn; nlinarith
  have h3 := mul_le_mul_of_nonneg_right h18 hn
  nlinarith

theorem ar_bal {δ n mB : ℝ} (hδ : 0 < δ) (h1 : δ * n - 1 < mB) (h2 : 2 ≤ δ * n) :
    n ≤ 2 / δ * mB := by
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  linarith

theorem ar_s {mp lam n B : ℝ} (hB0 : 0 ≤ B) (hB9 : B ≤ 9 * mp ^ 2) (hmp0 : 0 ≤ mp)
    (hmp : mp ≤ 2 * lam * n) : |mp ^ 2 / 2 - B| ≤ 38 * lam ^ 2 * n ^ 2 := by
  have h2 : mp ^ 2 ≤ (2 * lam * n) ^ 2 := pow_le_pow_left₀ hmp0 hmp 2
  have h3 : (2 * lam * n) ^ 2 = 4 * lam ^ 2 * n ^ 2 := by ring
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg mp]

theorem ar_seed {Kc C₀ Δ lam n : ℝ} (hKc : 0 ≤ Kc) (hn : 0 ≤ n) (hΔ : Δ ≤ 18 * lam * n)
    (hL1 : 144 * Kc * C₀ ^ 2 * lam ≤ 1) : 8 * Kc * C₀ ^ 2 * Δ ≤ n := by
  have h1 := mul_le_mul_of_nonneg_left hΔ (by positivity : (0 : ℝ) ≤ 8 * Kc * C₀ ^ 2)
  have h2 := mul_le_mul_of_nonneg_right hL1 hn
  nlinarith

theorem ar_rho {Kc C₀ Δ lam n : ℝ} (hKc : 0 ≤ Kc) (hC : 0 ≤ C₀) (hn : 0 ≤ n)
    (hΔ : Δ ≤ 18 * lam * n) :
    (4 * Kc + 1) * C₀ * Δ * n < (4 * Kc + 1) * C₀ * (18 * lam * n) * n + 1 := by
  have h1 := mul_le_mul_of_nonneg_left hΔ (by positivity : (0 : ℝ) ≤ (4 * Kc + 1) * C₀)
  have h2 := mul_le_mul_of_nonneg_right h1 hn
  linarith

theorem ar_low {ε Jc lam n Kc C₀ cc t t₀ : ℝ} (hε : 0 < ε) (hJ : 0 ≤ Jc) (hl : 0 ≤ lam)
    (hl1 : lam ≤ 1) (hKc : 0 ≤ Kc) (hC : 0 ≤ C₀) (hn1 : 1 ≤ n) (hcc0 : 0 ≤ cc)
    (hcc : cc ≤ n ^ 2) (ht : ε * n ^ 2 ≤ t) (ht₀ : t - 3 * Jc * (38 * lam ^ 2 * n ^ 2) ≤ t₀)
    (L2 : 480 * (Jc + 1) * lam ≤ ε) (L3 : 216 * (Jc + 1) * (4 * Kc + 1) * C₀ * lam ≤ ε)
    (hεn : 12 * (Jc + 1) ≤ ε * n) :
    ε / 2 * cc + 6 * Jc * ((4 * Kc + 1) * C₀ * (18 * lam * n) * n + 1) ≤ 2 * t₀ := by
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hn2 : (0 : ℝ) ≤ n ^ 2 := sq_nonneg n
  have a1 : ε / 2 * cc ≤ ε / 2 * n ^ 2 := mul_le_mul_of_nonneg_left hcc (by positivity)
  have b1 : 108 * Jc * (4 * Kc + 1) * C₀ * lam ≤ ε / 2 := by
    have : 108 * Jc * (4 * Kc + 1) * C₀ * lam ≤ 108 * (Jc + 1) * (4 * Kc + 1) * C₀ * lam := by
      have : 0 ≤ (4 * Kc + 1) * C₀ * lam := by positivity
      nlinarith
    linarith
  have b2 : 108 * Jc * (4 * Kc + 1) * C₀ * lam * n ^ 2 ≤ ε / 2 * n ^ 2 :=
    mul_le_mul_of_nonneg_right b1 hn2
  have b3 : 6 * Jc ≤ ε / 2 * n ^ 2 := by
    have h1 : 6 * (Jc + 1) ≤ ε / 2 * n := by linarith
    have h2 : ε / 2 * n ≤ ε / 2 * n ^ 2 := by
      have : n ≤ n ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have c1 : 114 * Jc * lam ^ 2 ≤ ε / 4 := by
    have h1 : lam ^ 2 ≤ lam := by nlinarith
    have h2 : 114 * Jc * lam ^ 2 ≤ 114 * (Jc + 1) * lam := by
      have := mul_le_mul_of_nonneg_left h1 hJ
      nlinarith
    linarith
  have c2 : 114 * Jc * lam ^ 2 * n ^ 2 ≤ ε / 4 * n ^ 2 := mul_le_mul_of_nonneg_right c1 hn2
  have e : 6 * Jc * ((4 * Kc + 1) * C₀ * (18 * lam * n) * n + 1) =
      108 * Jc * (4 * Kc + 1) * C₀ * lam * n ^ 2 + 6 * Jc := by ring
  have e2 : 3 * Jc * (38 * lam ^ 2 * n ^ 2) = 114 * Jc * lam ^ 2 * n ^ 2 := by ring
  rw [e]
  rw [e2] at ht₀
  linarith

theorem ar_big {k Δ lam n δ c : ℝ} (hk0 : 0 ≤ k) (hl : 0 ≤ lam) (hn : 0 ≤ n)
    (hΔ : Δ ≤ 18 * lam * n) (L6 : 36 * (k + 4) * lam ≤ δ) (hδnk : 2 * (k + 4) < δ * n)
    (hc : δ * n ≤ c) : (k + 4) * (Δ + 1) < c := by
  have h1 : (k + 4) * (Δ + 1) ≤ (k + 4) * (18 * lam * n + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : 36 * (k + 4) * lam * n ≤ δ * n := mul_le_mul_of_nonneg_right L6 hn
  nlinarith

theorem ar_D {Δ lam n δ : ℝ} (hΔ0 : 0 ≤ Δ) (hn : 0 ≤ n) (hΔ : Δ ≤ 18 * lam * n)
    (L5 : 360 * lam ≤ δ) (h20 : 20 ≤ δ * n) :
    10 * (Δ + 1) ≤ δ * n ∧ 4 * (Δ + 1) ≤ δ * n := by
  have h1 : 360 * lam * n ≤ δ * n := mul_le_mul_of_nonneg_right L5 hn
  constructor <;> nlinarith

theorem ar_sq {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : δ ^ 2 / 4 ≤ δ / 2 := by nlinarith

theorem ar_cc {a b n : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (han : a ≤ n) (hbn : b ≤ n) :
    a * b ≤ n ^ 2 := by nlinarith

theorem ar_m4 {lam n mp : ℝ} (hl : 0 ≤ lam) (hn : 0 ≤ n) (hmlo : lam * n / 2 ≤ mp) :
    lam ^ 2 / 32 * n ^ 2 ≤ mp ^ 2 / 4 := by
  have h0 : 0 ≤ lam * n / 2 := by positivity
  have h1 : (lam * n / 2) ^ 2 ≤ mp ^ 2 := pow_le_pow_left₀ h0 hmlo 2
  nlinarith

theorem ar_nu {Jc k n : ℝ} (hJk : Jc ≤ k * k) (hk0 : 0 ≤ k) (hk : k ≤ n) : Jc ≤ n ^ 2 := by
  nlinarith

/-! ### Theorem S -/

theorem le_of_mul_inv {T B lam : ℝ} (hB : 0 < B) (hlam : lam = 1 / B) (hT : T ≤ B) :
    T * lam ≤ 1 := by
  rw [hlam, mul_one_div, div_le_one hB]; exact hT

set_option maxHeartbeats 8000000 in
/-- **Theorem S (exact type spectrum in the interior).** -/
theorem kbicolour_types_exact (k : ℕ) (hk : 3 ≤ k) {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n → Odd n →
      (∀ X, δ * n ≤ ksz lab X) →
      (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X - 1) = n * (n - 1) →
      ∀ t : Fin k → Fin k → ℕ,
      (∀ X Y, X ≠ Y → 2 * (t X Y + t Y X) = ksz lab X * ksz lab Y) →
      (∀ X, 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y = ksz lab X * (ksz lab X - 1)) →
      (∀ X Y, X ≠ Y → ε * (n : ℝ) ^ 2 ≤ t X Y) →
      ∃ D : Finset (Finset (Fin n)), IsDecomposition (kHost lab) (bicF k) (edges (kHost lab)) D ∧
        ∀ X Y, X ≠ Y → kTypeCount lab D X Y = t X Y := by
  classical
  -- constants
  set o : Fin k := ⟨0, by omega⟩ with ho
  set Jc : ℝ := (Fintype.card (Coord o) : ℝ) with hJc
  have hJc0 : 0 ≤ Jc := Nat.cast_nonneg _
  set R : ℝ := 2 / δ with hR
  have hR2 : 2 ≤ R := by rw [hR, le_div_iff₀ hδ]; linarith
  have hR1 : 1 ≤ R := by linarith
  set η : ℝ := ε / 2 with hη
  have hη0 : 0 < η := by positivity
  set C₀ : ℝ := 1 / η + 2 / δ with hC₀
  have hC₀1 : 1 ≤ C₀ := by
    have : 2 ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
    have : 0 < 1 / η := by positivity
    linarith
  set Kc : ℝ := (#(Trip o) : ℝ) * (400 * R ^ 5 * R * (1 + 4 * R ^ 2)) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set B : ℝ := 1 + 144 * Kc * C₀ ^ 2 + 480 * (Jc + 1) / ε + 216 * (Jc + 1) * (4 * Kc + 1) * C₀ / ε +
    18 * (Jc + 1) / δ + 360 / δ + 36 * ((k : ℝ) + 4) / δ with hB
  have tB1 : 0 ≤ 144 * Kc * C₀ ^ 2 := by positivity
  have tB2 : 0 ≤ 480 * (Jc + 1) / ε := by positivity
  have tB3 : 0 ≤ 216 * (Jc + 1) * (4 * Kc + 1) * C₀ / ε := by positivity
  have tB4 : 0 ≤ 18 * (Jc + 1) / δ := by positivity
  have tB5 : 0 ≤ 360 / δ := by positivity
  have tB6 : 0 ≤ 36 * ((k : ℝ) + 4) / δ := by positivity
  have hBpos : 0 < B := by linarith
  set lam : ℝ := 1 / B with hlam
  have hlam0 : 0 < lam := by positivity
  have hlam1 : lam ≤ 1 := by
    have := le_of_mul_inv hBpos hlam (show (1 : ℝ) ≤ B by linarith); linarith
  have L1 : 144 * Kc * C₀ ^ 2 * lam ≤ 1 := le_of_mul_inv hBpos hlam (by linarith)
  have L2 : 480 * (Jc + 1) * lam ≤ ε := by
    have := le_of_mul_inv hBpos hlam (show 480 * (Jc + 1) / ε ≤ B by linarith)
    rw [div_mul_eq_mul_div, div_le_one hε] at this; exact this
  have L3 : 216 * (Jc + 1) * (4 * Kc + 1) * C₀ * lam ≤ ε := by
    have := le_of_mul_inv hBpos hlam
      (show 216 * (Jc + 1) * (4 * Kc + 1) * C₀ / ε ≤ B by linarith)
    rw [div_mul_eq_mul_div, div_le_one hε] at this; exact this
  have L4 : 18 * (Jc + 1) * lam ≤ δ := by
    have := le_of_mul_inv hBpos hlam (show 18 * (Jc + 1) / δ ≤ B by linarith)
    rw [div_mul_eq_mul_div, div_le_one hδ] at this; exact this
  have L5 : 360 * lam ≤ δ := by
    have := le_of_mul_inv hBpos hlam (show 360 / δ ≤ B by linarith)
    rw [div_mul_eq_mul_div, div_le_one hδ] at this; exact this
  have L6 : 36 * ((k : ℝ) + 4) * lam ≤ δ := by
    have := le_of_mul_inv hBpos hlam (show 36 * ((k : ℝ) + 4) / δ ≤ B by linarith)
    rw [div_mul_eq_mul_div, div_le_one hδ] at this; exact this
  set ηT : ℝ := lam ^ 2 / 32 with hηT
  have hηT0 : 0 < ηT := by positivity
  obtain ⟨nT, hT⟩ := Vortex.main_theorem_T_with_triangle_monitors (bicF k) (δ ^ 2 / 4) (2 * C₀)
    ηT 6 2 (by positivity) (by linarith) le_rfl hηT0
  set N₁ : ℝ := (513 + 64 * R ^ 3) / δ + 64 / lam + 12 * (Jc + 1) / ε + 20 / δ +
    2 * ((k : ℝ) + 4) / δ + k + 1 with hN₁
  have u1 : 0 ≤ (513 + 64 * R ^ 3) / δ := by positivity
  have u2 : 0 ≤ 64 / lam := by positivity
  have u3 : 0 ≤ 12 * (Jc + 1) / ε := by positivity
  have u4 : 0 ≤ 20 / δ := by positivity
  have u5 : 0 ≤ 2 * ((k : ℝ) + 4) / δ := by positivity
  have u6 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨max nT ⌈N₁⌉₊, fun n lab hn hodd hcls heven hdiv t htp htr htl => ?_⟩
  have hnN : N₁ ≤ n := (Nat.ceil_le.1 (le_of_max_le_right hn))
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hkn : (k : ℝ) ≤ n := by linarith
  have hδn : 513 + 64 * R ^ 3 ≤ δ * n := by
    have h : (513 + 64 * R ^ 3) / δ ≤ n := by linarith
    rw [div_le_iff₀ hδ] at h; linarith
  have hlamn : 64 ≤ lam * n := by
    have h : 64 / lam ≤ n := by linarith
    rw [div_le_iff₀ hlam0] at h; linarith
  have hεn : 12 * (Jc + 1) ≤ ε * n := by
    have h : 12 * (Jc + 1) / ε ≤ n := by linarith
    rw [div_le_iff₀ hε] at h; linarith
  have hδn20 : 20 ≤ δ * n := by
    have h : 20 / δ ≤ n := by linarith
    rw [div_le_iff₀ hδ] at h; linarith
  have hδnk : 2 * ((k : ℝ) + 4) < δ * n := by
    have h : 2 * ((k : ℝ) + 4) / δ < n := by linarith
    rw [div_lt_iff₀ hδ] at h; linarith
  have hcard : (Fintype.card (Fin n) : ℝ) = n := by simp
  have hcls' : ∀ X, δ * Fintype.card (Fin n) ≤ ksz lab X := by
    intro X; rw [hcard]; exact hcls X
  have hkszn : ∀ X, (ksz lab X : ℝ) ≤ n := by
    intro X
    have : ksz lab X ≤ n := by
      unfold ksz; exact (card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  -- the prime
  set r : ℕ := ⌊lam * n⌋₊ with hr
  have hr1 : lam * n - 1 < r := Nat.sub_one_lt_floor _
  have hr2 : (r : ℝ) ≤ lam * n := Nat.floor_le (by positivity)
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0] at hr1; push_cast at hr1; linarith
  obtain ⟨mp, hmp, hrm, hm2⟩ := Nat.exists_prime_lt_and_le_two_mul r hr0
  haveI : Fact mp.Prime := ⟨hmp⟩
  haveI : NeZero mp := ⟨hmp.ne_zero⟩
  have hmR1 : lam * n - 1 < mp := by
    have : (r : ℝ) < mp := by exact_mod_cast hrm
    linarith
  have hmR2 : (mp : ℝ) ≤ 2 * lam * n := by
    have : (mp : ℝ) ≤ 2 * r := by exact_mod_cast hm2
    linarith
  have hmlo : lam * n / 2 ≤ mp := by linarith
  have hm8 : 8 < mp := by
    have : (8 : ℝ) < mp := by linarith
    exact_mod_cast this
  have hmp0 : (0 : ℝ) ≤ mp := Nat.cast_nonneg _
  -- the placement and the leave
  have hplace : ∀ X, 9 * Fintype.card (Coord o) * mp ≤ ksz lab X := by
    intro X
    have : (9 * Fintype.card (Coord o) * mp : ℝ) ≤ ksz lab X :=
      ar_place hJc0 hlam0.le hn0.le hmR2 L4 (hcls X)
    exact_mod_cast this
  obtain ⟨P, hPτ⟩ := exists_place lab (tau3 o) (tau3_inj o) hplace
  set L := leaveG P with hL
  set Δ : ℕ := 9 * mp with hΔ
  have hdegL : ∀ p, degL L p ≤ Δ := degL_leaveG P
  have hΔR : (Δ : ℝ) ≤ 18 * lam * n := by simp only [hΔ]; push_cast; linarith
  set P0 := packG P (fun _ => false) with hP0
  have hP0L : P0.biUnion triEdges = L := packG_leave P _
  have hP0all := packG_allowed P (fun _ => false)
  have hP0disj := packG_disj P hm8 (fun _ => false)
  have hdeg0 : ∀ p, degL (P0.biUnion triEdges) p ≤ Δ := by rw [hP0L]; exact hdegL
  -- the bounded right inverse
  set mB : ℕ := ⌊δ * n⌋₊ with hmB
  have hmB1 : δ * n - 1 < mB := Nat.sub_one_lt_floor _
  have hmB2 : (mB : ℝ) ≤ δ * n := Nat.floor_le (by positivity)
  have hmBk : ∀ X, mB ≤ ksz lab X := by
    intro X; have : (mB : ℝ) ≤ ksz lab X := hmB2.trans (hcls X); exact_mod_cast this
  have h512 : 512 ≤ mB := by
    have : (512 : ℝ) ≤ mB := by
      have := pow_nonneg (show (0 : ℝ) ≤ R by linarith) 3; linarith
    exact_mod_cast this
  have hmR : 64 * R ^ 3 ≤ mB := by linarith
  have hbal : (Fintype.card (Fin n) : ℝ) ≤ R * mB := by
    rw [hcard, hR]
    exact ar_bal hδ hmB1 (by linarith)
  -- the target of the residual seed
  set s : Coord o → ℝ := fun j => (mp : ℝ) ^ 2 / 2 - Bn lab o P j with hs
  have hsb : ∀ j, |s j| ≤ 38 * lam ^ 2 * n ^ 2 := by
    intro j
    have hB0 : (0 : ℝ) ≤ Bn lab o P j := Nat.cast_nonneg _
    have hB9 : (Bn lab o P j : ℝ) ≤ 9 * (mp : ℝ) ^ 2 := by
      have := Bn_le lab o P hPτ j; exact_mod_cast this
    exact ar_s hB0 hB9 hmp0 hmR2
  set t₀ := tsh o (fun A B => (t A B : ℝ)) s with ht₀
  have hpair₀ : ∀ X Y, X ≠ Y → 2 * (t₀ X Y + t₀ Y X) = (ksz lab X : ℝ) * ksz lab Y := by
    intro X Y h
    rw [ht₀, tsh_pair]
    have := htp X Y h
    exact_mod_cast this
  have hrow₀ : ∀ X, 2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t₀ X Y =
      (ksz lab X : ℝ) * ((ksz lab X : ℝ) - 1) := by
    intro X
    rw [ht₀, tsh_row]
    have h1 : 1 ≤ ksz lab X := by
      have : (1 : ℝ) ≤ ksz lab X := by linarith [hcls X]
      exact_mod_cast this
    have := htr X
    have h' : ((2 * ∑ Y ∈ univ.filter (fun Y => Y ≠ X), t X Y : ℕ) : ℝ) =
        ((ksz lab X * (ksz lab X - 1) : ℕ) : ℝ) := by rw [this]
    push_cast [Nat.cast_sub h1] at h'
    exact h'
  set ρ : ℝ := (4 * Kc + 1) * C₀ * (18 * lam * n) * n + 1 with hρ
  have hΔseed : 8 * Kc * C₀ ^ 2 * Δ ≤ Fintype.card (Fin n) := by
    rw [hcard]
    exact ar_seed hKc0 hn0.le hΔR L1
  have hρE : (4 * Kc + 1) * C₀ * Δ * Fintype.card (Fin n) < ρ := by
    rw [hcard, hρ]
    exact ar_rho hKc0 (by linarith) hn0.le hΔR
  have hlow₀ : ∀ X Y, X ≠ Y →
      η * ksz lab X * ksz lab Y + 6 * Fintype.card (Coord o) * ρ ≤ 2 * t₀ X Y := by
    intro X Y h
    have hlo := tsh_low o (fun A B => (t A B : ℝ)) s hsb X Y
    have hcc := ar_cc (Nat.cast_nonneg (ksz lab X)) (Nat.cast_nonneg (ksz lab Y)) (hkszn X)
      (hkszn Y)
    have key := ar_low hε hJc0 hlam0.le hlam1 hKc0 (by linarith) hn1 (by positivity) hcc
      (htl X Y h) hlo L2 L3 hεn
    have e : η * ksz lab X * ksz lab Y = ε / 2 * ((ksz lab X : ℝ) * ksz lab Y) := by
      rw [hη]; ring
    rw [e]
    exact key
  obtain ⟨μ, hμ, hμm⟩ := residual_seed_exact lab hk o hR1 hmBk h512 hmR hbal hδ hη0 hcls'
    (by rw [hcard]; linarith) t₀ hpair₀ hrow₀ P0 hP0all hP0disj hdeg0 hΔseed hρE hlow₀
  rw [hP0L] at hμ hμm
  -- H2, H3, H4 on `K_n − L`
  have hbig : BigRk lab L := bigRk_of_deg hdegL (fun X => by
    have : ((k + 4) * (Δ + 1) : ℝ) < ksz lab X :=
      ar_big (Nat.cast_nonneg k) hlam0.le hn0.le hΔR L6 hδnk (hcls X)
    exact_mod_cast this)
  obtain ⟨ob, hob, hobadj⟩ := exists_baseK hbig (⟨0, by
    have : (0 : ℝ) < n := hn0; exact_mod_cast this⟩ : Fin n)
  let nx : Fin k → Fin k := fun X => if X.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hnx : ∀ X, nx X ≠ X := by
    intro X h
    simp only [nx] at h
    split_ifs at h with h0
    · have := congrArg Fin.val h; simp at this; omega
    · have := congrArg Fin.val h; simp at this; omega
  have hsum : ∑ X, ksz lab X = n := by
    unfold ksz
    rw [← card_eq_sum_card_fiberwise (f := lab) (fun _ _ => mem_univ _), card_univ,
      Fintype.card_fin]
  have hn' : Even (Fintype.card (Fin n) - 1) := by
    rw [Fintype.card_fin]; obtain ⟨m', hm'⟩ := hodd; exact ⟨m', by omega⟩
  have H2 : IsPhysical (rHostK lab L) (bicF k) (edges (rHostK lab L)) :=
    residual_physicalK hbig hob hnx hobadj o P0 hP0all hP0disj hP0L.symm hn' heven
      (pair_of_div (ksz lab) hsum hdiv)
  obtain ⟨d10, d4⟩ := ar_D (Nat.cast_nonneg Δ) hn0.le hΔR L5 hδn20
  have hΔ4 : 4 * ((Δ : ℝ) + 1) ≤ δ * Fintype.card (Fin n) := by rw [hcard]; exact d4
  have hΔ10 : 10 * ((Δ : ℝ) + 1) ≤ δ * Fintype.card (Fin n) := by rw [hcard]; exact d10
  have H3 := commonNbr_mono (residual_H3K hdegL hcls' hΔ4) (ar_sq hδ hδ1)
  have H4 := residual_H4K hdegL hδ hcls' hΔ10
  -- Theorem T with monitors on the cycle coordinates
  let w : Coord o → Finset (Fin n) → ℝ := fun i Q => wXY lab i.1.1 i.1.2 Q
  have hν : (Fintype.card (Coord o) : ℝ) ≤ (Fintype.card (Fin n) : ℝ) ^ 2 := by
    rw [hcard]
    have h1 : Fintype.card (Coord o) ≤ Fintype.card (Fin k × Fin k) := Fintype.card_subtype_le _
    rw [Fintype.card_prod, Fintype.card_fin] at h1
    have : (Fintype.card (Coord o) : ℝ) ≤ (k : ℝ) * k := by exact_mod_cast h1
    exact ar_nu this (Nat.cast_nonneg k) hkn
  have hw : ∀ i Q, IsAllowed (rHostK lab L) (bicF k) Q → |w i Q| ≤ 1 := fun i Q _ => by
    simp only [w, wXY]; split_ifs <;> norm_num
  obtain ⟨D, hD, hstat⟩ := hT (rHostK lab L) μ
    (by rw [Fintype.card_fin]; exact le_of_max_le_left hn) hμ H2 H3 H4 (Coord o) w hν hw
  -- the correction
  refine exact_from_packing lab o hm8 P hPτ D hD t htp htr fun i => ?_
  have h := hstat i
  have e1 : ∑ Q ∈ D, w i Q = (kTypeCount lab D i.1.1 i.1.2 : ℝ) := by
    simp only [w, wXY, kTypeCount]; rw [sum_boole]
  have e2 : ∑ Q ∈ allowed (rHostK lab L) (bicF k), μ Q * w i Q = t₀ i.1.1 i.1.2 := hμm i
  rw [e1, e2, hcard] at h
  have hc : t₀ i.1.1 i.1.2 = (t i.1.1 i.1.2 : ℝ) - Bn lab o P i + (mp : ℝ) ^ 2 / 2 := by
    rw [ht₀, tsh_coord]; simp only [hs]; ring
  rw [hc] at h
  have hm4 : ηT * (n : ℝ) ^ 2 ≤ (mp : ℝ) ^ 2 / 4 := by
    rw [hηT]
    exact ar_m4 hlam0.le hn0.le hmlo
  exact h.trans hm4

end CDRBicolour.KBicolor
