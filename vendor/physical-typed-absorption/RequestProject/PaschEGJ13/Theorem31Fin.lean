/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.PatternInc
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Theorem 3.1 on `Fin n` (proof by induction on `ℓ`)

`Conc31 n q g ℓ` is the conclusion of Theorem 3.1 for `ℓ`-set weight functions on `Fin n`,
for every weight function and every admissible value `M` of the normalised norm bound.
-/

@[expose] public section

namespace Pseudorandom

namespace Patt

open Finset

variable {n q : ℕ}

/-- The conclusion of Theorem 3.1 at level `ℓ`. -/
def Conc31 (n q : ℕ) (g : ℝ) (ℓ : ℕ) : Prop :=
  ∀ (w : Finset (Fin n) → ℝ), (∀ e, 0 ≤ w e) → ∀ (α : ℕ → Fin q) (M : ℝ), NB ℓ w q g M →
    ∀ lam : ℝ, 0 < lam →
      pProb (unif (Fin n) q) (fun c => lam ≤ |cnt ℓ w α c - nrm ℓ w ∅ * (1 / (q : ℝ)) ^ ℓ|) ≤
        2 ^ ℓ * Real.exp (-(lam ^ 2 / (12 * ℓ ^ 2 * M * (lam + nrm ℓ w ∅ * (1 / (q : ℝ)) ^ ℓ)))) +
          Real.exp (-(g / (24 * ℓ ^ 2)))

variable {ℓ : ℕ} {w : Finset (Fin n) → ℝ}

theorem pow_split (hq : 0 < q) {k ℓ : ℕ} (hk : k ≤ ℓ) :
    (1 / (q : ℝ)) ^ k = (q : ℝ) ^ (ℓ - k) * (1 / (q : ℝ)) ^ ℓ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have : (q : ℝ) ^ ℓ = (q : ℝ) ^ k * (q : ℝ) ^ (ℓ - k) := by
    rw [← pow_add]; congr 1; omega
  rw [one_div_pow, one_div_pow, this]
  field_simp

theorem nrm_wt_eq_zero (k : ℕ) {s : Fin n} {T' : Finset (Fin n)} (hs : s ∈ T') :
    nrm k (wt ℓ w s) T' = 0 := by
  classical
  unfold nrm wt
  refine sum_eq_zero fun T hT => ?_
  refine sum_eq_zero fun e he => ?_
  rw [mem_filter] at hT he
  exfalso
  have := hT.2 hs
  rw [← he.2.2] at this
  simp at this

theorem nb_wle (hw : ∀ e, 0 ≤ w e) {g M : ℝ} (hq : 0 < q) (hg : 0 < g) (hNB : NB ℓ w q g M)
    {k : ℕ} (hk : k ≤ ℓ) (t : ℕ) : NB k (wle ℓ w t) q g ((q : ℝ) ^ (ℓ - k) * M) := by
  intro j hj1 hjk T hT
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 := hNB j hj1 (hjk.trans hk) T hT
  have h2 := nrm_wle_le (ℓ := ℓ) (k := k) (t := t) hw T
  have hpow : (q : ℝ) ^ ℓ = (q : ℝ) ^ k * (q : ℝ) ^ (ℓ - k) := by
    rw [← pow_add]; congr 1; omega
  calc nrm k (wle ℓ w t) T * q ^ j * g ^ (j - 1) / q ^ k
      ≤ nrm ℓ w T * q ^ j * g ^ (j - 1) / q ^ k := by gcongr
    _ = (q : ℝ) ^ (ℓ - k) * (nrm ℓ w T * q ^ j * g ^ (j - 1) / q ^ ℓ) := by
        rw [hpow]; field_simp
    _ ≤ (q : ℝ) ^ (ℓ - k) * M := by gcongr

theorem nb_wt (hw : ∀ e, 0 ≤ w e) {g M : ℝ} (hq : 0 < q) (hg : 0 < g) (hM : 0 ≤ M)
    (hNB : NB ℓ w q g M) {k : ℕ} (hk : k < ℓ) (s : Fin n) :
    NB k (wt ℓ w s) q g ((q : ℝ) ^ (ℓ - k - 1) * M / g) := by
  intro j hj1 hjk T hT
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hs : s ∈ T
  · rw [nrm_wt_eq_zero k hs]; simp only [zero_mul, zero_div]; positivity
  have hcard : (insert s T).card = j + 1 := by rw [card_insert_of_notMem hs, hT]
  have h1 := hNB (j + 1) (by omega) (by omega) (insert s T) hcard
  have h2 := nrm_wt_le (ℓ := ℓ) (k := k) (t := s) hw T
  have hpow : (q : ℝ) ^ ℓ = (q : ℝ) ^ k * (q : ℝ) ^ (ℓ - k - 1) * q := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  have hg1 : g ^ (j + 1 - 1) = g ^ (j - 1) * g := by
    rw [← pow_succ]; congr 1; omega
  calc nrm k (wt ℓ w s) T * q ^ j * g ^ (j - 1) / q ^ k
      ≤ nrm ℓ w (insert s T) * q ^ j * g ^ (j - 1) / q ^ k := by gcongr
    _ = (q : ℝ) ^ (ℓ - k - 1) / g *
          (nrm ℓ w (insert s T) * q ^ (j + 1) * g ^ (j + 1 - 1) / q ^ ℓ) := by
        rw [hpow, hg1, pow_succ]; field_simp
    _ ≤ (q : ℝ) ^ (ℓ - k - 1) / g * M := by gcongr
    _ = (q : ℝ) ^ (ℓ - k - 1) * M / g := by ring

/-- `M ≥ ‖ω‖_1 q^{1-ℓ}`. -/
theorem nrm_single_le (hq : 0 < q) {g M : ℝ} (hℓ : 1 ≤ ℓ) (hNB : NB ℓ w q g M) (s : Fin n) :
    nrm ℓ w {s} ≤ (q : ℝ) ^ (ℓ - 1) * M := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h := hNB 1 le_rfl hℓ {s} (card_singleton s)
  have hpow : (q : ℝ) ^ ℓ = (q : ℝ) ^ (ℓ - 1) * q := by
    rw [← pow_succ]; congr 1; omega
  rw [pow_one, pow_zero, mul_one, hpow] at h
  rw [div_le_iff₀ (by positivity)] at h
  have : nrm ℓ w {s} * q ≤ M * ((q : ℝ) ^ (ℓ - 1) * q) := h
  nlinarith

/-- Tail bound for the first kind of bad event (via the induction hypothesis). -/
theorem tail_wle (hq : 0 < q) (hw : ∀ e, 0 ≤ w e) {g M lam : ℝ} (hg : 0 < g) (hM : 0 < M)
    (hlam : 0 < lam) (hNB : NB ℓ w q g M) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < ℓ)
    (IH : Conc31 n q g k) (α : ℕ → Fin q) (t : ℕ) :
    pProb (unif (Fin n) q) (fun c => nrm ℓ w ∅ * (1 / (q : ℝ)) ^ k + lam * (q : ℝ) ^ (ℓ - k) ≤
        cnt k (wle ℓ w t) α c) ≤
      2 ^ k * Real.exp (-(lam ^ 2 / (12 * ℓ ^ 2 * M * (lam + nrm ℓ w ∅ * (1 / (q : ℝ)) ^ ℓ)))) +
        Real.exp (-(g / (24 * k ^ 2))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set Q := (q : ℝ) ^ (ℓ - k) with hQ
  have hQ0 : 0 < Q := by positivity
  set N := nrm ℓ w ∅ with hN
  set E := N * (1 / (q : ℝ)) ^ ℓ with hE
  have hN0 : 0 ≤ N := nrm_nonneg hw ∅
  have hE0 : 0 ≤ E := by positivity
  set N' := nrm k (wle ℓ w t) ∅ with hN'
  have hN'0 : 0 ≤ N' := nrm_nonneg (fun e => wle_nonneg hw t e) ∅
  have hN'N : N' ≤ N := nrm_wle_le hw k t ∅
  have hsplit := pow_split hq hk.le
  have h := IH (wle ℓ w t) (fun e => wle_nonneg hw t e) α (Q * M)
    (nb_wle hw hq hg hNB hk.le t) (lam * Q) (by positivity)
  refine le_trans (pProb_mono (unif_isPMF q hq) fun c hc => ?_) (h.trans ?_)
  · -- event inclusion
    have : N' * (1 / (q : ℝ)) ^ k ≤ N * (1 / (q : ℝ)) ^ k :=
      mul_le_mul_of_nonneg_right hN'N (by positivity)
    rw [le_abs]; left; linarith
  · -- compare the exponents
    have hE' : N' * (1 / (q : ℝ)) ^ k ≤ Q * E := by
      rw [hsplit, hE]
      have := mul_le_mul_of_nonneg_right hN'N (show (0 : ℝ) ≤ Q * (1 / (q : ℝ)) ^ ℓ by positivity)
      linarith
    have hk2 : (k : ℝ) ^ 2 ≤ (ℓ : ℝ) ^ 2 := by
      have : (k : ℝ) ≤ ℓ := by exact_mod_cast hk.le
      exact pow_le_pow_left₀ (by positivity) this 2
    have hden : 12 * (k : ℝ) ^ 2 * (Q * M) * (lam * Q + N' * (1 / (q : ℝ)) ^ k) ≤
        Q ^ 2 * (12 * ℓ ^ 2 * M * (lam + E)) := by
      have h1 : lam * Q + N' * (1 / (q : ℝ)) ^ k ≤ Q * (lam + E) := by nlinarith
      have h2 : 0 ≤ lam * Q + N' * (1 / (q : ℝ)) ^ k := by positivity
      calc 12 * (k : ℝ) ^ 2 * (Q * M) * (lam * Q + N' * (1 / (q : ℝ)) ^ k)
          ≤ 12 * (ℓ : ℝ) ^ 2 * (Q * M) * (Q * (lam + E)) := by gcongr
        _ = Q ^ 2 * (12 * ℓ ^ 2 * M * (lam + E)) := by ring
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hexp : Real.exp (-((lam * Q) ^ 2 / (12 * (k : ℝ) ^ 2 * (Q * M) *
        (lam * Q + N' * (1 / (q : ℝ)) ^ k)))) ≤
        Real.exp (-(lam ^ 2 / (12 * ℓ ^ 2 * M * (lam + E)))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff]
      calc lam ^ 2 / (12 * ℓ ^ 2 * M * (lam + E))
          = (lam * Q) ^ 2 / (Q ^ 2 * (12 * ℓ ^ 2 * M * (lam + E))) := by
            field_simp
        _ ≤ (lam * Q) ^ 2 / (12 * (k : ℝ) ^ 2 * (Q * M) *
              (lam * Q + N' * (1 / (q : ℝ)) ^ k)) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have hN'eq : nrm k (wle ℓ w t) ∅ = N' := rfl
    rw [hN'eq]
    linarith [mul_le_mul_of_nonneg_left hexp (show (0:ℝ) ≤ 2 ^ k by positivity)]

/-- Tail bound for the second kind of bad event (via the induction hypothesis). -/
theorem tail_wt (hq : 0 < q) (hw : ∀ e, 0 ≤ w e) {g M : ℝ} (hg : 0 < g) (hM : 0 < M)
    (hNB : NB ℓ w q g M) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < ℓ)
    (IH : Conc31 n q g k) (α : ℕ → Fin q) (s : Fin n) :
    pProb (unif (Fin n) q) (fun c => 2 * ((q : ℝ) ^ (ℓ - k - 1) * M) ≤ cnt k (wt ℓ w s) α c) ≤
      (2 ^ k + 1) * Real.exp (-(g / (24 * k ^ 2))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set L := (q : ℝ) ^ (ℓ - k - 1) * M with hL
  have hL0 : 0 < L := by positivity
  set N' := nrm k (wt ℓ w s) ∅ with hN'
  have hN'0 : 0 ≤ N' := nrm_nonneg (fun e => wt_nonneg hw s e) ∅
  set E' := N' * (1 / (q : ℝ)) ^ k with hE'
  have hE'0 : 0 ≤ E' := by positivity
  have hE'L : E' ≤ L := by
    have h1 : N' ≤ nrm ℓ w {s} := by
      have := nrm_wt_le (ℓ := ℓ) (k := k) (t := s) hw ∅
      simpa using this
    have h2 := nrm_single_le hq (by omega : 1 ≤ ℓ) hNB s
    have hsplit : (q : ℝ) ^ (ℓ - 1) * (1 / (q : ℝ)) ^ k = (q : ℝ) ^ (ℓ - k - 1) := by
      have : (q : ℝ) ^ (ℓ - 1) = (q : ℝ) ^ (ℓ - k - 1) * (q : ℝ) ^ k := by
        rw [← pow_add]; congr 1; omega
      rw [this, one_div_pow]; field_simp
    calc E' ≤ (q : ℝ) ^ (ℓ - 1) * M * (1 / (q : ℝ)) ^ k :=
          mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
      _ = L := by rw [hL, ← hsplit]; ring
  have h := IH (wt ℓ w s) (fun e => wt_nonneg hw s e) α (L / g)
    (by have := nb_wt hw hq hg hM.le hNB hk s; rwa [← hL] at this) L hL0
  refine le_trans (pProb_mono (unif_isPMF q hq) fun c hc => ?_) (h.trans ?_)
  · rw [le_abs]; left; linarith
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hexp : Real.exp (-(L ^ 2 / (12 * (k : ℝ) ^ 2 * (L / g) * (L + E')))) ≤
        Real.exp (-(g / (24 * k ^ 2))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff]
      have hden : 12 * (k : ℝ) ^ 2 * (L / g) * (L + E') ≤ 24 * k ^ 2 * L ^ 2 / g := by
        rw [show 24 * (k : ℝ) ^ 2 * L ^ 2 / g = 12 * k ^ 2 * (L / g) * (2 * L) by ring]
        gcongr; linarith
      calc g / (24 * k ^ 2) = L ^ 2 / (24 * k ^ 2 * L ^ 2 / g) := by field_simp
        _ ≤ L ^ 2 / (12 * (k : ℝ) ^ 2 * (L / g) * (L + E')) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have : (2 : ℝ) ^ k * Real.exp (-(L ^ 2 / (12 * (k : ℝ) ^ 2 * (L / g) * (L + E')))) ≤
        2 ^ k * Real.exp (-(g / (24 * k ^ 2))) := by gcongr
    have hE'eq : nrm k (wt ℓ w s) ∅ * (1 / (q : ℝ)) ^ k = E' := rfl
    rw [hE'eq]
    linarith

end Patt

end Pseudorandom
