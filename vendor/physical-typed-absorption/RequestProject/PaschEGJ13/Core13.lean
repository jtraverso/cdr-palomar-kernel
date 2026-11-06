/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.Assembly13
public import RequestProject.PaschEGJ13.Step3_13
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Steps 1–3 of the proof of Theorem 1.3 for a fixed `Δ` -/

@[expose] public section

namespace Pseudorandom

open Finset

set_option maxHeartbeats 40000000 in
/-- Steps 1–3 of the proof of Theorem 1.3 for a fixed `Δ`. -/
theorem core_1_3 (r L : ℕ) (hr : 2 ≤ r) (hL : 1 ≤ L) (δ ε a b ρ κ σ D₀ : ℝ) (hε : 0 < ε)
    (ha0 : 0 < a) (hb : b = 2 * L * a + 4 * ε) (hb1 : b ≤ 1) (ha5 : 5 * ε ≤ a)
    (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hσ : 0 ≤ σ)
    (hnib : ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (H : Finset (Finset V)), IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ D ^ κ) → (H.card : ℝ) ≤ Real.exp (D ^ σ) →
      ∃ μ : Finset (Finset V) → ℝ, (∀ M, 0 ≤ μ M) ∧ ∑ M, μ M = 1 ∧
        (∀ M, μ M ≠ 0 → IsMatching M ∧ M ⊆ H) ∧
        ∀ e ∈ H, (1 - D ^ (-ρ)) / D ≤ ∑ M, μ M * (if e ∈ M then 1 else 0))
    (Δ : ℝ) (F : Facts13 r L δ ε a b ρ κ σ D₀ Δ)
    (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (huni : IsUniform H r)
    (hdeg : ∀ v, (degree H v : ℝ) ≤ Δ)
    (hcod : ∀ u v, u ≠ v → (codegree H u v : ℝ) ≤ Δ ^ (1 - δ))
    (hcard : (H.card : ℝ) ≤ Real.exp (Δ ^ (ε ^ 2)))
    (ι : ℕ → Type) [∀ ℓ, Fintype (ι ℓ)] (W : (ℓ : ℕ) → ι ℓ → Finset (Finset V) → ℝ)
    (hι : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → (Fintype.card (ι ℓ) : ℝ) ≤ Real.exp (Δ ^ (ε ^ 2)))
    (hW0 : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → ∀ k, ∀ S ∈ H.powersetCard ℓ, 0 ≤ W ℓ k S)
    (hclean : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → ∀ k, ∀ S ∈ H.powersetCard ℓ, W ℓ k S ≠ 0 → IsMatching S) :
    ∃ M ⊆ H, IsMatching M ∧ ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → ∀ k : ι ℓ,
      (∀ j, 1 ≤ j → j ≤ ℓ → ∀ T ∈ H.powersetCard j,
        tdeg ℓ (W ℓ k) H T * Δ ^ ((j : ℝ) + δ) ≤ tweight ℓ (W ℓ k) H) →
      |tweight ℓ (W ℓ k) M - tweight ℓ (W ℓ k) H / Δ ^ ℓ| ≤
        Δ ^ (-ε) * (tweight ℓ (W ℓ k) H / Δ ^ ℓ) := by
  classical
  have hD2 := F.h1
  have hD0 : 0 < Δ := by linarith
  have hD1 : 1 ≤ Δ := by linarith
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set ξ : ℝ := Δ ^ (-(2 * ε)) with hξ
  have hξ0 : 0 < ξ := Real.rpow_pos_of_pos hD0 _
  have hξ1 : ξ ≤ 1 / 2 := F.h4
  set C : ℝ := Δ ^ (1 - δ) with hC
  have hC0 : 0 < C := Real.rpow_pos_of_pos hD0 _
  set η : ℝ := Δ ^ (-(1 + δ)) with hη
  have hη0 : 0 < η := Real.rpow_pos_of_pos hD0 _
  set Xb : ℝ := 2 * Δ ^ b with hXb
  have hDb1 : 1 ≤ Δ ^ b := Real.one_le_rpow hD1 (by rw [hb]; positivity)
  have hDbD : Δ ^ b ≤ Δ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hD1 hb1
  have hXb1 : 1 ≤ Xb := by rw [hXb]; linarith
  -- the number of parts
  set p : ℕ := ⌈Δ ^ b⌉₊ with hpdef
  have hp_ge : Δ ^ b ≤ p := Nat.le_ceil _
  have hp_le : (p : ℝ) ≤ Xb := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Δ ^ b by linarith)
    rw [hXb]; linarith
  have hp1 : (1 : ℝ) ≤ p := hDb1.trans hp_ge
  have hp0 : 0 < p := by exact_mod_cast (lt_of_lt_of_le one_pos hp1)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hpD : (p : ℝ) ≤ 2 * Δ := by rw [hXb] at hp_le; linarith
  set P : ℝ := (p : ℝ) ^ (r - 1) with hPdef
  have hP1 : 1 ≤ P := one_le_pow₀ hp1
  have hPX : P ≤ Xb ^ (r - 1) := pow_le_pow_left₀ (by linarith) hp_le _
  set Y : ℝ := Δ ^ (1 - a) with hY
  have hPY : P ≤ Y := hPX.trans F.h2
  have hY1 : 1 ≤ Y := hP1.trans hPY
  have hpr : (p : ℝ) ^ r = p * P := by
    rw [hPdef, ← pow_succ']; congr 1; omega
  -- the number of edge classes
  set q : ℕ := ⌈Y / P⌉₊ with hqdef
  have hq_ge : Y / P ≤ q := Nat.le_ceil _
  have hq0 : 0 < q := Nat.ceil_pos.mpr (by positivity)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqP_ge : Y ≤ q * P := by rwa [div_le_iff₀ (by linarith)] at hq_ge
  have hqP_le : q * P ≤ 2 * Y := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Y / P by positivity)
    rw [← hqdef] at this
    have h2 : (q : ℝ) * P < (Y / P + 1) * P := mul_lt_mul_of_pos_right this (by linarith)
    rw [add_mul, div_mul_cancel₀ _ (by linarith), one_mul] at h2
    linarith
  have hYD : Y ≤ Δ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hD1 (show 1 - a ≤ 1 by linarith)
  have hq_le : (q : ℝ) ≤ 2 * Δ := by
    have : (q : ℝ) ≤ q * P := le_mul_of_one_le_right hqR.le hP1
    linarith
  -- the hypergraph
  have hne : ∀ e ∈ H, e.Nonempty := fun e he => by rw [← card_pos, huni e he]; omega
  set U := H.biUnion id with hU
  set X₀ : ℝ := Δ ^ (ε ^ 2) with hX₀
  set Y₀ : ℝ := Δ ^ ε / 64 with hY₀
  have heX : 1 ≤ Real.exp X₀ := Real.one_le_exp (Real.rpow_pos_of_pos hD0 _).le
  have hUcard : (U.card : ℝ) ≤ r * Real.exp X₀ := by
    have h1 : U.card ≤ ∑ e ∈ H, (id e).card := card_biUnion_le
    have h2 : ∑ e ∈ H, (id e).card = H.card * r := sum_const_nat (fun e he => huni e he)
    have h3 : (U.card : ℝ) ≤ H.card * r := by exact_mod_cast h2 ▸ h1
    have : (0 : ℝ) ≤ r := by positivity
    calc (U.card : ℝ) ≤ H.card * r := h3
      _ ≤ Real.exp X₀ * r := mul_le_mul_of_nonneg_right hcard this
      _ = r * Real.exp X₀ := mul_comm _ _
  have hexpY : ∀ E : ℝ, Y₀ ≤ E → Real.exp (-E) ≤ Real.exp (-Y₀) := fun E h =>
    Real.exp_le_exp.mpr (by linarith)
  have hY₀pos : 0 < Real.exp (-Y₀) := Real.exp_pos _
  -- the weight functions, indexed by a single type
  set ℓf : (Σ j : Fin L, ι ((j : ℕ) + 1)) → ℕ := fun k => (k.1 : ℕ) + 1 with hℓf
  set Wf : (Σ j : Fin L, ι ((j : ℕ) + 1)) → Finset (Finset V) → ℝ := fun k => W ((k.1 : ℕ) + 1) k.2 with hWf
  have hℓ1 : ∀ k, 1 ≤ ℓf k := fun k => by simp [hℓf]
  have hℓL : ∀ k, ℓf k ≤ L := fun k => by simp only [hℓf]; omega
  have hWf0 : ∀ k, ∀ S ∈ H.powersetCard (ℓf k), 0 ≤ Wf k S :=
    fun k => hW0 _ (hℓ1 k) (hℓL k) k.2
  have hWfc : ∀ k, ∀ S ∈ H.powersetCard (ℓf k), Wf k S ≠ 0 → IsMatching S :=
    fun k => hclean _ (hℓ1 k) (hℓL k) k.2
  set Kall : Finset (Σ j : Fin L, ι ((j : ℕ) + 1)) := univ.filter (fun k : (Σ j : Fin L, ι ((j : ℕ) + 1)) =>
    (∀ j, 1 ≤ j → j ≤ ℓf k → ∀ T ∈ H.powersetCard j,
      tdeg (ℓf k) (Wf k) H T * Δ ^ ((j : ℝ) + δ) ≤ tweight (ℓf k) (Wf k) H) ∧
    0 < tweight (ℓf k) (Wf k) H) with hKall
  have hKcard : (Kall.card : ℝ) ≤ L * Real.exp X₀ := by
    have h1 : (Kall.card : ℝ) ≤ Fintype.card (Σ j : Fin L, ι ((j : ℕ) + 1)) := by exact_mod_cast card_le_univ Kall
    have h2 : (Fintype.card (Σ j : Fin L, ι ((j : ℕ) + 1)) : ℝ) = ∑ j : Fin L, (Fintype.card (ι ((j : ℕ) + 1)) : ℝ) := by
      rw [Fintype.card_sigma]; push_cast; rfl
    have h3 : ∑ j : Fin L, (Fintype.card (ι ((j : ℕ) + 1)) : ℝ) ≤ ∑ _j : Fin L, Real.exp X₀ :=
      sum_le_sum fun j _ => hι _ (by omega) (by omega)
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    linarith
  have hKnorm : ∀ k ∈ Kall, ∀ j, 1 ≤ j → j ≤ ℓf k → ∀ T ∈ H.powersetCard j,
      tdeg (ℓf k) (Wf k) H T * Δ ^ ((j : ℝ) + δ) ≤ tweight (ℓf k) (Wf k) H :=
    fun k hk => by simp only [hKall, mem_filter] at hk; exact hk.2.1
  have hKpos : ∀ k ∈ Kall, 0 < tweight (ℓf k) (Wf k) H := fun k hk => by
    simp only [hKall, mem_filter] at hk; exact hk.2.2
  have hKη : ∀ k ∈ Kall, ∀ e ∈ H, tdeg (ℓf k) (Wf k) H {e} ≤ η * tweight (ℓf k) (Wf k) H := by
    intro k hk e he
    have h := hKnorm k hk 1 le_rfl (hℓ1 k) {e} (by simp [he])
    have hpos : 0 < Δ ^ (1 + δ) := Real.rpow_pos_of_pos hD0 _
    rw [hη, Real.rpow_neg hD0.le, ← div_eq_inv_mul, le_div_iff₀ hpos]
    simpa using h
  have hℓp : ∀ k, ℓf k ≤ p := by
    intro k
    have h1 : (ℓf k : ℝ) ≤ L := by exact_mod_cast hℓL k
    have h2 : (L : ℝ) ≤ 2 * (L : ℝ) ^ 2 := by nlinarith
    have : (ℓf k : ℝ) ≤ p := by linarith [F.h16]
    exact_mod_cast this
  -- union bound bookkeeping
  set Z8 : ℝ := (8 * (L : ℝ)) ^ (4 * L) with hZ8
  obtain ⟨hZ4, hZ2L, hZ8L⟩ := big_const_bounds hL
  set G : ℝ := (r : ℝ) ^ 2 * Z8 * Δ ^ (2 * L + 2) * (Real.exp X₀ * Real.exp X₀) with hG
  have hunion : 256 * G * Real.exp (-Y₀) < 1 := by
    have := F.h6
    rw [show 2 * Δ ^ (ε ^ 2) - Δ ^ ε / 64 = X₀ + X₀ + -Y₀ by rw [hX₀, hY₀]; ring,
      Real.exp_add, Real.exp_add] at this
    have e : nc13 r L * Δ ^ (2 * L + 2) * (Real.exp X₀ * Real.exp X₀ * Real.exp (-Y₀)) =
        256 * G * Real.exp (-Y₀) := by rw [hG, nc13]; ring
    linarith
  have hterm : ∀ (c : ℝ), 0 ≤ c → c ≤ Z8 → ∀ m, m ≤ 2 * L + 2 → ∀ k, k ≤ 2 →
      c * (r : ℝ) ^ k * Δ ^ m * Real.exp X₀ ≤ G := fun c hc0 hc m hm k hk =>
    union_term_le hr hD2 heX hc0 hc hm k hk
  have hG0 : 0 ≤ G := by positivity
  -- the exponent lower bound
  have hDη : Δ * η = Δ ^ (-δ) := by
    rw [hη, show -δ = 1 + -(1 + δ) by ring, Real.rpow_add hD0, Real.rpow_one]
  have hDη0 : 0 < Δ * η := by positivity
  set s₀ : ℝ := ξ / 2 * (1 / Xb) ^ (r * L) with hs₀
  have hs₀pos : 0 < s₀ := by positivity
  have hS0 : 24 * (L : ℝ) ^ 2 * (r * L + 1) * (Δ * η) * Y₀ ≤ s₀ ^ 2 := by
    set Q : ℝ := Xb ^ (2 * r * L) with hQ
    have hQ0 : 0 < Q := by positivity
    have e1 : s₀ ^ 2 = Δ ^ (-(4 * ε)) / (4 * Q) := by
      rw [hs₀, hQ, mul_pow, div_pow, hξ, rpow_sq' hD0, ← pow_mul, one_div_pow]
      rw [show 2 * -(2 * ε) = -(4 * ε) by ring, show r * L * 2 = 2 * r * L by ring]
      field_simp
      ring
    have e2 : Δ ^ (-(4 * ε)) = Δ ^ (δ - 4 * ε) * Δ ^ (-δ) := by
      rw [← Real.rpow_add hD0]; ring_nf
    rw [e1, e2, hDη, le_div_iff₀ (by positivity), hY₀]
    have h12 := F.h12
    rw [← hXb, ← hQ] at h12
    have hDδ : 0 < Δ ^ (-δ) := Real.rpow_pos_of_pos hD0 _
    have hDε : 0 < Δ ^ ε := Real.rpow_pos_of_pos hD0 _
    have hrL : (0 : ℝ) ≤ r * L + 1 := by positivity
    have := mul_le_mul_of_nonneg_right h12 hDδ.le
    have h0 : 0 ≤ (L : ℝ) ^ 2 * (r * L + 1) * Q * Δ ^ ε * Δ ^ (-δ) := by positivity
    have e3 : 24 * (L : ℝ) ^ 2 * (r * L + 1) * Δ ^ (-δ) * (Δ ^ ε / 64) * (4 * Q) =
        3 / 2 * ((L : ℝ) ^ 2 * (r * L + 1) * Q * Δ ^ ε * Δ ^ (-δ)) := by ring
    have e4 : 1024 * (r * (L : ℝ) + 1) * L ^ 2 * Q * Δ ^ ε * Δ ^ (-δ) =
        1024 * ((L : ℝ) ^ 2 * (r * L + 1) * Q * Δ ^ ε * Δ ^ (-δ)) := by ring
    rw [e3]
    linarith
  have hexpo : ∀ k, ∀ s, s₀ ≤ s → s ≤ 1 →
      Y₀ ≤ s ^ 2 / (2 * Δ * η * (r * (ℓf k : ℝ) + s)) := by
    intro k s hs hs1
    rw [show 2 * Δ * η = 2 * (Δ * η) by ring]
    refine expo_lb hs₀pos hs hs1 hDη0 (by positivity) ?_
    have hℓ : (ℓf k : ℝ) ≤ L := by exact_mod_cast hℓL k
    have h1 : 2 * ((r : ℝ) * ℓf k + 1) ≤ 24 * (L : ℝ) ^ 2 * (r * L + 1) := by
      have : (r : ℝ) * ℓf k ≤ r * L := by gcongr
      have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
      have h0 : (0 : ℝ) ≤ r * L + 1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hL2 h0]
    have hY0 : 0 ≤ Y₀ := by positivity
    have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hDη0.le hY0)
    nlinarith
  -- per-weight quantities
  have hρlo : ∀ k, (1 / Xb) ^ (r * L) ≤ (1 / (p : ℝ)) ^ (r * ℓf k) := by
    intro k
    calc (1 / Xb) ^ (r * L) ≤ (1 / (p : ℝ)) ^ (r * L) :=
          pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hpR hp_le) _
      _ ≤ (1 / (p : ℝ)) ^ (r * ℓf k) :=
          pow_le_pow_of_le_one (by positivity) (by rw [div_le_one hpR]; exact hp1)
            (Nat.mul_le_mul_left r (hℓL k))
  have hpℓρ : ∀ k, (p : ℝ) ^ ℓf k * (1 / (p : ℝ)) ^ (r * ℓf k) ≤ 1 := by
    intro k
    rw [one_div_pow, mul_one_div, div_le_one (by positivity)]
    exact pow_le_pow_right₀ hp1 (Nat.le_mul_of_pos_left _ (by omega))
  have hdF : ∀ k, (1 / 2 : ℝ) * (p : ℝ) ^ ℓf k ≤ p.descFactorial (ℓf k) ∧
      (p.descFactorial (ℓf k) : ℝ) ≤ (p : ℝ) ^ ℓf k := by
    intro k
    obtain ⟨h1, h2⟩ := descFactorial_ratio p hp0 (ℓf k) (hℓp k)
    refine ⟨le_trans ?_ h1, h2⟩
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hℓ : (ℓf k : ℝ) ≤ L := by exact_mod_cast hℓL k
    have : (ℓf k : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hℓ 2
    have : (ℓf k : ℝ) ^ 2 / p ≤ 1 / 2 := by
      rw [div_le_iff₀ hpR]; linarith [F.h16]
    linarith
  have hsD : ∀ k, s₀ ≤ ξ * (p.descFactorial (ℓf k) * (1 / (p : ℝ)) ^ (r * ℓf k)) ∧
      ξ * (p.descFactorial (ℓf k) * (1 / (p : ℝ)) ^ (r * ℓf k)) ≤ 1 := by
    intro k
    obtain ⟨h1, h2⟩ := hdF k
    have hρ0 : 0 ≤ (1 / (p : ℝ)) ^ (r * ℓf k) := by positivity
    have hpl : (1 : ℝ) ≤ (p : ℝ) ^ ℓf k := one_le_pow₀ hp1
    constructor
    · rw [hs₀, show ξ / 2 * (1 / Xb) ^ (r * L) = ξ * (1 / 2 * (1 / Xb) ^ (r * L)) by ring]
      apply mul_le_mul_of_nonneg_left _ hξ0.le
      calc 1 / 2 * (1 / Xb) ^ (r * L) ≤ 1 / 2 * (1 / (p : ℝ)) ^ (r * ℓf k) := by
            gcongr; exact hρlo k
        _ ≤ 1 / 2 * (p : ℝ) ^ ℓf k * (1 / (p : ℝ)) ^ (r * ℓf k) := by
            rw [mul_assoc]; gcongr; exact le_mul_of_one_le_left hρ0 hpl
        _ ≤ _ := by gcongr
    · have : (p.descFactorial (ℓf k) : ℝ) * (1 / (p : ℝ)) ^ (r * ℓf k) ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_right h2 hρ0) (hpℓρ k)
      have : 0 ≤ (p.descFactorial (ℓf k) : ℝ) * (1 / (p : ℝ)) ^ (r * ℓf k) := by positivity
      nlinarith
  have hsY : ∀ k, s₀ ≤ (ℓf k : ℝ) ^ ℓf k * (1 / (p : ℝ)) ^ (r * ℓf k) ∧
      (ℓf k : ℝ) ^ ℓf k * (1 / (p : ℝ)) ^ (r * ℓf k) ≤ 1 := by
    intro k
    have hρ0 : 0 ≤ (1 / (p : ℝ)) ^ (r * ℓf k) := by positivity
    have hl1 : (1 : ℝ) ≤ (ℓf k : ℝ) ^ ℓf k := one_le_pow₀ (by exact_mod_cast hℓ1 k)
    constructor
    · calc s₀ ≤ (1 / Xb) ^ (r * L) := by
            rw [hs₀]
            have : ξ / 2 ≤ 1 := by linarith
            have : 0 ≤ (1 / Xb) ^ (r * L) := by positivity
            nlinarith
        _ ≤ (1 / (p : ℝ)) ^ (r * ℓf k) := hρlo k
        _ ≤ _ := le_mul_of_one_le_left hρ0 hl1
    · have : (ℓf k : ℝ) ^ ℓf k ≤ (p : ℝ) ^ ℓf k :=
        pow_le_pow_left₀ (by positivity) (by exact_mod_cast hℓp k) _
      exact le_trans (mul_le_mul_of_nonneg_right this hρ0) (hpℓρ k)
  -- Step 1: the vertex partition
  have hXb2 : P ^ 2 ≤ Xb ^ (2 * r) := by
    calc P ^ 2 ≤ (Xb ^ (r - 1)) ^ 2 := pow_le_pow_left₀ (by linarith) hPX 2
      _ = Xb ^ (2 * (r - 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ Xb ^ (2 * r) := pow_le_pow_right₀ hXb1 (by omega)
  have hE2 := e2_bound r hD0 hξ (by linarith) hC hp1 hP1 hXb2 F.h5
  have hbad1 := tuple_vertex_bad hp0 r (by omega) H huni Δ η ξ hD0 hη0 hξ0 hdeg Kall ℓf Wf
    (fun k _ => hWf0 k) (fun k _ => hWfc k) hKpos hKη (fun k _ => hℓp k)
  set πB1 : ℝ := ∑ k ∈ Kall, (2 * Real.exp (-((ξ * (p.descFactorial (ℓf k) *
      (1 / (p : ℝ)) ^ (r * ℓf k))) ^ 2 / (2 * Δ * η * (r * ℓf k + ξ * (p.descFactorial (ℓf k) *
      (1 / (p : ℝ)) ^ (r * ℓf k)))))) + (p : ℝ) ^ ℓf k *
      Real.exp (-(((ℓf k : ℝ) ^ ℓf k * (1 / (p : ℝ)) ^ (r * ℓf k)) ^ 2 /
        (2 * Δ * η * (r * ℓf k + (ℓf k : ℝ) ^ ℓf k * (1 / (p : ℝ)) ^ (r * ℓf k)))))) with hπB1
  have hπB1le : πB1 ≤ Kall.card * (2 + (2 * Δ) ^ L) * Real.exp (-Y₀) := by
    rw [hπB1]
    calc _ ≤ ∑ _k ∈ Kall, (2 + (2 * Δ) ^ L) * Real.exp (-Y₀) := by
          refine sum_le_sum fun k hk => ?_
          have e1 := hexpY _ (hexpo k _ (hsD k).1 (hsD k).2)
          have e2 := hexpY _ (hexpo k _ (hsY k).1 (hsY k).2)
          have hpL : (p : ℝ) ^ ℓf k ≤ (2 * Δ) ^ L :=
            (pow_le_pow_right₀ hp1 (hℓL k)).trans (pow_le_pow_left₀ (by positivity) hpD L)
          have : 0 ≤ (p : ℝ) ^ ℓf k := by positivity
          nlinarith [Real.exp_pos (-Y₀)]
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  obtain ⟨τ, hτdeg, -, hτbad⟩ := vertex_partition_ext (K := (∅ : Finset Unit))
    hp0 H r (by omega) huni Δ C η ξ hD0 hC0 hη0 hξ0 hdeg hcod (fun _ _ => (0 : ℝ))
    (by simp) (by simp) (by simp) _ πB1 hbad1 (by
      refine lt_of_le_of_lt ?_ hunion
      have e1 := hexpY _ hE2
      have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
      have hK0 : (0 : ℝ) ≤ Kall.card := Nat.cast_nonneg _
      simp only [card_empty, Nat.cast_zero, mul_zero, zero_mul, add_zero]
      have hA : ((H.biUnion id).card : ℝ) * p * Real.exp (-(ξ ^ 2 * Δ / (2 * C *
          (r * ((p : ℝ) ^ (r - 1)) ^ 2 / p + ξ * (p : ℝ) ^ (r - 1))))) ≤
          (r * Real.exp X₀ * (2 * Δ)) * Real.exp (-Y₀) :=
        mul_le_mul (mul_le_mul hUcard hpD (by positivity) (by positivity)) e1 (by positivity)
          (by positivity)
      have hB : πB1 ≤ L * Real.exp X₀ * (2 + (2 * Δ) ^ L) * Real.exp (-Y₀) :=
        hπB1le.trans (by gcongr)
      have hC' : (r * Real.exp X₀ * (2 * Δ)) * Real.exp (-Y₀) +
          L * Real.exp X₀ * (2 + (2 * Δ) ^ L) * Real.exp (-Y₀) ≤ (G + G + G) * Real.exp (-Y₀) := by
        have e : (r * Real.exp X₀ * (2 * Δ)) * Real.exp (-Y₀) +
            L * Real.exp X₀ * (2 + (2 * Δ) ^ L) * Real.exp (-Y₀) =
            (2 * (r : ℝ) ^ 1 * Δ ^ 1 * Real.exp X₀ + 2 * L * (r : ℝ) ^ 0 * Δ ^ 0 * Real.exp X₀ +
            L * 2 ^ L * (r : ℝ) ^ 0 * Δ ^ L * Real.exp X₀) * Real.exp (-Y₀) := by
          rw [mul_pow]; ring
        rw [e]
        have h2L1 : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
        gcongr
        · exact hterm 2 (by norm_num) (by linarith) 1 (by omega) 1 (by omega)
        · exact hterm (2 * L) (by positivity) (by nlinarith) 0 (by omega) 0 (by omega)
        · exact hterm (L * 2 ^ L) (by positivity) (by nlinarith) L (by omega) 0 (by omega)
      nlinarith)
  simp only [not_exists, not_and, not_or, not_not] at hτbad
  -- Step 2: the edge partition
  set A : Fin p → Finset (Finset V) := part H τ with hAdef
  letI : LinearOrder {e // e ∈ H} :=
    LinearOrder.lift' (Fintype.equivFin {e // e ∈ H}) (Fintype.equivFin _).injective
  set gg : ℝ := Δ ^ (2 * ε) with hgg
  have hgg1 : 1 ≤ gg := Real.one_le_rpow hD1 (by positivity)
  have hq2Y : (q : ℝ) ≤ 2 * Y := by
    have : (q : ℝ) ≤ q * P := le_mul_of_one_le_right hqR.le hP1
    linarith
  have hqg : (q : ℝ) * gg ≤ Δ := by
    have := F.h15
    rw [← hY, ← hgg] at this
    have : (q : ℝ) * gg ≤ 2 * Y * gg := mul_le_mul_of_nonneg_right hq2Y (by positivity)
    linarith
  have hqΔ : (q : ℝ) ≤ Δ := le_trans (le_mul_of_one_le_right hqR.le hgg1) hqg
  have hlogH : Real.log (Fintype.card {e // e ∈ H}) ≤ X₀ := by
    rw [Fintype.card_coe]
    rcases Nat.eq_zero_or_pos H.card with h | h
    · rw [h]; simp only [Nat.cast_zero, Real.log_zero]; positivity
    · calc Real.log H.card ≤ Real.log (Real.exp X₀) :=
            Real.log_le_log (by exact_mod_cast h) hcard
        _ = X₀ := Real.log_exp X₀
  set Ybd : (Σ j : Fin L, ι ((j : ℕ) + 1)) → ℝ := fun k =>
    2 * ((ℓf k : ℝ) ^ ℓf k * (1 / (p : ℝ)) ^ (r * ℓf k)) * tweight (ℓf k) (Wf k) H with hYbd
  have hYpos : ∀ k ∈ Kall, 0 < Ybd k := by
    intro k hk
    have := hKpos k hk
    have := (hsY k).1
    simp only [hYbd]; positivity
  have hbad2 := tuple_edge_bad hq0 H A Δ δ gg hD0 (by positivity) hqΔ hqg Kall ℓf Wf
    (fun k _ => hℓ1 k) (fun k _ => hWf0 k) hKpos hKnorm Ybd hYpos
    (fun k hk u => (hτbad k hk).2 u) (fun k hk => by
      have hℓ : (ℓf k : ℝ) ≤ L := by exact_mod_cast hℓL k
      have := F.h13
      rw [← hX₀, ← hgg] at this
      have h1 : 24 * (ℓf k : ℝ) ^ 3 * (ℓf k + 1 + Real.log (Fintype.card {e // e ∈ H})) ≤
          24 * (L : ℝ) ^ 3 * (L + 1 + X₀) := by
        have : (0 : ℝ) ≤ Real.log (Fintype.card {e // e ∈ H}) :=
          Real.log_natCast_nonneg _
        gcongr
      linarith)
  set πB2 : ℝ := ∑ k ∈ Kall, ((p : ℝ) * q) ^ ℓf k * ((ℓf k : ℝ) ^ ℓf k * (2 ^ ℓf k *
      Real.exp (-(Ybd k * (1 / (q : ℝ)) ^ ℓf k / (24 * (ℓf k : ℝ) ^ 2 *
        (tweight (ℓf k) (Wf k) H * Δ ^ (-δ) / (q : ℝ) ^ ℓf k)))) +
      Real.exp (-(gg / (24 * (ℓf k : ℝ) ^ 2))))) with hπB2
  have hπB2le : πB2 ≤ Kall.card * ((4 * Δ ^ 2) ^ L * ((L : ℝ) ^ L * (2 ^ L + 1))) *
      Real.exp (-Y₀) := by
    rw [hπB2]
    calc _ ≤ ∑ _k ∈ Kall, ((4 * Δ ^ 2) ^ L * ((L : ℝ) ^ L * (2 ^ L + 1))) * Real.exp (-Y₀) := by
          refine sum_le_sum fun k hk => ?_
          have hℓ0 : (0 : ℝ) < ℓf k := by exact_mod_cast hℓ1 k
          have hℓ : (ℓf k : ℝ) ≤ L := by exact_mod_cast hℓL k
          have hY0 : 0 ≤ Y₀ := by positivity
          have hsk : 12 * (ℓf k : ℝ) ^ 2 * Δ ^ (-δ) * Y₀ ≤
              (ℓf k : ℝ) ^ ℓf k * (1 / (p : ℝ)) ^ (r * ℓf k) := by
            have hs := (hsY k).1
            have hs01 : s₀ ≤ 1 := (hsY k).1.trans (hsY k).2
            have hss : s₀ ^ 2 ≤ s₀ := by
              rw [sq]; exact mul_le_of_le_one_left hs₀pos.le hs01
            have h1 : 12 * (ℓf k : ℝ) ^ 2 ≤ 24 * (L : ℝ) ^ 2 * (r * L + 1) := by
              have : (ℓf k : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ hℓ0.le hℓ 2
              have : (0 : ℝ) ≤ (L : ℝ) ^ 2 * (r * L) := by positivity
              have : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
              linarith
            rw [← hDη]
            have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hDη0.le hY0)
            linarith
          have hggk : 24 * (ℓf k : ℝ) ^ 2 * Y₀ ≤ gg := by
            rw [hY₀, hgg]
            have := F.h14
            have hl2 : (ℓf k : ℝ) ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ hℓ0.le hℓ 2
            have hDe : 0 < Δ ^ ε := Real.rpow_pos_of_pos hD0 _
            have := mul_le_mul_of_nonneg_right hl2 hDe.le
            have : 0 ≤ (L : ℝ) ^ 2 * Δ ^ ε := by positivity
            linarith
          exact pib2_term (ℓf k) L (hℓ1 k) (hℓL k) hp1 (by exact_mod_cast hq0) hpD hq_le
            (hKpos k hk) (Real.rpow_pos_of_pos hD0 _) hsk hggk
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  set m : ℝ := Δ / (q * P) with hmdef
  have hqP0 : 0 < (q : ℝ) * P := by positivity
  have hm_ge : Δ ^ a / 2 ≤ m := by
    have hDY : Δ / Y = Δ ^ a := by
      rw [hY, div_eq_iff (Real.rpow_pos_of_pos hD0 _).ne', ← Real.rpow_add hD0]
      simp
    rw [hmdef, ← hDY, div_div]
    exact div_le_div_of_nonneg_left hD0.le (by positivity) (by linarith)
  set D₁ : ℝ := (1 + ξ) * Δ / P with hD₁
  set t₃ : ℝ := ξ * Δ / (q * P) with ht₃
  set t₄ : ℝ := Δ ^ ε / 2 with ht₄
  have ht₃0 : 0 < t₃ := by positivity
  have ht₄0 : 0 < t₄ := by have := Real.rpow_pos_of_pos hD0 ε; positivity
  have hD₁q : D₁ / q = (1 + ξ) * m := by
    rw [hD₁, hmdef]; field_simp
  have ht₃m : t₃ = ξ * m := by rw [ht₃, hmdef]; ring
  have hCq : C / q ≤ t₄ := by
    have h1 : C / q ≤ C * P / Y := by
      rw [div_le_div_iff₀ hqR (by linarith)]
      have := mul_le_mul_of_nonneg_left hqP_ge hC0.le
      linarith
    have h2 : C * P / Y = P * Δ ^ (a - δ) := by
      rw [hC, hY, mul_comm, mul_div_assoc, ← Real.rpow_sub hD0]; ring_nf
    have h3 : P * Δ ^ (a - δ) ≤ Xb ^ (r - 1) * Δ ^ (a - δ) :=
      mul_le_mul_of_nonneg_right hPX (Real.rpow_pos_of_pos hD0 _).le
    have h4 := F.h3
    rw [ht₄]
    rw [← hXb] at h4
    linarith
  have hCq0 : 0 ≤ C / q := by positivity
  have hE3 : Y₀ ≤ t₃ ^ 2 / (2 * (1 * D₁ / q + 1 * t₃)) := by
    have := e3_bound hD1 hξ hξ1 hm_ge ha5
    rw [mul_div_assoc, hD₁q, ht₃m]; exact this
  have hE4 : Y₀ ≤ t₄ ^ 2 / (2 * (1 * C / q + 1 * t₄)) := by
    have := e4_bound hD0 ht₄ hCq0 hCq
    rw [mul_div_assoc]; exact this
  obtain ⟨fc, hfdeg, hfcod, -, hfbad⟩ := edge_partition_ext (K := (∅ : Finset Unit)) hq0 H A
    (fun i => part_subset H τ i) D₁ C t₃ t₄ ht₃0 ht₄0 (fun i x => hτdeg x i)
    (fun i x y hxy => le_trans (by exact_mod_cast codegree_mono (part_subset H τ i) x y)
      (hcod x y hxy))
    (fun _ _ => (0 : ℝ)) 1 1 1 one_pos zero_le_one one_pos (by simp) (by simp) (by simp)
    (by simp) _ πB2 hbad2 (by
      refine lt_of_le_of_lt ?_ hunion
      simp only [card_empty, Nat.cast_zero, zero_mul, add_zero]
      have e3 := hexpY _ hE3
      have e4 := hexpY _ hE4
      have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
      have hA3 : ((H.biUnion id).card * p * q : ℝ) *
          Real.exp (-(t₃ ^ 2 / (2 * (1 * D₁ / q + 1 * t₃)))) ≤
          (r * Real.exp X₀ * (2 * Δ) * (2 * Δ)) * Real.exp (-Y₀) :=
        mul_le_mul (mul_le_mul (mul_le_mul hUcard hpD (by positivity) (by positivity)) hq_le
          (by positivity) (by positivity)) e3 (by positivity) (by positivity)
      have hA4 : ((H.biUnion id).card ^ 2 * p * q : ℝ) *
          Real.exp (-(t₄ ^ 2 / (2 * (1 * C / q + 1 * t₄)))) ≤
          ((r * Real.exp X₀) ^ 2 * (2 * Δ) * (2 * Δ)) * Real.exp (-Y₀) :=
        mul_le_mul (mul_le_mul (mul_le_mul (pow_le_pow_left₀ hU0 hUcard 2) hpD (by positivity)
          (by positivity)) hq_le (by positivity) (by positivity)) e4 (by positivity)
          (by positivity)
      have hB : πB2 ≤ L * Real.exp X₀ * ((4 * Δ ^ 2) ^ L * ((L : ℝ) ^ L * (2 ^ L + 1))) *
          Real.exp (-Y₀) := hπB2le.trans (by gcongr)
      have hc3 : (L : ℝ) * 4 ^ L * (L : ℝ) ^ L * (2 ^ L + 1) ≤ Z8 := by
        have h1 : (4 : ℝ) ^ L * (2 ^ L + 1) ≤ 2 * 8 ^ L := by
          have : (4 : ℝ) ^ L * 2 ^ L = 8 ^ L := by rw [← mul_pow]; norm_num
          have : (4 : ℝ) ^ L ≤ 8 ^ L := pow_le_pow_left₀ (by norm_num) (by norm_num) L
          linarith
        have : (0 : ℝ) ≤ L * (L : ℝ) ^ L := by positivity
        calc (L : ℝ) * 4 ^ L * (L : ℝ) ^ L * (2 ^ L + 1) =
            (L * (L : ℝ) ^ L) * (4 ^ L * (2 ^ L + 1)) := by ring
          _ ≤ (L * (L : ℝ) ^ L) * (2 * 8 ^ L) := by gcongr
          _ = 2 * L * 8 ^ L * (L : ℝ) ^ L := by ring
          _ ≤ Z8 := hZ8L
      have hsum : (r * Real.exp X₀ * (2 * Δ) * (2 * Δ)) * Real.exp (-Y₀) +
          ((r * Real.exp X₀) ^ 2 * (2 * Δ) * (2 * Δ)) * Real.exp (-Y₀) +
          L * Real.exp X₀ * ((4 * Δ ^ 2) ^ L * ((L : ℝ) ^ L * (2 ^ L + 1))) * Real.exp (-Y₀) ≤
          (G + G + G) * Real.exp (-Y₀) := by
        have e : (r * Real.exp X₀ * (2 * Δ) * (2 * Δ)) * Real.exp (-Y₀) +
            ((r * Real.exp X₀) ^ 2 * (2 * Δ) * (2 * Δ)) * Real.exp (-Y₀) +
            L * Real.exp X₀ * ((4 * Δ ^ 2) ^ L * ((L : ℝ) ^ L * (2 ^ L + 1))) * Real.exp (-Y₀) =
            (4 * (r : ℝ) ^ 1 * Δ ^ 2 * Real.exp X₀ +
              4 * (r : ℝ) ^ 2 * Δ ^ 2 * (Real.exp X₀ * Real.exp X₀) +
              (L * 4 ^ L * (L : ℝ) ^ L * (2 ^ L + 1)) * (r : ℝ) ^ 0 * Δ ^ (2 * L) *
                Real.exp X₀) * Real.exp (-Y₀) := by
          simp only [mul_pow, ← pow_mul]; ring
        rw [e]
        gcongr
        · exact hterm 4 (by norm_num) hZ4 2 (by omega) 1 (by omega)
        · rw [hG]
          have : Δ ^ 2 ≤ Δ ^ (2 * L + 2) := pow_le_pow_right₀ hD1 (by omega)
          calc 4 * (r : ℝ) ^ 2 * Δ ^ 2 * (Real.exp X₀ * Real.exp X₀) =
              (r : ℝ) ^ 2 * 4 * Δ ^ 2 * (Real.exp X₀ * Real.exp X₀) := by ring
            _ ≤ _ := by gcongr
        · exact hterm _ (by positivity) hc3 (2 * L) (by omega) 0 (by omega)
      have hGe : 0 ≤ G * Real.exp (-Y₀) := mul_nonneg hG0 hY₀pos.le
      linarith)
  simp only [not_exists, not_and, not_not] at hfbad
  -- Step 3
  have hKc : 2 * Kall.card * Real.exp (-(Δ ^ ε / 64)) < 1 := by
    have hLZ : (L : ℝ) ≤ Z8 := by
      have h2L : (1 : ℝ) ≤ 2 * 2 ^ L := by
        have : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
        linarith
      have : (L : ℝ) * 1 ≤ L * (2 * 2 ^ L) := mul_le_mul_of_nonneg_left h2L (by positivity)
      linarith
    have h1 := hterm L (by positivity) hLZ 0 (by omega) 0 (by omega)
    simp only [pow_zero, mul_one] at h1
    have h2 : (Kall.card : ℝ) ≤ G := hKcard.trans h1
    rw [← hY₀]
    have h3 := mul_le_mul_of_nonneg_right h2 hY₀pos.le
    have hGe : 0 ≤ G * Real.exp (-Y₀) := mul_nonneg hG0 hY₀pos.le
    linarith
  have hfdeg' : ∀ i j x, (degree (cls (part H τ) fc i j) x : ℝ) ≤
      (1 + 2 * Δ ^ (-(2 * ε))) * (Δ / (q * (p : ℝ) ^ (r - 1))) := by
    intro i j x
    have := hfdeg i j x
    rw [hD₁q, ht₃m] at this
    rw [← hξ, ← hPdef, ← hmdef]
    linarith
  have hfcod' : ∀ i j x y, x ≠ y → (codegree (cls (part H τ) fc i j) x y : ℝ) ≤ Δ ^ ε := by
    intro i j x y hxy
    have := hfcod i j x y hxy
    rw [ht₄] at this hCq
    linarith
  obtain ⟨M, hMH, hMm, hMK⟩ := core13_step3 r L hr hL δ ε a b ρ κ σ D₀ hε ha0 hb hρ hκ hσ hnib
    Δ F V H huni hcard p q hp0 hq0 hp_ge hqP_ge hqP_le τ fc hfdeg' hfcod' Kall hKc ℓf Wf
    (fun k _ => hℓ1 k) (fun k _ => hℓL k) (fun k _ => hWf0 k) hKpos
    (fun k hk => (hτbad k hk).1) (fun k hk v => hfbad k hk v)
  refine ⟨M, hMH, hMm, ?_⟩
  intro ℓ hℓ1' hℓL' k hnorm
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
  set kk : (Σ j : Fin L, ι ((j : ℕ) + 1)) := ⟨⟨n, by omega⟩, k⟩ with hkk
  have htw0 : 0 ≤ tweight (n + 1) (W (n + 1) k) H :=
    sum_nonneg fun S hS => hW0 _ hℓ1' hℓL' k S hS
  rcases htw0.lt_or_eq with hpos | hzero
  · have hk : kk ∈ Kall := by
      simp only [hKall, mem_filter, mem_univ, true_and]
      exact ⟨hnorm, hpos⟩
    exact hMK kk hk
  · have hMle : tweight (n + 1) (W (n + 1) k) M ≤ tweight (n + 1) (W (n + 1) k) H :=
      sum_le_sum_of_subset_of_nonneg (powersetCard_mono hMH)
        fun S hS _ => hW0 _ hℓ1' hℓL' k S hS
    have hM0 : 0 ≤ tweight (n + 1) (W (n + 1) k) M :=
      sum_nonneg fun S hS => hW0 _ hℓ1' hℓL' k S (powersetCard_mono hMH hS)
    have hM : tweight (n + 1) (W (n + 1) k) M = 0 := by linarith
    rw [hM, ← hzero]
    simp

end Pseudorandom
