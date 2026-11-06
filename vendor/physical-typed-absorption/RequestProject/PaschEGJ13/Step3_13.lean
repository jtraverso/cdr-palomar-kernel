/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.Numerics13b
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Step 3 of the proof of Theorem 1.3 for a fixed `Δ`

Given the vertex partition `τ` (Step 1) and the edge colouring `fc` (Step 2) with the required
properties, we choose random matchings in all classes and show that the union satisfies the
conclusion of Theorem 1.3 for all weight functions in `K`. -/

@[expose] public section

namespace Pseudorandom

open Finset

set_option maxHeartbeats 4000000 in
/-- Step 3 of the proof of Theorem 1.3 for a fixed `Δ`. -/
theorem core13_step3 (r L : ℕ) (hr : 2 ≤ r) (hL : 1 ≤ L) (δ ε a b ρ κ σ D₀ : ℝ) (hε : 0 < ε)
    (ha0 : 0 < a) (hb : b = 2 * L * a + 4 * ε) (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hσ : 0 ≤ σ)
    (hnib : ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (H : Finset (Finset V)), IsUniform H r → (∀ v, (degree H v : ℝ) ≤ D) →
      (∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ D ^ κ) → (H.card : ℝ) ≤ Real.exp (D ^ σ) →
      ∃ μ : Finset (Finset V) → ℝ, (∀ M, 0 ≤ μ M) ∧ ∑ M, μ M = 1 ∧
        (∀ M, μ M ≠ 0 → IsMatching M ∧ M ⊆ H) ∧
        ∀ e ∈ H, (1 - D ^ (-ρ)) / D ≤ ∑ M, μ M * (if e ∈ M then 1 else 0))
    (Δ : ℝ) (F : Facts13 r L δ ε a b ρ κ σ D₀ Δ)
    (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (huni : IsUniform H r)
    (hcard : (H.card : ℝ) ≤ Real.exp (Δ ^ (ε ^ 2)))
    (p q : ℕ) (hp0 : 0 < p) (hq0 : 0 < q) (hp_ge : Δ ^ b ≤ p)
    (hqP_ge : Δ ^ (1 - a) ≤ q * (p : ℝ) ^ (r - 1))
    (hqP_le : q * (p : ℝ) ^ (r - 1) ≤ 2 * Δ ^ (1 - a))
    (τ : V → Fin p) (fc : Finset V → Fin q)
    (hfdeg : ∀ i j x, (degree (cls (part H τ) fc i j) x : ℝ) ≤
      (1 + 2 * Δ ^ (-(2 * ε))) * (Δ / (q * (p : ℝ) ^ (r - 1))))
    (hfcod : ∀ i j x y, x ≠ y → (codegree (cls (part H τ) fc i j) x y : ℝ) ≤ Δ ^ ε)
    {κ' : Type} (K : Finset κ') (hKcard : 2 * K.card * Real.exp (-(Δ ^ ε / 64)) < 1)
    (ℓf : κ' → ℕ) (Wf : κ' → Finset (Finset V) → ℝ) (hℓ1 : ∀ k ∈ K, 1 ≤ ℓf k)
    (hℓL : ∀ k ∈ K, ℓf k ≤ L)
    (hWf0 : ∀ k ∈ K, ∀ S ∈ H.powersetCard (ℓf k), 0 ≤ Wf k S)
    (hKpos : ∀ k ∈ K, 0 < tweight (ℓf k) (Wf k) H)
    (hdS : ∀ k ∈ K, |dSum (ℓf k) H (Wf k) τ - tweight (ℓf k) (Wf k) H *
        (p.descFactorial (ℓf k) * (1 / (p : ℝ)) ^ (r * ℓf k))| ≤
      Δ ^ (-(2 * ε)) * (tweight (ℓf k) (Wf k) H *
        (p.descFactorial (ℓf k) * (1 / (p : ℝ)) ^ (r * ℓf k))))
    (hzS : ∀ k ∈ K, ∀ v : Fin (ℓf k) → Fin p × Fin q, zSum H (Wf k) (part H τ) v fc ≤
      2 * (ℓf k : ℝ) ^ ℓf k * (2 * ((ℓf k : ℝ) ^ ℓf k * (1 / (p : ℝ)) ^ (r * ℓf k)) *
        tweight (ℓf k) (Wf k) H * (1 / (q : ℝ)) ^ ℓf k)) :
    ∃ M ⊆ H, IsMatching M ∧ ∀ k ∈ K,
      |tweight (ℓf k) (Wf k) M - tweight (ℓf k) (Wf k) H / Δ ^ ℓf k| ≤
        Δ ^ (-ε) * (tweight (ℓf k) (Wf k) H / Δ ^ ℓf k) := by
  classical
  have hD2 := F.h1
  have hD0 : 0 < Δ := by linarith
  have hD1 : 1 ≤ Δ := by linarith
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = Δ ^ (-(2 * ε)) := ⟨_, rfl⟩
  rw [← hξ] at hfdeg hdS
  have hξ0 : 0 < ξ := by rw [hξ]; exact Real.rpow_pos_of_pos hD0 _
  have hξ1 : ξ ≤ 1 / 2 := hξ ▸ F.h4
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (p : ℝ) ^ (r - 1) := ⟨_, rfl⟩
  rw [← hP] at hqP_ge hqP_le hfdeg
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp0
  have hP1 : 1 ≤ P := hP ▸ one_le_pow₀ hp1
  have hP0 : 0 < P := by linarith
  have hpr : (p : ℝ) ^ r = p * P := by rw [hP, ← pow_succ']; congr 1; omega
  have hQ0 : 0 < (q : ℝ) * P := by positivity
  have hY0 : 0 < Δ ^ (1 - a) := Real.rpow_pos_of_pos hD0 _
  -- the classes
  set A : Fin p → Finset (Finset V) := part H τ with hAdef
  have hne : ∀ i, ∀ e ∈ A i, e.Nonempty := fun i e he => by
    rw [← card_pos, huni e (part_subset H τ i he)]; omega
  have hBH : ∀ i j, cls A fc i j ⊆ H := fun i j => (cls_subset A fc i j).trans (part_subset H τ i)
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = Δ / (q * P) := ⟨_, rfl⟩
  rw [← hm] at hfdeg
  have hm0 : 0 < m := by rw [hm]; positivity
  have hm_ge : Δ ^ a / 2 ≤ m := by
    have hDY : Δ / Δ ^ (1 - a) = Δ ^ a := by
      rw [div_eq_iff hY0.ne', ← Real.rpow_add hD0]; simp
    rw [hm, ← hDY, div_div]
    exact div_le_div_of_nonneg_left hD0.le (by positivity) (by linarith)
  obtain ⟨Dt, hDt⟩ : ∃ Dt : ℝ, Dt = (1 + 2 * ξ) * m := ⟨_, rfl⟩
  rw [← hDt] at hfdeg
  have hDt_ge : Δ ^ a / 2 ≤ Dt := by rw [hDt]; nlinarith
  have hDtm : m ≤ Dt := by rw [hDt]; nlinarith
  have hDt1 : 1 ≤ Dt := F.h11.trans hDt_ge
  have hDt0 : 0 < Dt := by linarith
  obtain ⟨νr, hνr⟩ : ∃ νr : ℝ, νr = Dt ^ (-ρ) := ⟨_, rfl⟩
  have hνr0 : 0 ≤ νr := hνr ▸ (Real.rpow_pos_of_pos hDt0 _).le
  have hνr_le : νr ≤ (Δ ^ a / 2) ^ (-ρ) :=
    hνr ▸ Real.rpow_le_rpow_of_nonpos (by linarith [F.h11]) hDt_ge (by linarith)
  have hνr1 : νr ≤ 1 := hνr ▸ Real.rpow_le_one_of_one_le_of_nonpos hDt1 (by linarith)
  have heps1 : Δ ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hD1 (by linarith)
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hbpos : 0 < Δ ^ (-b) := Real.rpow_pos_of_pos hD0 _
  have hνr2 : νr ≤ 1 / 2 := by
    have h10 := F.h10
    rw [← hξ] at h10
    have : (Δ ^ a / 2) ^ (-ρ) ≤ L * (Δ ^ a / 2) ^ (-ρ) :=
      le_mul_of_one_le_left (Real.rpow_nonneg (by linarith [F.h11]) _) hLR
    nlinarith [sq_nonneg (L : ℝ)]
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ = (1 - νr) / Dt := ⟨_, rfl⟩
  have hx₀0 : 0 ≤ x₀ := hx₀ ▸ div_nonneg (by linarith) hDt0.le
  have hdist : ∀ i j, ∃ ν : Finset (Finset V) → ℝ, (∀ N, 0 ≤ ν N) ∧ ∑ N, ν N = 1 ∧
      (∀ N, ν N ≠ 0 → IsMatching N ∧ N ⊆ cls A fc i j) ∧ ∀ e ∈ cls A fc i j, marg ν e = x₀ := by
    intro i j
    have hcodB : ∀ u w, u ≠ w → (codegree (cls A fc i j) u w : ℝ) ≤ Dt ^ κ := by
      intro u w huw
      have h2 : Δ ^ ε ≤ Dt ^ κ :=
        F.h8.trans (Real.rpow_le_rpow (by linarith [F.h11]) hDt_ge hκ)
      exact (hfcod i j u w huw).trans h2
    have hcardB : ((cls A fc i j).card : ℝ) ≤ Real.exp (Dt ^ σ) := by
      have h1 : ((cls A fc i j).card : ℝ) ≤ H.card := by exact_mod_cast card_le_card (hBH i j)
      have h2 : Δ ^ (ε ^ 2) ≤ Dt ^ σ :=
        F.h9.trans (Real.rpow_le_rpow (by linarith [F.h11]) hDt_ge hσ)
      exact h1.trans (hcard.trans (Real.exp_le_exp.mpr h2))
    obtain ⟨μ, hμ0, hμ1, hμsupp, hμmarg⟩ := hnib Dt (F.h7.trans hDt_ge) V (cls A fc i j)
      (fun e he => huni e (hBH i j he)) (fun v => hfdeg i j v) hcodB hcardB
    obtain ⟨ν, hν0, hν1, hνsupp, hνmarg⟩ := thinning (cls A fc i j) μ hμ0 hμ1 x₀ hx₀0
      (fun e he => by rw [hx₀, hνr]; exact hμmarg e he)
    refine ⟨ν, hν0, hν1, fun N hN => ?_, hνmarg⟩
    obtain ⟨M, hM, hNM, hNB⟩ := hνsupp N hN
    have hMm := (hμsupp M hM).1
    exact ⟨fun e he g hg heg => hMm e (hNM he) g (hNM hg) heg, hNB⟩
  choose ν hν0 hν1 hνsupp hνmarg using hdist
  have hdisj : ∀ i i', i ≠ i' → ∀ e ∈ A i, ∀ g ∈ A i', Disjoint e g := by
    intro i i' hii e he g hg
    have he' : ∀ v ∈ e, τ v = i := (mem_filter.mp he).2
    have hg' : ∀ v ∈ g, τ v = i' := (mem_filter.mp hg).2
    rw [Finset.disjoint_left]
    intro v hve hvg
    exact hii ((he' v hve).symm.trans (hg' v hvg))
  -- the constants
  set Bk : κ' → ℝ := fun k => 2 * (ℓf k : ℝ) ^ ℓf k * (2 * ((ℓf k : ℝ) ^ ℓf k *
    (1 / (p : ℝ)) ^ (r * ℓf k)) * tweight (ℓf k) (Wf k) H * (1 / (q : ℝ)) ^ ℓf k) with hBk
  set c : κ' → ℝ := fun k => (ℓf k : ℝ) * (p : ℝ) ^ (ℓf k - 1) * Bk k with hc
  set t : κ' → ℝ := fun k => Δ ^ (-ε) * (tweight (ℓf k) (Wf k) H / Δ ^ ℓf k) / 2 with ht
  have hBk0 : ∀ k ∈ K, 0 < Bk k := fun k hk => by
    have := hKpos k hk
    have : (0 : ℝ) < ℓf k := by exact_mod_cast hℓ1 k hk
    simp only [hBk]; positivity
  have hc0 : ∀ k ∈ K, 0 < c k := fun k hk => by
    have := hBk0 k hk
    have : (0 : ℝ) < ℓf k := by exact_mod_cast hℓ1 k hk
    simp only [hc]; positivity
  have ht0 : ∀ k ∈ K, 0 < t k := fun k hk => by
    have := hKpos k hk
    have := Real.rpow_pos_of_pos hD0 (-ε)
    simp only [ht]; positivity
  have hE : ∀ k ∈ K, Δ ^ ε / 64 ≤ t k ^ 2 / (2 * (p * c k ^ 2 + c k * t k)) := by
    intro k hk
    have htw := hKpos k hk
    refine step3_expo (ℓf k) L (hℓ1 k hk) (hℓL k hk) hD1 hε ha0.le hb hp_ge
      (by positivity) (hc0 k hk) ?_ rfl F.h17
    have e1 : c k = 4 * (ℓf k : ℝ) ^ (2 * ℓf k + 1) * tweight (ℓf k) (Wf k) H /
        (p * (q * P) ^ ℓf k) := c13_eq (ℓf k) r (hℓ1 k hk) hpR hqR hpr hP0
    rw [e1]
    exact c13_le (ℓf k) hpR hqR hP0 hqP_ge hD0 htw.le _ (by positivity)
  obtain ⟨M, hMH, hMm, hMw⟩ := random_matching_tuple hq0 H (fun i => part_subset H τ i) hne
    hdisj ν hν0 hν1 hνsupp x₀ hνmarg K ℓf Wf hWf0 c t hc0 ht0
    (fun k hk i σ' => gamma_le_of_zSum H (Wf k) (hWf0 k hk) A fc hne hdisj (Bk k)
      (hBk0 k hk).le (hzS k hk) i σ') (by
      calc ∑ k ∈ K, 2 * Real.exp (-(t k ^ 2 / (2 * (p * c k ^ 2 + c k * t k))))
          ≤ ∑ _k ∈ K, 2 * Real.exp (-(Δ ^ ε / 64)) :=
            sum_le_sum fun k hk => by
              have := Real.exp_le_exp.mpr (neg_le_neg (hE k hk)); linarith
        _ = 2 * K.card * Real.exp (-(Δ ^ ε / 64)) := by rw [sum_const, nsmul_eq_mul]; ring
        _ < 1 := hKcard)
  refine ⟨M, hMH, hMm, fun k hk => ?_⟩
  obtain ⟨hlo, hup⟩ := hMw k hk
  have htw := hKpos k hk
  have hℓ1k := hℓ1 k hk
  have hℓLk := hℓL k hk
  have hℓR : (ℓf k : ℝ) ≤ L := by exact_mod_cast hℓLk
  have hℓp : ℓf k ≤ p := by
    have h2 : (L : ℝ) ≤ 2 * (L : ℝ) ^ 2 := by nlinarith
    have : (ℓf k : ℝ) ≤ p := by linarith [F.h16]
    exact_mod_cast this
  obtain ⟨hF1, hF2⟩ := main_factor_bounds (ℓf k) p hp0 hℓp hνr0 hνr1 hξ0.le
  have hSDeq : dSum (ℓf k) H (Wf k) τ = ∑ S ∈ H.powersetCard (ℓf k),
      Wf k S * if DistinctParts A S then 1 else 0 := by
    unfold dSum; rfl
  have hDtq : (q : ℝ) * Dt = (1 + 2 * ξ) * Δ / P := by
    rw [hDt, hm]; field_simp
  have hmA := main13 (ℓf k) r hpR hqR hP0 hD0 hpr hDtq hξ0.le (ν := νr)
    (tw := tweight (ℓf k) (Wf k) H) (d := (p.descFactorial (ℓf k) : ℝ))
  rw [← hx₀] at hmA
  -- the error term
  have hErr := err_le_of_zSum H (Wf k) (hWf0 k hk) A fc hne hdisj (Bk k) (hzS k hk) (x₀ / q)
    (by positivity)
  have hS := sum_range_lt_le (Y := Fin p × Fin q) (ℓf k) (x₀ / q) (by positivity)
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hS
  have hErr' := hErr.trans (mul_le_mul_of_nonneg_left hS (hBk0 k hk).le)
  have hxle : x₀ ≤ q * P / Δ := by
    rw [hx₀]
    calc (1 - νr) / Dt ≤ 1 / m := by
          rw [div_le_div_iff₀ hDt0 hm0]; nlinarith
      _ = q * P / Δ := by rw [hm]; field_simp
  have hX : 1 ≤ x₀ * p := xp13 hD0 hνr2 hξ0.le hξ1 hQ0 (by rw [hx₀, hDt, hm])
    hqP_ge hp_ge F.h19
  have hErrb := err13 (ℓf k) L r hℓ1k hℓLk hD1 hp_ge hqR hP0 hpr hqP_ge hx₀0 hxle hX htw.le
    hErr' F.h18
  refine final_estimate13 (by positivity) (by positivity) (by positivity) hξ0.le (by linarith)
    (f := ℓf k * νr + 2 * ℓf k * ξ + (ℓf k : ℝ) ^ 2 / p) (by positivity)
    (hSDeq ▸ hdS k hk) hmA hF2 hF1 hlo hup rfl hErrb (by rw [hξ]; linarith [F.h20]) ?_
  have h10 := F.h10
  rw [← hξ] at h10
  have hpb : (ℓf k : ℝ) ^ 2 / p ≤ (L : ℝ) ^ 2 * Δ ^ (-b) := by
    rw [Real.rpow_neg hD0.le, ← div_eq_mul_inv]
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) hℓR 2)
      (Real.rpow_pos_of_pos hD0 _) hp_ge
  have h1 : (ℓf k : ℝ) * νr ≤ L * (Δ ^ a / 2) ^ (-ρ) :=
    mul_le_mul hℓR hνr_le hνr0 (by positivity)
  have h2 : 2 * (ℓf k : ℝ) * ξ ≤ 2 * L * ξ := by nlinarith
  linarith

end Pseudorandom
