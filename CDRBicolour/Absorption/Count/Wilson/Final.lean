/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Count.Wilson.CoreBound

/-!
# The optimal counting constant `1/6` (backlog item 4)

**`realCount_lower_sharp`**: for every `ε > 0` and every sufficiently large admissible profile,

    (1/6 − ε) · n² · log n ≤ log realCount(a, b, c).

With `realCount_upper` (Linial–Luria) this gives `log realCount(a, b, c) = (1/6 + o(1)) n² log n`:
the constant `1/6` is optimal (`realCount_log_asymptotic`).  No Keevash-type theorem is used: the
construction is Wilson's (groups balanced in the three classes, a Steiner triple system on the
groups, free Latin squares between groups with the class pattern `τ`), completed by Theorem T on
the residual host (`wilson_core`).

The choice of parameters: `η = min(ε, 1/2)`, `g = 6(⌈3/η⌉ + 3) + 3` groups (`g ≡ 3 mod 6`,
`g ≥ 3/η`), `K = 2g + 1`, `t = ⌊2 min(a,b,c)/K⌋ ≥ (2/3)(n/K)(1 − η/2)`, and
`(3/2) g (g−1) t² ≥ (1/6)(1 − η)² n²` because `(1 − η) K² ≤ 4 g (g − 1)`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.Absorption.Count.Wilson

open Finset TypedTriangle CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.Absorption.Count

theorem sqrt_le_mul {n q : ℝ} (hq : 0 < q) (hn : 2 / q ^ 2 ≤ n) :
    Real.sqrt (2 * n) ≤ q * n := by
  have hq2 : 0 < q ^ 2 := by positivity
  have h2 : 2 ≤ n * q ^ 2 := (div_le_iff₀ hq2).1 hn
  have hn0 : 0 ≤ n := le_trans (by positivity) hn
  have hqn : 0 ≤ q * n := mul_nonneg hq.le hn0
  calc Real.sqrt (2 * n) ≤ Real.sqrt ((q * n) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left h2 hn0])
    _ = q * n := Real.sqrt_sq hqn

/-- The smallest class of an admissible profile is at least `(n − 2√(2n))/3`. -/
theorem min_ge {a b c : ℕ} (h : AdmissibleProfile a b c) :
    (((a + b + c : ℕ) : ℝ) - 2 * Real.sqrt (2 * ((a + b + c : ℕ) : ℝ))) / 3 ≤
      ((min a (min b c) : ℕ) : ℝ) := by
  have h0' : (a : ℝ) ≤ ((min a (min b c) : ℕ) : ℝ) + Real.sqrt (2 * ((a + b + c : ℕ) : ℝ)) := by
    have := csize_le_min_add h 0
    simpa [csize] using this
  have h1' : (b : ℝ) ≤ ((min a (min b c) : ℕ) : ℝ) + Real.sqrt (2 * ((a + b + c : ℕ) : ℝ)) := by
    have := csize_le_min_add h 1
    simpa [csize] using this
  have h2' : (c : ℝ) ≤ ((min a (min b c) : ℕ) : ℝ) + Real.sqrt (2 * ((a + b + c : ℕ) : ℝ)) := by
    have := csize_le_min_add h 2
    simpa [csize] using this
  have hn : ((a + b + c : ℕ) : ℝ) = a + b + c := by push_cast; ring
  have hm3 : min a (min b c) = a ∨ min a (min b c) = b ∨ min a (min b c) = c := by omega
  rcases hm3 with e | e | e <;> rw [e] at h0' h1' h2' ⊢ <;> linarith

/-- The final real inequality. -/
theorem final_ineq {ε η g u n t L : ℝ} (hη0 : 0 < η) (hηε : η ≤ ε) (hη2 : η ≤ 1 / 2)
    (hg : 3 / η ≤ g) (hg1 : 1 ≤ g) (hn : n = (2 * g + 1) * u) (hu : 0 ≤ u)
    (ht : 2 / 3 * u * (1 - η / 2) ≤ t) (hL : 0 ≤ L) (hlog : (1 - η) * L ≤ Real.log t - 2) :
    (1 / 6 - ε) * n ^ 2 * L ≤ 3 / 2 * g * (g - 1) * t ^ 2 * (Real.log t - 2) := by
  have hηg : 3 ≤ g * η := (div_le_iff₀ hη0).1 hg
  have hgr : (1 - η) * (2 * g + 1) ^ 2 ≤ 4 * g * (g - 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hηg (by linarith : (0 : ℝ) ≤ 4 * g),
      mul_nonneg hη0.le (by linarith : (0 : ℝ) ≤ g)]
  have h1η : 0 ≤ 1 - η := by linarith
  have hA : 0 ≤ 3 / 2 * g * (g - 1) := by nlinarith
  have h0 : 0 ≤ 2 / 3 * u * (1 - η / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hu) (by linarith)
  have h2 : (2 / 3 * u * (1 - η / 2)) * (2 / 3 * u * (1 - η / 2)) ≤ t * t :=
    mul_le_mul ht ht h0 (h0.trans ht)
  have hT : 4 / 9 * (1 - η) * u ^ 2 ≤ t ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg η)]
  calc (1 / 6 - ε) * n ^ 2 * L ≤ 1 / 6 * (1 - η) ^ 3 * n ^ 2 * L := by
        apply mul_le_mul_of_nonneg_right _ hL
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg n)
        nlinarith [mul_nonneg (sq_nonneg η) (by linarith : (0 : ℝ) ≤ 3 - η)]
    _ = (1 / 6 * (1 - η) ^ 2 * n ^ 2) * ((1 - η) * L) := by ring
    _ ≤ (3 / 2 * g * (g - 1) * (4 / 9 * (1 - η) * u ^ 2)) * ((1 - η) * L) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg h1η hL)
        rw [hn]
        nlinarith [mul_le_mul_of_nonneg_left hgr
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6) h1η) (sq_nonneg u))]
    _ ≤ (3 / 2 * g * (g - 1) * t ^ 2) * (Real.log t - 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hT hA) hlog (mul_nonneg h1η hL)
          (mul_nonneg hA (sq_nonneg t))
    _ = 3 / 2 * g * (g - 1) * t ^ 2 * (Real.log t - 2) := by ring

set_option maxHeartbeats 800000 in
/-- **The optimal constant (lower bound).** For every `ε > 0`, every sufficiently large admissible
profile has `log realCount(a, b, c) ≥ (1/6 − ε) n² log n`. -/
theorem realCount_lower_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
      (1 / 6 - ε) * ((a + b + c : ℕ) : ℝ) ^ 2 * Real.log (a + b + c : ℕ) ≤
        Real.log (realCount a b c) := by
  obtain ⟨η, hη0, hηε, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ η ≤ 1 / 2 :=
    ⟨min ε (1 / 2), lt_min hε (by norm_num), min_le_left _ _, min_le_right _ _⟩
  -- the number of groups
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ, g = 6 * (⌈3 / η⌉₊ + 3) + 3 := ⟨_, rfl⟩
  have hg15 : 15 ≤ g := by omega
  have hg1 : 1 ≤ g := by omega
  have hga : _root_.STS.Admissible g := by unfold _root_.STS.Admissible; omega
  have hgη : 3 / η ≤ (g : ℝ) := by
    have h1 : 3 / η ≤ (⌈3 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈3 / η⌉₊ : ℝ) ≤ (g : ℝ) := by exact_mod_cast (show ⌈3 / η⌉₊ ≤ g by omega)
    linarith
  have hgR : (15 : ℝ) ≤ g := by exact_mod_cast hg15
  have hg0 : (0 : ℝ) < g := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * g + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; linarith
  have hK31 : 31 ≤ K := by rw [hK]; linarith
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 2 + Real.log 2 + Real.log K := ⟨_, rfl⟩
  -- Theorem T
  have hαpos : 0 < alphaG g := by
    unfold alphaG
    have : 0 < Mg g ^ 2 := pow_pos (by unfold Mg; omega) 2
    exact one_div_pos.mpr (by exact_mod_cast this)
  have hC1 : 1 ≤ CG g := by
    unfold CG
    have : (0 : ℝ) ≤ 6 * g * (2 * g + 1) := by positivity
    linarith
  obtain ⟨nT, hT⟩ := Vortex.main_theorem_T cdrF (alphaG g) (CG g) 6 hαpos hC1 le_rfl
  -- the threshold
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 6 / η * K + 1024 * K + (8 * (g : ℝ) + 16) * K +
      3328000 * (g : ℝ) * K + 2 / (η / (8 * K)) ^ 2 + 2 / (1 / (416000 * (g : ℝ) * K)) ^ 2 +
      Real.exp (c₀ / η) := ⟨_, rfl⟩
  refine ⟨max nT (max 400 ⌈R⌉₊), fun a b c hadm hn => ?_⟩
  have hnT : nT ≤ a + b + c := le_of_max_le_left hn
  have hn400 : 400 ≤ a + b + c := le_trans (le_max_left _ _) (le_of_max_le_right hn)
  have hceil : ⌈R⌉₊ ≤ a + b + c := le_trans (le_max_right _ _) (le_of_max_le_right hn)
  obtain ⟨n, hn_def⟩ : ∃ n : ℝ, n = ((a + b + c : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hn_def]
  have hnR : R ≤ n := by rw [hn_def]; exact (Nat.le_ceil R).trans (by exact_mod_cast hceil)
  have hp1 : 0 ≤ 6 / η * K := mul_nonneg (div_nonneg (by norm_num) hη0.le) hK0.le
  have hp3 : 0 ≤ (8 * (g : ℝ) + 16) * K := mul_nonneg (by positivity) hK0.le
  have hp4 : 0 ≤ 3328000 * (g : ℝ) * K := mul_nonneg (by positivity) hK0.le
  have hp5 : 0 ≤ 2 / (η / (8 * K)) ^ 2 := by positivity
  have hp6 : 0 ≤ 2 / (1 / (416000 * (g : ℝ) * K)) ^ 2 := by positivity
  have hp7 : 0 < Real.exp (c₀ / η) := Real.exp_pos _
  have hn0 : 0 < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by rw [hn_def]; exact_mod_cast (show 1 ≤ a + b + c by omega)
  -- u = n / K
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = n / K := ⟨_, rfl⟩
  have hnu : n = K * u := by rw [hu_def]; field_simp
  have hu0 : 0 < u := by rw [hu_def]; exact div_pos hn0 hK0
  have hU : ∀ x : ℝ, x * K ≤ n → x ≤ u := fun x hx => by
    rw [hu_def, le_div_iff₀ hK0]; exact hx
  have hu1 : 6 / η ≤ u := hU _ (by linarith)
  have hu2 : (1024 : ℝ) ≤ u := hU _ (by linarith)
  have hu3 : 8 * (g : ℝ) + 16 ≤ u := hU _ (by linarith)
  have hu4 : 3328000 * (g : ℝ) ≤ u := hU _ (by linarith)
  have hηu : 6 ≤ u * η := (div_le_iff₀ hη0).1 hu1
  have hηu2 : η * u ≤ 1 / 2 * u := mul_le_mul_of_nonneg_right hη2 hu0.le
  -- the square root
  have hs0 : 0 ≤ Real.sqrt (2 * n) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (2 * n) ≤ η / 8 * u := by
    have hq : 0 < η / (8 * K) := div_pos hη0 (by linarith)
    have := sqrt_le_mul (n := n) hq (by linarith)
    calc Real.sqrt (2 * n) ≤ η / (8 * K) * n := this
      _ = η / 8 * u := by rw [hu_def]; field_simp
  have hs2 : 416000 * (g : ℝ) * Real.sqrt (2 * n) ≤ u := by
    have hq0 : 0 < 416000 * (g : ℝ) * K := mul_pos (mul_pos (by norm_num) hg0) hK0
    have := sqrt_le_mul (n := n) (one_div_pos.2 hq0) (by linarith)
    calc 416000 * (g : ℝ) * Real.sqrt (2 * n) ≤ 416000 * g * (1 / (416000 * g * K) * n) := by
          gcongr
      _ = u := by rw [hu_def]; field_simp
  -- t
  obtain ⟨t, htdef⟩ : ∃ t : ℕ, t = 2 * min a (min b c) / (2 * g + 1) := ⟨_, rfl⟩
  obtain ⟨-, htb⟩ := t_bounds (a := a) (b := b) (c := c) hg1 htdef
  have hm := min_ge hadm
  rw [← hn_def] at hm
  obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = min a (min b c) := ⟨_, rfl⟩
  rw [← hm_def] at htb hm
  have htb' : 2 * (m : ℝ) < ((t : ℝ) + 1) * K := by
    have : ((2 * m : ℕ) : ℝ) < ((t * (2 * g + 1) + (2 * g + 1) : ℕ) : ℝ) := by
      exact_mod_cast htb
    push_cast at this
    rw [hK]; linarith
  have hKs : Real.sqrt (2 * n) ≤ K * Real.sqrt (2 * n) := le_mul_of_one_le_left hs0 (by linarith)
  have key : 2 / 3 * (K * u - 2 * Real.sqrt (2 * n)) < ((t : ℝ) + 1) * K := by
    rw [← hnu]; linarith
  have h5 : 2 / 3 * (u - 2 * Real.sqrt (2 * n)) * K < ((t : ℝ) + 1) * K := by linarith [key, hKs]
  have ht_lo : 2 / 3 * (u - 2 * Real.sqrt (2 * n)) < (t : ℝ) + 1 :=
    lt_of_mul_lt_mul_right h5 hK0.le
  have ht_main : 2 / 3 * u * (1 - η / 2) ≤ (t : ℝ) := by linarith [ht_lo, hs1, hηu]
  have ht_half : u / 2 ≤ (t : ℝ) := by linarith [ht_main, hηu2]
  have ht512 : 512 ≤ t := by
    have : (512 : ℝ) ≤ t := by linarith
    exact_mod_cast this
  have ht1 : 2 * (Real.sqrt (2 * n) + g + 2) ≤ (t : ℝ) := by
    linarith [hs1, hηu2, hu3, ht_half]
  have ht3 : 8 * 52000 * (g : ℝ) * (4 + Real.sqrt (2 * n)) ≤ 3 * (t : ℝ) := by
    linarith [hs2, hu4, ht_half]
  -- the core bound
  have hcore := wilson_core hadm hg15 hga htdef
    (fun H h1 h2 h3 h4 => hT H (by rw [Fintype.card_fin]; exact hnT) h1 h2 h3 h4)
    hn400 ht512 (by rw [← hn_def]; exact ht1) (by rw [← hn_def]; exact ht3)
  -- logarithms
  have hlogn : c₀ / η ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]; linarith
  have hcη : c₀ ≤ Real.log n * η := (div_le_iff₀ hη0).1 hlogn
  have hlogt : Real.log (u / 2) ≤ Real.log t := Real.log_le_log (half_pos hu0) ht_half
  have hlogu : Real.log (u / 2) = Real.log n - Real.log K - Real.log 2 := by
    rw [Real.log_div hu0.ne' (by norm_num), hu_def, Real.log_div hn0.ne' hK0.ne']
  have hlog : (1 - η) * Real.log n ≤ Real.log t - 2 := by
    rw [hc₀] at hcη; linarith [hcη, hlogu, hlogt]
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hfin := final_ineq (ε := ε) (n := n) (u := u) (t := t) hη0 hηε hη2 hgη
    (by exact_mod_cast hg1) (by rw [hnu, hK]) hu0.le ht_main hL hlog
  linarith

/-- **The constant `1/6` is optimal.** `log realCount(a, b, c) = (1/6 + o(1)) n² log n` over
admissible profiles: the lower bound is `realCount_lower_sharp`, the upper bound is
`realCount_upper` (Linial–Luria). -/
theorem realCount_log_asymptotic {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ a b c : ℕ, AdmissibleProfile a b c → n₀ ≤ a + b + c →
      (1 / 6 - ε) * ((a + b + c : ℕ) : ℝ) ^ 2 * Real.log (a + b + c : ℕ) ≤
          Real.log (realCount a b c) ∧
        Real.log (realCount a b c) ≤
          (1 / 6 + ε) * ((a + b + c : ℕ) : ℝ) ^ 2 * Real.log (a + b + c : ℕ) := by
  obtain ⟨n₁, h₁⟩ := realCount_lower_sharp hε
  refine ⟨max n₁ 360004, fun a b c hadm hn => ⟨h₁ a b c hadm (le_of_max_le_left hn), ?_⟩⟩
  have hn4 : 360004 ≤ a + b + c := le_of_max_le_right hn
  have hup := realCount_upper (a := a) (b := b) (c := c) (by omega)
  obtain ⟨n, hn_def⟩ : ∃ n : ℝ, n = ((a + b + c : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hn_def] at hup ⊢
  have hnR : (360004 : ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hn4
  have hsq : 600 ≤ Real.sqrt (n - 3) := by
    rw [show (600 : ℝ) = Real.sqrt (600 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hfrac : 1200 / Real.sqrt (n - 3) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hfrac0 : 0 ≤ 1200 / Real.sqrt (n - 3) := by positivity
  have hlog2 : 2 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h82 : Real.exp 2 < 8 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        _ < 2.7182818286 * 2.7182818286 := by gcongr
        _ < 8 := by norm_num
    linarith
  have hX0 : 0 ≤ Real.log n - 2 + 1200 / Real.sqrt (n - 3) := by linarith
  have hXl : Real.log n - 2 + 1200 / Real.sqrt (n - 3) ≤ Real.log n := by linarith
  have hA : 0 ≤ n * (n - 1) / 6 := by
    have : 0 ≤ n * (n - 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hA2 : n * (n - 1) / 6 ≤ n ^ 2 / 6 := by nlinarith
  have hlogR : Real.log (realCount a b c) ≤
      n * (n - 1) / 6 * (Real.log n - 2 + 1200 / Real.sqrt (n - 3)) := by
    rcases Nat.eq_zero_or_pos (realCount a b c) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact mul_nonneg hA hX0
    · have := Real.log_le_log (by exact_mod_cast hpos) hup
      rwa [Real.log_exp] at this
  have hL : 0 ≤ Real.log n := by linarith
  calc Real.log (realCount a b c)
      ≤ n * (n - 1) / 6 * (Real.log n - 2 + 1200 / Real.sqrt (n - 3)) := hlogR
    _ ≤ n ^ 2 / 6 * Real.log n := mul_le_mul hA2 hXl hX0 (by positivity)
    _ ≤ (1 / 6 + ε) * n ^ 2 * Real.log n := by
        nlinarith [mul_nonneg (mul_nonneg hε.le (sq_nonneg n)) hL]

end CDRBicolour.Absorption.Count.Wilson
