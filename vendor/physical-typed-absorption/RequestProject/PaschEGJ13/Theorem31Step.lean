/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.Theorem31Fin
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Theorem 3.1 on `Fin n`: the inductive step

We apply Freedman's inequality to the exposure martingale `Xp`, stopped as soon as one of the
auxiliary counts `cnt k (wle ℓ w (t+1))` or `cnt k (wt ℓ w t)` (for `1 ≤ k < ℓ`) becomes too
large; the probability of stopping is controlled by the induction hypothesis.
-/

@[expose] public section

namespace Pseudorandom

namespace Patt

open Finset

variable {n q : ℕ} {ℓ : ℕ} {w : Finset (Fin n) → ℝ}

theorem cnt_sum {ι : Type*} (S : Finset ι) (f : ι → Finset (Fin n) → ℝ) (k : ℕ)
    (α : ℕ → Fin q) (c : Fin n → Fin q) :
    cnt k (fun T => ∑ s ∈ S, f s T) α c = ∑ s ∈ S, cnt k (f s) α c := by
  unfold cnt
  simp_rw [sum_mul]
  rw [sum_comm]

theorem cnt_congr (k : ℕ) (f : Finset (Fin n) → ℝ) (α : ℕ → Fin q) (c c' : Fin n → Fin q)
    (h : ∀ T, f T ≠ 0 → ∀ v ∈ T, c v = c' v) : cnt k f α c = cnt k f α c' := by
  unfold cnt
  refine sum_congr rfl fun T _ => ?_
  by_cases hT : f T = 0
  · simp [hT]
  · congr 2
    unfold Pat
    apply propext
    constructor
    · intro H v hv; rw [← h T hT v hv]; exact H v hv
    · intro H v hv; rw [h T hT v hv]; exact H v hv

theorem wt_support {s : Fin n} {T : Finset (Fin n)} (h : wt ℓ w s T ≠ 0) : ∀ v ∈ T, v < s := by
  unfold wt at h
  obtain ⟨e, he, -⟩ := exists_ne_zero_of_sum_ne_zero h
  rw [mem_filter] at he
  intro v hv
  rw [← he.2.2, mem_filter] at hv
  exact hv.2

theorem wle_support {t : ℕ} {T : Finset (Fin n)} (h : wle ℓ w t T ≠ 0) :
    ∀ v ∈ T, (v : ℕ) + 1 < t := by
  unfold wle at h
  obtain ⟨s, hs, hs'⟩ := exists_ne_zero_of_sum_ne_zero h
  rw [mem_filter] at hs
  intro v hv
  have := wt_support hs' v hv
  have : (v : ℕ) < s := this
  omega

open Classical in
/-- The good event at time `t`. -/
def goodEv (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (α : ℕ → Fin q) (N M lam : ℝ) (t : ℕ)
    (c : Fin n → Fin q) : Prop :=
  ∀ k, 1 ≤ k → k < ℓ →
    cnt k (wle ℓ w (t + 1)) α c < N * (1 / (q : ℝ)) ^ k + lam * (q : ℝ) ^ (ℓ - k) ∧
    ∀ s : Fin n, (s : ℕ) = t → cnt k (wt ℓ w s) α c < 2 * ((q : ℝ) ^ (ℓ - k - 1) * M)

theorem goodEv_adapted (α : ℕ → Fin q) (N M lam : ℝ) (t : ℕ) :
    Adapted t (goodEv ℓ w α N M lam t) := by
  intro c c' h
  unfold goodEv
  have h1 : ∀ k, cnt k (wle ℓ w (t + 1)) α c = cnt k (wle ℓ w (t + 1)) α c' := by
    intro k
    apply cnt_congr
    intro T hT v hv
    exact h v (by have := wle_support hT v hv; omega)
  have h2 : ∀ k (s : Fin n), (s : ℕ) = t → cnt k (wt ℓ w s) α c = cnt k (wt ℓ w s) α c' := by
    intro k s hs
    apply cnt_congr
    intro T hT v hv
    exact h v (by have : v < s := wt_support hT v hv; rw [← hs]; exact this)
  apply propext
  constructor
  · intro H k hk1 hk
    refine ⟨by rw [← h1]; exact (H k hk1 hk).1, fun s hs => ?_⟩
    rw [← h2 k s hs]; exact (H k hk1 hk).2 s hs
  · intro H k hk1 hk
    refine ⟨by rw [h1]; exact (H k hk1 hk).1, fun s hs => ?_⟩
    rw [h2 k s hs]; exact (H k hk1 hk).2 s hs

theorem sum_Ico_two_pow : ∀ ℓ : ℕ, 1 ≤ ℓ → ∑ k ∈ Ico 1 ℓ, (2 : ℝ) ^ k = 2 ^ ℓ - 2
  | 0, h => absurd h (by omega)
  | 1, _ => by simp
  | ℓ + 2, _ => by
    rw [sum_Ico_succ_top (by omega), sum_Ico_two_pow (ℓ + 1) (by omega)]
    ring

/-- The final numerical estimate of the union bound. -/
theorem union_numeric {ℓ n : ℕ} {g : ℝ} (hℓ : 2 ≤ ℓ) (hn : 1 ≤ n)
    (hg : 24 * (ℓ : ℝ) ^ 3 * (ℓ + 1 + Real.log n) ≤ g) :
    2 ^ (ℓ + 1) * (n : ℝ) * Real.exp (-(g / (24 * ((ℓ : ℝ) - 1) ^ 2))) ≤
      Real.exp (-(g / (24 * ℓ ^ 2))) := by
  have hL : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hg0 : 0 < g := by
    have : 0 < 24 * (ℓ : ℝ) ^ 3 * (ℓ + 1 + Real.log n) := by positivity
    linarith
  have hpos : (0 : ℝ) < 2 ^ (ℓ + 1) * n := by positivity
  rw [← Real.exp_log hpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log (2 ^ (ℓ + 1) * (n : ℝ)) ≤ ℓ + 1 + Real.log n := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    push_cast
    nlinarith
  have hkey : g / (24 * ℓ ^ 2) + (ℓ + 1 + Real.log n) ≤ g / (24 * ((ℓ : ℝ) - 1) ^ 2) := by
    have h1 : (ℓ + 1 + Real.log n) ≤ g / (24 * ℓ ^ 3) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2 : g / (24 * ℓ ^ 2) + g / (24 * ℓ ^ 3) ≤ g / (24 * ((ℓ : ℝ) - 1) ^ 2) := by
      have hl1 : (0 : ℝ) < ℓ - 1 := by linarith
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      have : (ℓ : ℝ) ^ 3 + ℓ ^ 2 ≥ 0 := by positivity
      have key : ((ℓ : ℝ) ^ 3 + ℓ ^ 2) * (ℓ - 1) ^ 2 ≤ ℓ ^ 5 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left key (show (0:ℝ) ≤ 24 ^ 3 * g by positivity)]
    linarith
  linarith

end Patt

end Pseudorandom
