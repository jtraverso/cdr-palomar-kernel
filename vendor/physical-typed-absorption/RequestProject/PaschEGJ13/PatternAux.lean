/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.PaschEGJ13.PatternCount
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Auxiliary weight functions for the proof of Theorem 3.1

For an `ℓ`-set weight function `w`:
* `nrm ℓ w T = ∑_{|e| = ℓ, e ⊇ T} w e` is the quantity `ω(T)` of (1.1);
* `wt ℓ w t T = ∑ w e` over the `ℓ`-sets `e ∋ t` whose elements below `t` are exactly `T`
  (the function `ω^{t,k}` of the paper, on `k`-sets `T`);
* `wle ℓ w t = ∑_{s < t} wt ℓ w s` (the function `ω^{≤t-1,k}`).
-/

@[expose] public section

namespace Pseudorandom

namespace Patt

open Finset

variable {n q : ℕ}

/-- `ω(T) = ∑_{e ⊇ T} ω(e)` over `ℓ`-sets. -/
noncomputable def nrm (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (T : Finset (Fin n)) : ℝ :=
  ∑ e ∈ (powersetCard ℓ univ).filter (fun e => T ⊆ e), w e

/-- The weight function `ω^{t,k}`. -/
noncomputable def wt (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (t : Fin n) (T : Finset (Fin n)) : ℝ :=
  ∑ e ∈ (powersetCard ℓ univ).filter (fun e => t ∈ e ∧ e.filter (· < t) = T), w e

/-- The weight function `ω^{≤ t-1, k} = ∑_{s < t} ω^{s,k}`. -/
noncomputable def wle (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (t : ℕ) (T : Finset (Fin n)) : ℝ :=
  ∑ s ∈ univ.filter (fun s : Fin n => (s : ℕ) < t), wt ℓ w s T

/-- The normalised norm bound `‖ω‖_j q^j g^{j-1} q^{-ℓ} ≤ M` for all `j ∈ [ℓ]`. -/
def NB (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (q g M : ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ ℓ → ∀ T : Finset (Fin n), T.card = j →
    nrm ℓ w T * q ^ j * g ^ (j - 1) / q ^ ℓ ≤ M

variable {ℓ : ℕ} {w : Finset (Fin n) → ℝ}

theorem wt_nonneg (hw : ∀ e, 0 ≤ w e) (t : Fin n) (T : Finset (Fin n)) : 0 ≤ wt ℓ w t T :=
  sum_nonneg fun e _ => hw e

theorem wle_nonneg (hw : ∀ e, 0 ≤ w e) (t : ℕ) (T : Finset (Fin n)) : 0 ≤ wle ℓ w t T :=
  sum_nonneg fun s _ => wt_nonneg hw s T

theorem nrm_nonneg (hw : ∀ e, 0 ≤ w e) (T : Finset (Fin n)) : 0 ≤ nrm ℓ w T :=
  sum_nonneg fun e _ => hw e

theorem wle_mono (hw : ∀ e, 0 ≤ w e) {t t' : ℕ} (h : t ≤ t') (T : Finset (Fin n)) :
    wle ℓ w t T ≤ wle ℓ w t' T := by
  unfold wle
  apply sum_le_sum_of_subset_of_nonneg
  · intro s; simp only [mem_filter, mem_univ, true_and]; omega
  · intro s _ _; exact wt_nonneg hw s T

/-- The rank map is injective on `e`. -/
theorem card_filter_rk_le_one (e : Finset (Fin n)) (k : ℕ) :
    (e.filter (fun s => rk e s = k)).card ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  rw [mem_filter] at ha hb
  by_contra hab
  have key : ∀ x y, x ∈ e → x < y → rk e x < rk e y := by
    intro x y hx hxy
    unfold rk
    apply card_lt_card
    rw [ssubset_iff_of_subset]
    · exact ⟨x, by simp [hx, hxy], by simp⟩
    · intro z; simp only [mem_filter]; exact fun h => ⟨h.1, h.2.trans hxy⟩
  rcases lt_or_gt_of_ne hab with h | h
  · have := key a b ha.1 h; omega
  · have := key b a hb.1 h; omega

/-- Fibre decomposition of a sum over pairs `(T, e)` with `e.filter (· < t) = T`. -/
theorem sum_fiber (k : ℕ) (t : Fin n) (Q : Finset (Fin n) → Prop) [DecidablePred Q]
    (f : Finset (Fin n) → ℝ) :
    ∑ T ∈ (powersetCard k univ).filter Q,
      ∑ e ∈ (powersetCard ℓ univ).filter (fun e => t ∈ e ∧ e.filter (· < t) = T), f e =
    ∑ e ∈ (powersetCard ℓ univ).filter (fun e => t ∈ e ∧ rk e t = k ∧ Q (e.filter (· < t))),
      f e := by
  rw [← sum_fiberwise_of_maps_to (s := (powersetCard ℓ univ).filter
      (fun e => t ∈ e ∧ rk e t = k ∧ Q (e.filter (· < t))))
    (t := (powersetCard k univ).filter Q) (g := fun e => e.filter (· < t))]
  · refine sum_congr rfl fun T hT => ?_
    refine sum_congr ?_ fun _ _ => rfl
    ext e
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at hT ⊢
    constructor
    · rintro ⟨he, hte, hT'⟩
      subst hT'
      exact ⟨⟨he, hte, hT.1, hT.2⟩, rfl⟩
    · rintro ⟨⟨he, hte, -, -⟩, hT'⟩
      exact ⟨he, hte, hT'⟩
  · intro e he
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at he ⊢
    exact ⟨he.2.2.1, he.2.2.2⟩

theorem nrm_wt_le (hw : ∀ e, 0 ≤ w e) (k : ℕ) (t : Fin n) (T' : Finset (Fin n)) :
    nrm k (wt ℓ w t) T' ≤ nrm ℓ w (insert t T') := by
  classical
  unfold nrm wt
  rw [sum_fiber k t (fun T => T' ⊆ T) w]
  apply sum_le_sum_of_subset_of_nonneg
  · intro e
    simp only [mem_filter]
    rintro ⟨he, hte, -, hT'⟩
    refine ⟨he, insert_subset hte (hT'.trans (filter_subset _ _))⟩
  · intro e _ _; exact hw e

theorem nrm_wle_le (hw : ∀ e, 0 ≤ w e) (k : ℕ) (t : ℕ) (T' : Finset (Fin n)) :
    nrm k (wle ℓ w t) T' ≤ nrm ℓ w T' := by
  classical
  unfold nrm wle
  rw [sum_comm]
  have h1 : ∀ s : Fin n, ∑ T ∈ (powersetCard k univ).filter (fun T => T' ⊆ T), wt ℓ w s T =
      ∑ e ∈ (powersetCard ℓ univ).filter (fun e => T' ⊆ e),
        w e * (if s ∈ e ∧ rk e s = k ∧ T' ⊆ e.filter (· < s) then 1 else 0) := by
    intro s
    unfold wt
    rw [sum_fiber k s (fun T => T' ⊆ T) w]
    rw [← sum_filter_add_sum_filter_not ((powersetCard ℓ univ).filter (fun e => T' ⊆ e))
      (fun e => s ∈ e ∧ rk e s = k ∧ T' ⊆ e.filter (· < s))]
    have h0 : ∑ e ∈ ((powersetCard ℓ univ).filter (fun e => T' ⊆ e)).filter
        (fun e => ¬ (s ∈ e ∧ rk e s = k ∧ T' ⊆ e.filter (· < s))),
        w e * (if s ∈ e ∧ rk e s = k ∧ T' ⊆ e.filter (· < s) then 1 else 0) = 0 :=
      sum_eq_zero fun e he => by rw [mem_filter] at he; simp [he.2]
    rw [h0, add_zero]
    rw [filter_filter]
    refine sum_congr ?_ fun e he => ?_
    · ext e
      simp only [mem_filter]
      constructor
      · rintro ⟨he, h1, h2, h3⟩; exact ⟨he, h3.trans (filter_subset _ _), h1, h2, h3⟩
      · rintro ⟨he, -, h1, h2, h3⟩; exact ⟨he, h1, h2, h3⟩
    · rw [mem_filter] at he; simp [he.2]
  rw [sum_filter]
  simp_rw [sum_filter] at h1 ⊢
  calc ∑ s : Fin n, (if (s : ℕ) < t then ∑ T ∈ powersetCard k univ,
          (if T' ⊆ T then wt ℓ w s T else 0) else 0)
      ≤ ∑ s : Fin n, ∑ T ∈ powersetCard k univ, (if T' ⊆ T then wt ℓ w s T else 0) := by
        refine sum_le_sum fun s _ => ?_
        split_ifs
        · exact le_rfl
        · exact sum_nonneg fun T _ => by split_ifs; exacts [wt_nonneg hw s T, le_rfl]
    _ = ∑ s : Fin n, ∑ e ∈ powersetCard ℓ univ, (if T' ⊆ e then
          w e * (if s ∈ e ∧ rk e s = k ∧ T' ⊆ e.filter (· < s) then 1 else 0) else 0) := by
        refine sum_congr rfl fun s _ => h1 s
    _ = ∑ e ∈ powersetCard ℓ univ, (if T' ⊆ e then w e *
          ((e.filter (fun s => s ∈ e ∧ rk e s = k ∧ T' ⊆ e.filter (· < s))).card : ℝ)
          else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun e _ => ?_
        split_ifs
        · rw [← mul_sum, sum_boole]
          congr 3
          ext s; simp only [mem_filter, mem_univ, true_and]
          constructor
          · intro h; exact ⟨h.1, h⟩
          · intro h; exact h.2
        · simp
    _ ≤ ∑ e ∈ powersetCard ℓ univ, (if T' ⊆ e then w e else 0) := by
        refine sum_le_sum fun e _ => ?_
        split_ifs
        · have : ((e.filter (fun s => s ∈ e ∧ rk e s = k ∧ T' ⊆ e.filter (· < s))).card : ℝ)
              ≤ 1 := by
            have h := card_filter_rk_le_one e k
            have : (e.filter (fun s => s ∈ e ∧ rk e s = k ∧ T' ⊆ e.filter (· < s))).card ≤
                (e.filter (fun s => rk e s = k)).card :=
              card_le_card fun s => by simp only [mem_filter]; exact fun h => ⟨h.1, h.2.2.1⟩
            exact_mod_cast this.trans h
          exact mul_le_of_le_one_right (hw e) this
        · exact le_rfl

theorem cnt_le_nrm (hw : ∀ e, 0 ≤ w e) (α : ℕ → Fin q) (c : Fin n → Fin q) :
    cnt ℓ w α c ≤ nrm ℓ w ∅ := by
  unfold cnt nrm
  rw [filter_true_of_mem (fun e _ => empty_subset e)]
  refine sum_le_sum fun e _ => ?_
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]; exact hw e

theorem cnt_mono {w w' : Finset (Fin n) → ℝ} (h : ∀ e, w e ≤ w' e) (α : ℕ → Fin q)
    (c : Fin n → Fin q) : cnt ℓ w α c ≤ cnt ℓ w' α c := by
  unfold cnt
  refine sum_le_sum fun e _ => ?_
  split_ifs
  · simpa using h e
  · simp

theorem cnt_zero (w : Finset (Fin n) → ℝ) (α : ℕ → Fin q) (c : Fin n → Fin q) :
    cnt 0 w α c = w ∅ := by
  unfold cnt
  simp [Pat]

theorem nrm_empty_eq (w : Finset (Fin n) → ℝ) :
    nrm ℓ w ∅ = ∑ e ∈ powersetCard ℓ univ, w e := by
  unfold nrm
  rw [filter_true_of_mem (fun e _ => empty_subset e)]

end Patt

end Pseudorandom
