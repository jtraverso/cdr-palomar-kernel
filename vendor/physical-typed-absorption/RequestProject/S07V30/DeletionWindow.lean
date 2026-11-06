/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# Quantitative deletion window for the rooted/prepared absorber supply (V30)

Elementary arithmetic: the two G2 resource windows survive the deletion of up to `⌊δ n⌋₊`
saturated vertices, with `δ` and `n₀` fixed from `α, β, U, h` (and a threshold `N`) BEFORE
`n`, the deletion `z` and the parameter `d`.

Constants (with `C = 2 ^ (h.choose 2)`):
* `delta α β h = min (min β (1/2)) (α / (40 * C))`;
* `n0 α U h N = ⌈8 * ((U + 3) + (U + 1 + h) * C) / α⌉₊ + 1 + 2 * N`.

This lemma does not close G3, G4 or T.
-/

namespace S07V30

/-- The constant `2 ^ (h choose 2)` (as a real). -/
noncomputable def capC (h : ℕ) : ℝ := (2 : ℝ) ^ (Nat.choose h 2)

/-- The deletion ratio `δ`, depending only on `α, β, h`. -/
noncomputable def delta (α β : ℝ) (h : ℕ) : ℝ :=
  min (min β (1 / 2)) (α / (40 * capC h))

/-- The threshold `n₀`, depending only on `α, U, h` and the prescribed bound `N`. -/
noncomputable def n0 (α : ℝ) (U h N : ℕ) : ℕ :=
  ⌈8 * (((U : ℝ) + 3) + ((U : ℝ) + 1 + (h : ℝ)) * capC h) / α⌉₊ + 1 + 2 * N

lemma capC_pos (h : ℕ) : 0 < capC h := by unfold capC; positivity

lemma one_le_capC (h : ℕ) : 1 ≤ capC h := by
  unfold capC; exact one_le_pow₀ (by norm_num)

lemma delta_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (h : ℕ) : 0 < delta α β h := by
  have := capC_pos h
  unfold delta
  refine lt_min (lt_min hβ (by norm_num)) (by positivity)

/-- Main window lemma with a prescribed threshold `N` for `n'`. The constants
`delta α β h` and `n0 α U h N` are fixed before `n`, `n'`, `z`, `d`. -/
theorem deletion_window_threshold {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (U h N : ℕ)
    (n n' z d : ℕ) (hn : n0 α U h N ≤ n) (hsum : n' + z = n)
    (hz : z ≤ ⌊delta α β h * (n : ℝ)⌋₊) (hd : d ≤ ⌊delta α β h * (n : ℝ)⌋₊) :
    (z : ℝ) ≤ β * (n : ℝ) ∧
    ((n : ℝ) / 2 ≤ (n' : ℝ) ∧ 0 < n') ∧
    ((U : ℝ) + 3 + 4 * (d : ℝ) < α * (n' : ℝ)) ∧
    ((U : ℝ) + 1 + (h : ℝ) + 5 * (d : ℝ)) * (2 : ℝ) ^ (Nat.choose h 2)
      ≤ (α / 2) * (n' : ℝ) ∧
    N ≤ n' := by
  set C := capC h with hCdef
  have hC1 : 1 ≤ C := one_le_capC h
  have hC0 : 0 < C := capC_pos h
  set δ := delta α β h with hδdef
  have hδ0 : 0 < δ := delta_pos hα hβ h
  have hδβ : δ ≤ β := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδh : δ ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδα : δ ≤ α / (40 * C) := min_le_right _ _
  have hδαC : δ * (40 * C) ≤ α := (le_div_iff₀ (by positivity)).1 hδα
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hzr : (z : ℝ) ≤ δ * n :=
    le_trans (Nat.cast_le.2 hz) (Nat.floor_le (by positivity))
  have hdr : (d : ℝ) ≤ δ * n :=
    le_trans (Nat.cast_le.2 hd) (Nat.floor_le (by positivity))
  have hsumr : (n' : ℝ) + z = n := by exact_mod_cast hsum
  -- the threshold
  set K : ℝ := 8 * (((U : ℝ) + 3) + ((U : ℝ) + 1 + (h : ℝ)) * C) / α with hK
  have hnK : K + 1 + 2 * (N : ℝ) ≤ n := by
    have h1 : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
    have h2 : ((⌈K⌉₊ + 1 + 2 * N : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hKα : α * K = 8 * (((U : ℝ) + 3) + ((U : ℝ) + 1 + (h : ℝ)) * C) := by
    rw [hK]; field_simp
  have hUC : 0 ≤ ((U : ℝ) + 1 + (h : ℝ)) * C := by positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- α n > 8 * stuff
  have hαn : 8 * (((U : ℝ) + 3) + ((U : ℝ) + 1 + (h : ℝ)) * C) < α * n := by
    have : α * K < α * n := mul_lt_mul_of_pos_left (by linarith) hα
    linarith
  have hδn2 : δ * n ≤ (1 / 2) * n := mul_le_mul_of_nonneg_right hδh hn0
  have hδnβ : δ * n ≤ β * n := mul_le_mul_of_nonneg_right hδβ hn0
  have hhalf : (n : ℝ) / 2 ≤ n' := by linarith
  have hαhalf : α * ((n : ℝ) / 2) ≤ α * n' := mul_le_mul_of_nonneg_left hhalf hα.le
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have e1 : (d : ℝ) * (40 * C) ≤ δ * n * (40 * C) :=
    mul_le_mul_of_nonneg_right hdr (by positivity)
  have e2 : δ * (40 * C) * n ≤ α * n := mul_le_mul_of_nonneg_right hδαC hn0
  have e3 : (d : ℝ) * 1 ≤ d * C := mul_le_mul_of_nonneg_left hC1 hd0
  refine ⟨by linarith, ⟨hhalf, ?_⟩, ?_, ?_, ?_⟩
  · have : (0 : ℝ) < n' := by
      have : (1 : ℝ) ≤ n := by
        have : 0 ≤ K := by rw [hK]; positivity
        linarith
      linarith
    exact_mod_cast this
  · linarith
  · have hpow : (2 : ℝ) ^ (Nat.choose h 2) = C := rfl
    rw [hpow]
    linarith
  · have hK0 : 0 ≤ K := by rw [hK]; positivity
    have : (N : ℝ) ≤ n' := by linarith
    exact_mod_cast this

/-- The window lemma as an explicit `∃ δ n₀` statement with a prescribed threshold `N`:
`δ` and `n₀` depend only on `α, β, U, h, N` and are chosen before `n` and the deletion. -/
theorem exists_deletion_window_threshold {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (U h N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n n' z d : ℕ, n₀ ≤ n → n' + z = n →
      z ≤ ⌊δ * (n : ℝ)⌋₊ → d ≤ ⌊δ * (n : ℝ)⌋₊ →
      (z : ℝ) ≤ β * (n : ℝ) ∧
      ((n : ℝ) / 2 ≤ (n' : ℝ) ∧ 0 < n') ∧
      ((U : ℝ) + 3 + 4 * (d : ℝ) < α * (n' : ℝ)) ∧
      ((U : ℝ) + 1 + (h : ℝ) + 5 * (d : ℝ)) * (2 : ℝ) ^ (Nat.choose h 2)
        ≤ (α / 2) * (n' : ℝ) ∧
      N ≤ n' :=
  ⟨delta α β h, delta_pos hα hβ h, n0 α U h N, fun n n' z d hn hs hz hd =>
    deletion_window_threshold hα hβ U h N n n' z d hn hs hz hd⟩

/-- The basic window lemma (items 1–4), `n₀ = n0 α U h 0`. -/
theorem deletion_window {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (U h : ℕ)
    (n n' z d : ℕ) (hn : n0 α U h 0 ≤ n) (hsum : n' + z = n)
    (hz : z ≤ ⌊delta α β h * (n : ℝ)⌋₊) (hd : d ≤ ⌊delta α β h * (n : ℝ)⌋₊) :
    (z : ℝ) ≤ β * (n : ℝ) ∧
    ((n : ℝ) / 2 ≤ (n' : ℝ) ∧ 0 < n') ∧
    ((U : ℝ) + 3 + 4 * (d : ℝ) < α * (n' : ℝ)) ∧
    ((U : ℝ) + 1 + (h : ℝ) + 5 * (d : ℝ)) * (2 : ℝ) ^ (Nat.choose h 2)
      ≤ (α / 2) * (n' : ℝ) :=
  let ⟨a, b, c, e, _⟩ := deletion_window_threshold hα hβ U h 0 n n' z d hn hsum hz hd
  ⟨a, b, c, e⟩

/-- `∃ δ n₀` form of the basic window lemma. -/
theorem exists_deletion_window {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (U h : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n n' z d : ℕ, n₀ ≤ n → n' + z = n →
      z ≤ ⌊δ * (n : ℝ)⌋₊ → d ≤ ⌊δ * (n : ℝ)⌋₊ →
      (z : ℝ) ≤ β * (n : ℝ) ∧
      ((n : ℝ) / 2 ≤ (n' : ℝ) ∧ 0 < n') ∧
      ((U : ℝ) + 3 + 4 * (d : ℝ) < α * (n' : ℝ)) ∧
      ((U : ℝ) + 1 + (h : ℝ) + 5 * (d : ℝ)) * (2 : ℝ) ^ (Nat.choose h 2)
        ≤ (α / 2) * (n' : ℝ) :=
  ⟨delta α β h, delta_pos hα hβ h, n0 α U h 0, fun n n' z d hn hs hz hd =>
    deletion_window hα hβ U h n n' z d hn hs hz hd⟩

end S07V30
