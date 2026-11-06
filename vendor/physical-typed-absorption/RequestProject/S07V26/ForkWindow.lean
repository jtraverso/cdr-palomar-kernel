/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# V26 — the explicit constants and the loss window for the fork greedy

All constants depend only on the pool density `β > 0` (in the native application
`β = qα/2`, from the retained H3 pools of the V25 core); they are fixed BEFORE the host.

* saturation threshold `forkQ β r = max 1 ⌈128 r / β⌉₊` (`r = 0` is covered by the `max 1`:
  then there is no input edge and `Q = 1`);
* sparsity constant `forkEps β = β² / (1024 (β + 1))`;
* size threshold `n ≥ 32 / β`.

`fork_window`: if `r, b ≤ forkEps β · n`, `βn ≥ 32`, `2I ≤ n r` and `βn ≤ m`, then the integer
window `8I + Q(6 + 2(b + 3r + Q + 4)) < Q m` of `fork_greedy` holds. The proof is the actual
computation `8I/Q ≤ βn/32`, `2b + 6r ≤ βn/128`, `2Q ≤ βn/4 + 2`, `16 < (91/128)βn`.
-/

namespace S07V26

/-- the saturation threshold -/
noncomputable def forkQ (β : ℝ) (r : ℕ) : ℕ := max 1 ⌈128 * (r : ℝ) / β⌉₊

/-- the sparsity constant -/
noncomputable def forkEps (β : ℝ) : ℝ := β ^ 2 / (1024 * (β + 1))

lemma forkEps_pos {β : ℝ} (hβ : 0 < β) : 0 < forkEps β := by unfold forkEps; positivity

lemma one_le_forkQ (β : ℝ) (r : ℕ) : 1 ≤ forkQ β r := le_max_left _ _

lemma forkQ_lower {β : ℝ} (hβ : 0 < β) (r : ℕ) : 128 * (r : ℝ) ≤ forkQ β r * β := by
  have h1 : 128 * (r : ℝ) / β ≤ forkQ β r := by
    unfold forkQ
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  rwa [div_le_iff₀ hβ] at h1

lemma forkQ_upper {β : ℝ} (hβ : 0 < β) (r : ℕ) : (forkQ β r : ℝ) ≤ 128 * r / β + 1 := by
  have hx : 0 ≤ 128 * (r : ℝ) / β := by positivity
  unfold forkQ
  rcases le_total 1 ⌈128 * (r : ℝ) / β⌉₊ with h | h
  · rw [max_eq_right h]; exact (Nat.ceil_lt_add_one hx).le
  · rw [max_eq_left h]; push_cast; linarith

/-- **the window**: the actual constants make the integer window of `fork_greedy` hold -/
theorem fork_window {β : ℝ} (hβ : 0 < β) {n : ℝ} (hn0 : 0 ≤ n) (hn : 32 ≤ β * n)
    {r b I m : ℕ} (hr : (r : ℝ) ≤ forkEps β * n) (hb : (b : ℝ) ≤ forkEps β * n)
    (hI : 2 * (I : ℝ) ≤ n * r) (hm : β * n ≤ m) :
    8 * I + forkQ β r * (6 + 2 * (b + 3 * r + forkQ β r + 4)) < forkQ β r * m := by
  set Q := forkQ β r with hQdef
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast one_le_forkQ β r
  have hQlo := forkQ_lower hβ r
  have hQhi := forkQ_upper hβ r
  rw [← hQdef] at hQlo hQhi
  set e := forkEps β with he
  have he0 : 0 ≤ e := (forkEps_pos hβ).le
  have hedef : e * (1024 * (β + 1)) = β ^ 2 := by
    rw [he, forkEps]; field_simp
  have hK1 : 1024 * e ≤ β := by nlinarith
  have hK2 : 1024 * e ≤ β ^ 2 := by nlinarith
  -- `8I ≤ Qβn/32`
  have hB : 8 * (I : ℝ) ≤ Q * β * n / 32 := by
    have : 128 * (r : ℝ) * n ≤ Q * β * n := mul_le_mul_of_nonneg_right hQlo hn0
    nlinarith
  -- `2Q ≤ βn/4 + 2`
  have h2Q : 2 * (Q : ℝ) ≤ β * n / 4 + 2 := by
    have hQβ : (Q : ℝ) * β ≤ 128 * r + β := by
      have := mul_le_mul_of_nonneg_right hQhi hβ.le
      rwa [add_mul, div_mul_cancel₀ _ hβ.ne', one_mul] at this
    have h3 : 256 * (r : ℝ) ≤ β ^ 2 * n / 4 := by nlinarith
    have : β * (2 * Q) ≤ β * (β * n / 4 + 2) := by nlinarith
    exact le_of_mul_le_mul_left this hβ
  -- `2b + 6r ≤ βn/128`
  have hbr : 2 * (b : ℝ) + 6 * r ≤ β * n / 128 := by nlinarith
  have hA : 14 + 2 * (b : ℝ) + 6 * r + 2 * Q < 31 / 32 * (β * n) := by nlinarith
  have hQpos : (0 : ℝ) < Q := by linarith
  have hreal : 8 * (I : ℝ) + Q * (6 + 2 * (b + 3 * r + Q + 4)) < Q * m := by
    have h1 : (Q : ℝ) * (6 + 2 * (b + 3 * r + Q + 4)) < Q * (31 / 32 * (β * n)) :=
      mul_lt_mul_of_pos_left (by linarith) hQpos
    have h2 : (Q : ℝ) * (β * n) ≤ Q * m := mul_le_mul_of_nonneg_left hm hQpos.le
    nlinarith
  exact_mod_cast hreal

end S07V26
