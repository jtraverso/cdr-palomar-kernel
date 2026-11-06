/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-!
# Stratified charge bank, part 1: the cost recurrence (V33)

Constants `A M P : ℕ` are fixed first; then a cost sequence `N : ℕ → ℕ` and a demand
sequence `E : ℕ → ℕ` (nondecreasing on the steps `s < P`) with

  `N s ≤ A * (1 + E s + M * ∑ i < s, N i)`   for every step `s < P`.

* `cumulative_bound_sharp`: `∑ i ≤ s, N i ≤ A * (s+1) * (1+A*M)^s * (1 + E s)`.
* `cumulative_bound`: the uniform form `∑ i ≤ s, N i ≤ A * P * (1+A*M)^P * (1 + E s)`.
* `step_cost_le`: the single step cost `N s` obeys the same bound.
* zero cases: `cumulative_bound_zero_monitor` (`M = 0`), `cumulative_bound_zero_demand`
  (`E = 0`, only the additive `1`, i.e. torsion, is paid), `cost_eq_zero_of_A_eq_zero`.

The bound does not involve the number of bank cells.
-/

@[expose] public section

namespace S07V33

open Finset

/-- The cumulative constant `c s = A * (s+1) * (1+A*M)^s`. -/
def cumConst (A M s : ℕ) : ℕ := A * (s + 1) * (1 + A * M) ^ s

/-- Auxiliary: `(1+AM) * c s + A ≤ c (s+1)`. -/
lemma cumConst_step (A M s : ℕ) :
    (1 + A * M) * cumConst A M s + A ≤ cumConst A M (s + 1) := by
  unfold cumConst
  have h1 : 1 ≤ (1 + A * M) ^ (s + 1) := Nat.one_le_pow _ _ (by omega)
  have : A ≤ A * (1 + A * M) ^ (s + 1) := Nat.le_mul_of_pos_right _ h1
  calc (1 + A * M) * (A * (s + 1) * (1 + A * M) ^ s) + A
      = A * (s + 1) * (1 + A * M) ^ (s + 1) + A := by ring
    _ ≤ A * (s + 1) * (1 + A * M) ^ (s + 1) + A * (1 + A * M) ^ (s + 1) := by omega
    _ = A * (s + 1 + 1) * (1 + A * M) ^ (s + 1) := by ring

/-- **Sharp cumulative bound.** -/
theorem cumulative_bound_sharp (A M P : ℕ) (N E : ℕ → ℕ)
    (hE : MonotoneOn E (Set.Iio P))
    (hrec : ∀ s < P, N s ≤ A * (1 + E s + M * ∑ i ∈ range s, N i)) :
    ∀ s < P, ∑ i ∈ range (s + 1), N i ≤ cumConst A M s * (1 + E s) := by
  intro s
  induction s with
  | zero =>
    intro hs
    have := hrec 0 hs
    simp only [range_one, sum_singleton, cumConst, zero_add, pow_zero, mul_one,
      range_zero, sum_empty, mul_zero, add_zero] at this ⊢
    exact this
  | succ s ih =>
    intro hs
    have ih' := ih (by omega)
    have hmono : E s ≤ E (s + 1) := hE (by simp; omega) (by simpa using hs) (by omega)
    have hr := hrec (s + 1) hs
    rw [sum_range_succ]
    set S := ∑ i ∈ range (s + 1), N i
    have hS : S ≤ cumConst A M s * (1 + E (s + 1)) :=
      ih'.trans (Nat.mul_le_mul_left _ (by omega))
    calc S + N (s + 1) ≤ S + A * (1 + E (s + 1) + M * S) := by omega
      _ = (1 + A * M) * S + A * (1 + E (s + 1)) := by ring
      _ ≤ (1 + A * M) * (cumConst A M s * (1 + E (s + 1))) + A * (1 + E (s + 1)) := by
          gcongr
      _ = ((1 + A * M) * cumConst A M s + A) * (1 + E (s + 1)) := by ring
      _ ≤ cumConst A M (s + 1) * (1 + E (s + 1)) := by
          gcongr; exact cumConst_step A M s

/-- `c s ≤ A * P * (1+AM)^P` for `s < P`. -/
lemma cumConst_le_uniform (A M P s : ℕ) (hs : s < P) :
    cumConst A M s ≤ A * P * (1 + A * M) ^ P := by
  unfold cumConst
  have h1 : (1 + A * M) ^ s ≤ (1 + A * M) ^ P := Nat.pow_le_pow_right (by omega) hs.le
  gcongr
  omega

/-- **Uniform cumulative bound** `∑ i ≤ s, N i ≤ A * P * (1+A*M)^P * (1 + E s)`.
(The hypothesis `1 ≤ P` is not needed: it is implied by the existence of a step `s < P`.) -/
theorem cumulative_bound (A M P : ℕ) (N E : ℕ → ℕ)
    (hE : MonotoneOn E (Set.Iio P))
    (hrec : ∀ s < P, N s ≤ A * (1 + E s + M * ∑ i ∈ range s, N i)) :
    ∀ s < P, ∑ i ∈ range (s + 1), N i ≤ A * P * (1 + A * M) ^ P * (1 + E s) := by
  intro s hs
  exact (cumulative_bound_sharp A M P N E hE hrec s hs).trans
    (Nat.mul_le_mul_right _ (cumConst_le_uniform A M P s hs))

/-- Each single step cost obeys the uniform bound. -/
theorem step_cost_le (A M P : ℕ) (N E : ℕ → ℕ)
    (hE : MonotoneOn E (Set.Iio P))
    (hrec : ∀ s < P, N s ≤ A * (1 + E s + M * ∑ i ∈ range s, N i)) :
    ∀ s < P, N s ≤ A * P * (1 + A * M) ^ P * (1 + E s) := by
  intro s hs
  refine le_trans ?_ (cumulative_bound A M P N E hE hrec s hs)
  rw [sum_range_succ]; omega

/-- Zero monitor `M = 0`: `∑ i ≤ s, N i ≤ A * P * (1 + E s)`. -/
theorem cumulative_bound_zero_monitor (A P : ℕ) (N E : ℕ → ℕ)
    (hE : MonotoneOn E (Set.Iio P))
    (hrec : ∀ s < P, N s ≤ A * (1 + E s)) :
    ∀ s < P, ∑ i ∈ range (s + 1), N i ≤ A * P * (1 + E s) := by
  intro s hs
  have := cumulative_bound A 0 P N E hE (fun s hs => by simpa using hrec s hs) s hs
  simpa using this

/-- Zero demand `E = 0`: only the additive `1` (torsion) is paid:
`∑ i ≤ s, N i ≤ A * P * (1+A*M)^P`. -/
theorem cumulative_bound_zero_demand (A M P : ℕ) (N : ℕ → ℕ)
    (hrec : ∀ s < P, N s ≤ A * (1 + M * ∑ i ∈ range s, N i)) :
    ∀ s < P, ∑ i ∈ range (s + 1), N i ≤ A * P * (1 + A * M) ^ P := by
  intro s hs
  have := cumulative_bound A M P N (fun _ => 0) (fun _ _ _ _ _ => le_rfl)
    (fun s hs => by simpa using hrec s hs) s hs
  simpa using this

/-- Zero constant `A = 0` forces zero cost. -/
theorem cost_eq_zero_of_A_eq_zero (M P : ℕ) (N E : ℕ → ℕ)
    (hrec : ∀ s < P, N s ≤ 0 * (1 + E s + M * ∑ i ∈ range s, N i)) :
    ∀ s < P, N s = 0 := by
  intro s hs; simpa using hrec s hs

end S07V33
