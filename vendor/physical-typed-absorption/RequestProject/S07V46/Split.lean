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
# V46 §1 — capacitated integer splitting (occurrence capacities)

The purely combinatorial core of the allocation: an integer demand `w` whose absolute value is at
most the total capacity of a finite family of slots can be split EXACTLY into integer pieces, each
of absolute value at most the capacity of its slot.

* `nat_split` : `a ≤ ∑_{i∈s} cap i` ⇒ `∃ f ≤ cap`, supported on `s`, with `∑_{i∈s} f i = a`.
* `int_split` : `|w| ≤ ∑_{i∈s} cap i` ⇒ `∃ f`, `|f i| ≤ cap i`, supported on `s`, `∑ f = w`.
* `strata_split` : the slots are (stratum `i ≤ t`, colour `p : Fin P`), slot capacity `m i`;
  `|w| ≤ P * ∑_{i ≤ t} m i` ⇒ an exact split `z i p` with `|z i p| ≤ m i`, zero for `i > t`.

The bank has `m i` occurrences of EACH sign for every active (entry, colour) in stratum `i`, so
no sign constraint between slots is needed.
-/

@[expose] public section

namespace S07V46

open Finset

/-- **Natural-number splitting under capacities.** -/
theorem nat_split {ι : Type*} [DecidableEq ι] (cap : ι → ℕ) :
    ∀ (s : Finset ι) (a : ℕ), a ≤ ∑ i ∈ s, cap i →
      ∃ f : ι → ℕ, (∀ i, f i ≤ cap i) ∧ (∀ i, i ∉ s → f i = 0) ∧ ∑ i ∈ s, f i = a := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro a ha
    refine ⟨fun _ => 0, fun _ => Nat.zero_le _, fun _ _ => rfl, ?_⟩
    simp at ha; simp [ha]
  | insert j s hj ih =>
    intro a ha
    rw [sum_insert hj] at ha
    obtain ⟨f, hf, hf0, hfs⟩ := ih (a - min a (cap j)) (by omega)
    refine ⟨Function.update f j (min a (cap j)), fun i => ?_, fun i hi => ?_, ?_⟩
    · by_cases h : i = j
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hf i
    · have hij : i ≠ j := fun h => hi (h ▸ mem_insert_self _ _)
      rw [Function.update_of_ne hij]
      exact hf0 i fun h => hi (mem_insert_of_mem h)
    · rw [sum_insert hj, Function.update_self]
      have : ∑ i ∈ s, Function.update f j (min a (cap j)) i = ∑ i ∈ s, f i :=
        sum_congr rfl fun i hi => Function.update_of_ne (fun h : i = j => hj (h ▸ hi)) _ _
      rw [this, hfs]
      omega

/-- **Integer splitting under capacities.** -/
theorem int_split {ι : Type*} [DecidableEq ι] (cap : ι → ℕ) (s : Finset ι) (w : ℤ)
    (hw : w.natAbs ≤ ∑ i ∈ s, cap i) :
    ∃ f : ι → ℤ, (∀ i, (f i).natAbs ≤ cap i) ∧ (∀ i, i ∉ s → f i = 0) ∧
      ∑ i ∈ s, f i = w := by
  obtain ⟨f, hf, hf0, hfs⟩ := nat_split cap s w.natAbs hw
  rcases le_or_gt 0 w with h | h
  · refine ⟨fun i => (f i : ℤ), fun i => by simpa using hf i, fun i hi => by simp [hf0 i hi],
      ?_⟩
    rw [← Nat.cast_sum, hfs]; exact Int.natAbs_of_nonneg h
  · refine ⟨fun i => -(f i : ℤ), fun i => by simpa using hf i, fun i hi => by simp [hf0 i hi],
      ?_⟩
    rw [sum_neg_distrib, ← Nat.cast_sum, hfs, Int.natCast_natAbs, abs_of_neg h, neg_neg]

/-- **Stratum × colour splitting.** The slots are pairs `(i, p)` with `i ≤ t`, `p : Fin P`, the slot
`(i, p)` having capacity `m i`.  An integer `w` with `|w| ≤ P * ∑_{i ≤ t} m i` splits exactly. -/
theorem strata_split (P : ℕ) (m : ℕ → ℕ) (t : ℕ) (w : ℤ)
    (hw : w.natAbs ≤ P * ∑ i ∈ range (t + 1), m i) :
    ∃ z : ℕ → Fin P → ℤ, (∀ i p, (z i p).natAbs ≤ m i) ∧ (∀ i p, t < i → z i p = 0) ∧
      ∑ i ∈ range (t + 1), ∑ p, z i p = w := by
  classical
  have hcap : ∑ ip ∈ (range (t + 1)) ×ˢ (univ : Finset (Fin P)), m ip.1 =
      P * ∑ i ∈ range (t + 1), m i := by
    rw [sum_product]; simp [mul_sum]
  obtain ⟨f, hf, hf0, hfs⟩ := int_split (fun ip : ℕ × Fin P => m ip.1)
    ((range (t + 1)) ×ˢ (univ : Finset (Fin P))) w (by rw [hcap]; exact hw)
  refine ⟨fun i p => f (i, p), fun i p => hf (i, p), fun i p hi => hf0 _ ?_, ?_⟩
  · simp only [mem_product, mem_range, mem_univ, and_true]; omega
  · rw [← hfs, sum_product]

end S07V46
