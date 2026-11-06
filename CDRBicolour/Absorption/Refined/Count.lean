/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Refined.Shift

/-!
# Residues mod 6 on the colour classes (refined H1/H3/H4, item 2b)

* `abs_class_sgn_le`: on a colour class, `Σ_w sgn(t + w)` (`sgn m = 1` if `m mod 6 < 3`, else
  `−1`) has absolute value at most `5` — six consecutive integers contribute `0`.
* `card_class_res`: every residue class mod `6` meets each colour class in at least `⌊len/6⌋`
  points.
-/

@[expose] public section

namespace CDRBicolour.Absorption.Refined

open Finset CDRBicolour.Prefix

/-- The sign of a residue. -/
def sgn6 (m : ℕ) : ℝ := if m % 6 < 3 then 1 else -1

theorem six_sum (m : ℕ) : ∑ i ∈ range 6, sgn6 (m + i) = 0 := by
  simp only [sum_range_succ, sum_range_zero, sgn6]
  have : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases h : m % 6 <;>
    simp only [show (m + 0) % 6 = m % 6 by simp, h,
      show (m + 1) % 6 = (m % 6 + 1) % 6 by omega, show (m + 2) % 6 = (m % 6 + 2) % 6 by omega,
      show (m + 3) % 6 = (m % 6 + 3) % 6 by omega, show (m + 4) % 6 = (m % 6 + 4) % 6 by omega,
      show (m + 5) % 6 = (m % 6 + 5) % 6 by omega] <;> norm_num

theorem abs_range_sgn_le (m len : ℕ) : |∑ i ∈ range len, sgn6 (m + i)| ≤ 5 := by
  induction len using Nat.strong_induction_on generalizing m with
  | _ len ih =>
  by_cases h6 : 6 ≤ len
  · obtain ⟨l, rfl⟩ : ∃ l, len = 6 + l := ⟨len - 6, by omega⟩
    rw [sum_range_add, six_sum, zero_add]
    have := ih l (by omega) (m + 6)
    simpa [add_assoc] using this
  · calc |∑ i ∈ range len, sgn6 (m + i)| ≤ ∑ i ∈ range len, |sgn6 (m + i)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ range len, (1 : ℝ) := by
          gcongr with i; unfold sgn6; split_ifs <;> norm_num
      _ = len := by simp
      _ ≤ 5 := by exact_mod_cast (show len ≤ 5 by omega)

variable {a b c : ℕ}

theorem mem_class_iff (X : Fin 3) (w : Fin (a + b + c)) :
    col3 a b c w = X ↔ cstart a b c X ≤ w.val ∧ w.val < cstart a b c X + clen a b c X := by
  constructor
  · rintro rfl; exact class_bounds w
  · rintro ⟨h1, h2⟩; exact col3_of_mem w.isLt h1 h2

/-- A sum over a colour class is a sum over an interval. -/
theorem sum_class (X : Fin 3) (g : ℕ → ℝ) :
    ∑ w ∈ univ.filter (fun w : Fin (a + b + c) => col3 a b c w = X), g w.val =
      ∑ i ∈ range (clen a b c X), g (cstart a b c X + i) := by
  have hend := class_end (a := a) (b := b) (c := c) X
  refine sum_bij' (fun w _ => w.val - cstart a b c X)
    (fun i hi => ⟨cstart a b c X + i, by
      have : i < clen a b c X := mem_range.mp hi
      omega⟩) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and, mem_class_iff] at hw
    simp only [mem_range]; omega
  · intro i hi
    simp only [mem_range] at hi
    simp only [mem_filter, mem_univ, true_and, mem_class_iff]
    omega
  · intro w hw
    simp only [mem_filter, mem_univ, true_and, mem_class_iff] at hw
    ext; simp only; omega
  · intro i hi; simp
  · intro w hw
    simp only [mem_filter, mem_univ, true_and, mem_class_iff] at hw
    congr 1; omega

/-- **Signs on a colour class.** -/
theorem abs_class_sgn_le (X : Fin 3) (t : ℕ) :
    |∑ w ∈ univ.filter (fun w : Fin (a + b + c) => col3 a b c w = X), sgn6 (t + w.val)| ≤ 5 := by
  rw [sum_class X (fun m => sgn6 (t + m))]
  simpa [add_assoc] using abs_range_sgn_le (t + cstart a b c X) (clen a b c X)

/-- Every residue appears `⌊len/6⌋` times in an interval of length `len`. -/
theorem card_range_res (m len r : ℕ) (hr : r < 6) :
    len / 6 ≤ #((range len).filter fun i => (m + i) % 6 = r) := by
  induction len using Nat.strong_induction_on generalizing m with
  | _ len ih =>
  by_cases h6 : 6 ≤ len
  · obtain ⟨l, rfl⟩ : ∃ l, len = 6 + l := ⟨len - 6, by omega⟩
    have hsplit : (range (6 + l)).filter (fun i => (m + i) % 6 = r) ⊇
        ((range l).filter (fun i => (m + 6 + i) % 6 = r)).map (addLeftEmbedding 6) ∪
          ((range 6).filter fun i => (m + i) % 6 = r) := by
      intro i hi
      simp only [mem_union, mem_map, mem_filter, mem_range, addLeftEmbedding_apply] at hi
      simp only [mem_filter, mem_range]
      rcases hi with ⟨k, ⟨hk, hk'⟩, rfl⟩ | ⟨hi, hi'⟩
      · exact ⟨by omega, by rw [← hk']; omega⟩
      · exact ⟨by omega, hi'⟩
    have hdisj : Disjoint (((range l).filter (fun i => (m + 6 + i) % 6 = r)).map
        (addLeftEmbedding 6)) ((range 6).filter fun i => (m + i) % 6 = r) := by
      rw [disjoint_left]
      intro i h1 h2
      simp only [mem_map, mem_filter, mem_range, addLeftEmbedding_apply] at h1 h2
      obtain ⟨k, -, rfl⟩ := h1
      omega
    have hone : 1 ≤ #((range 6).filter fun i => (m + i) % 6 = r) := by
      apply card_pos.mpr
      refine ⟨(r + 6 - m % 6) % 6, ?_⟩
      simp only [mem_filter, mem_range]
      constructor <;> omega
    have := card_le_card hsplit
    rw [card_union_of_disjoint hdisj, card_map] at this
    have ih' := ih l (by omega) (m + 6)
    omega
  · have : len / 6 = 0 := by omega
    omega

/-- **Refined class sizes.** -/
theorem card_class_res (X : Fin 3) {r : ℕ} (hr : r < 6) :
    clen a b c X / 6 ≤
      #(univ.filter fun w : Fin (a + b + c) => col3 a b c w = X ∧ w.val % 6 = r) := by
  have h := card_range_res (cstart a b c X) (clen a b c X) r hr
  have hend := class_end (a := a) (b := b) (c := c) X
  by_cases h0 : clen a b c X / 6 = 0
  · rw [h0]; exact Nat.zero_le _
  have hpos : 0 < a + b + c := by omega
  refine h.trans (card_le_card_of_injOn (fun i => (⟨(cstart a b c X + i) % (a + b + c),
      Nat.mod_lt _ hpos⟩ : Fin (a + b + c))) ?_ ?_)
  · intro i hi
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hi
    have hm : (cstart a b c X + i) % (a + b + c) = cstart a b c X + i := Nat.mod_eq_of_lt (by omega)
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, mem_class_iff, hm]
    exact ⟨⟨by omega, by omega⟩, hi.2⟩
  · intro i hi j hj he
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hi hj
    simp only [Fin.mk.injEq] at he
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
    omega

end CDRBicolour.Absorption.Refined
