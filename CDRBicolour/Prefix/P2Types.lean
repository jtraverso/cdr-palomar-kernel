/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.Counting
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The concrete vertex set `Fin (a+b+c)` with its three classes

`col v = 0` on `[0,a)`, `1` on `[a,a+b)`, `2` on `[a+b,a+b+c)`.
-/

@[expose] public section

namespace CDRBicolour.Prefix

open Finset

/-- The three-class colouring of `Fin (a+b+c)`. -/
def col3 (a b c : ℕ) (v : Fin (a + b + c)) : Fin 3 :=
  if v.val < a then 0 else if v.val < a + b then 1 else 2

variable {a b c : ℕ}

theorem col3_eq_zero {v : Fin (a + b + c)} : col3 a b c v = 0 ↔ v.val < a := by
  unfold col3; split_ifs with h1 h2 <;> simp_all

theorem col3_eq_one {v : Fin (a + b + c)} : col3 a b c v = 1 ↔ a ≤ v.val ∧ v.val < a + b := by
  unfold col3; split_ifs with h1 h2 <;> simp_all <;> omega

theorem col3_eq_two {v : Fin (a + b + c)} : col3 a b c v = 2 ↔ a + b ≤ v.val := by
  unfold col3; split_ifs with h1 h2 <;> simp_all <;> omega

/-- Number of points of `Fin n` whose value lies in `[lo, hi)`. -/
theorem card_filter_Ico (n lo hi : ℕ) (h : hi ≤ n) (hlh : lo ≤ hi) :
    (univ.filter fun v : Fin n => lo ≤ v.val ∧ v.val < hi).card = hi - lo := by
  rw [← Nat.card_Ico lo hi]
  refine card_bij (fun v _ => v.val) ?_ ?_ ?_
  · intro v hv; simp only [mem_filter, mem_univ, true_and] at hv; simp [hv.1, hv.2]
  · intro v _ w _ h; exact Fin.ext h
  · intro k hk
    simp only [mem_Ico] at hk
    exact ⟨⟨k, by omega⟩, by simp [hk.1, hk.2], rfl⟩

theorem card_classA : Fintype.card {v : Fin (a + b + c) // col3 a b c v = 0} = a := by
  rw [Fintype.card_subtype]
  have := card_filter_Ico (a + b + c) 0 a (by omega) (by omega)
  simp only [zero_le, true_and, Nat.sub_zero] at this
  refine (congrArg Finset.card (filter_congr ?_)).trans this; intro v _; simp [col3_eq_zero]

theorem card_classB : Fintype.card {v : Fin (a + b + c) // col3 a b c v = 1} = b := by
  rw [Fintype.card_subtype]
  have := card_filter_Ico (a + b + c) a (a + b) (by omega) (by omega)
  rw [show a + b - a = b by omega] at this
  refine (congrArg Finset.card (filter_congr ?_)).trans this; intro v _; simp [col3_eq_one]

theorem card_classC : Fintype.card {v : Fin (a + b + c) // col3 a b c v = 2} = c := by
  rw [Fintype.card_subtype]
  have := card_filter_Ico (a + b + c) (a + b) (a + b + c) (by omega) (by omega)
  rw [show a + b + c - (a + b) = c by omega] at this
  refine (congrArg Finset.card (filter_congr ?_)).trans this; intro v _; simp [col3_eq_two, Fin.is_lt]

end CDRBicolour.Prefix
