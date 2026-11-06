/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.P2Types
public import CDRBicolour.Product

/-!
# Steiner quasigroup tables as witnesses (finite base)

`realises_of_table`: a table `T x y` (the third point of the block through `x ≠ y`) which is
symmetric, avoids its arguments, is involutive (`T x (T x y) = y`) and gives every triple
`{x, y, T x y}` exactly two colours for `col3 a b c`, yields `Realises a b c`.  The proof is
ordinary; in the Palomar branch concrete tables are checked by kernel reduction.

`decodeTable`: tables are stored as ASCII strings, two base-64 digits per unordered pair
`x < y`, in lexicographic order.
-/

@[expose] public section

namespace CDRBicolour.Base

open Finset CDRBicolour.Prefix

theorem realises_of_table (a b c : ℕ) (T : Fin (a + b + c) → Fin (a + b + c) → Fin (a + b + c))
    (h : ∀ x y, x ≠ y → T x y ≠ x ∧ T x y ≠ y ∧ T y x = T x y ∧ T x (T x y) = y ∧
      col3 a b c x + col3 a b c y + col3 a b c (T x y) ≠ 0) : Realises a b c := by
  classical
  -- the six values of `T` on a block
  have third : ∀ u v, u ≠ v →
      T u v = T u v ∧ T v u = T u v ∧ T u (T u v) = v ∧ T (T u v) u = v ∧
        T v (T u v) = u ∧ T (T u v) v = u := by
    intro u v huv
    obtain ⟨h1, h2, h3, h4, -⟩ := h u v huv
    obtain ⟨g1, g2, g3, g4, -⟩ := h v u (Ne.symm huv)
    rw [← g3] at g4
    refine ⟨rfl, g3.symm, h4, ?_, g4, ?_⟩
    · rw [(h u (T u v) (Ne.symm h1)).2.2.1]; exact h4
    · rw [(h v (T u v) (Ne.symm h2)).2.2.1]; exact g4
  let blocks : Finset (Finset (Fin (a + b + c))) :=
    ((univ : Finset (Fin (a + b + c) × Fin (a + b + c))).filter fun p => p.1 ≠ p.2).image
      fun p => ({p.1, p.2, T p.1 p.2} : Finset (Fin (a + b + c)))
  have mem_blocks : ∀ B, B ∈ blocks ↔ ∃ u v, u ≠ v ∧ B = {u, v, T u v} := by
    intro B
    simp only [blocks, mem_image, mem_filter, mem_univ, true_and, Prod.exists]
    constructor
    · rintro ⟨u, v, huv, rfl⟩; exact ⟨u, v, huv, rfl⟩
    · rintro ⟨u, v, huv, rfl⟩; exact ⟨u, v, huv, rfl⟩
  have card3 : ∀ u v, u ≠ v → ({u, v, T u v} : Finset (Fin (a + b + c))).card = 3 := by
    intro u v huv
    obtain ⟨h1, h2, -⟩ := h u v huv
    exact card_eq_three.2 ⟨u, v, T u v, huv, Ne.symm h1, Ne.symm h2, rfl⟩
  refine ⟨⟨blocks, ?_, ?_⟩, col3 a b c, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨u, v, huv, rfl⟩ := (mem_blocks B).1 hB
    exact card3 u v huv
  · intro x y hxy
    refine ⟨{x, y, T x y}, ⟨(mem_blocks _).2 ⟨x, y, hxy, rfl⟩, by simp, by simp⟩, ?_⟩
    rintro B ⟨hB, hxB, hyB⟩
    obtain ⟨u, v, huv, rfl⟩ := (mem_blocks B).1 hB
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := third u v huv
    -- the third point of `x, y` lies in the block
    have hT : T x y ∈ ({u, v, T u v} : Finset (Fin (a + b + c))) := by
      simp only [mem_insert, mem_singleton] at hxB hyB ⊢
      rcases hxB with rfl | rfl | rfl <;> rcases hyB with rfl | rfl | rfl
      all_goals first
        | exact absurd rfl hxy
        | (rw [e2]; simp)
        | (rw [e3]; simp)
        | (rw [e4]; simp)
        | (rw [e5]; simp)
        | (rw [e6]; simp)
        | simp
    have hsub : ({x, y, T x y} : Finset (Fin (a + b + c))) ⊆ {u, v, T u v} := by
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hxB
      · exact hyB
      · exact hT
    exact (eq_of_subset_of_card_le hsub (by rw [card3 u v huv, card3 x y hxy])).symm
  · intro B hB
    obtain ⟨u, v, huv, rfl⟩ := (mem_blocks B).1 hB
    simp only [image_insert, image_singleton]
    exact (fin3_card_two _ _ _).2 (h u v huv).2.2.2.2
  · rw [classSize, ← Fintype.card_subtype]; exact card_classA
  · rw [classSize, ← Fintype.card_subtype]; exact card_classB
  · rw [classSize, ← Fintype.card_subtype]; exact card_classC

/-- Base-64 digit. -/
def dig (u : UInt8) : ℕ :=
  if 48 ≤ u ∧ u ≤ 57 then u.toNat - 48
  else if 65 ≤ u ∧ u ≤ 90 then u.toNat - 55
  else if 97 ≤ u ∧ u ≤ 122 then u.toNat - 61
  else if u = 43 then 62 else 63

/-- Raw table entry for `x < y`. -/
def raw (s : ByteArray) (n x y : ℕ) : ℕ :=
  let i := 2 * (x * n - x * (x + 1) / 2 + (y - x - 1))
  dig (s.get! i) * 64 + dig (s.get! (i + 1))

/-- The decoded table. -/
def decodeTable (s : ByteArray) (n : ℕ) (hn : 0 < n) (x y : Fin n) : Fin n :=
  ⟨(if x.1 < y.1 then raw s n x y else raw s n y x) % n, Nat.mod_lt _ hn⟩

end CDRBicolour.Base
