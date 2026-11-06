/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.ProductRealises

/-!
# L162 (three-fibre lift) and permutations of the classes

* `realises_012`: the STS(3) with sizes `(0, 1, 2)` (a two-colour outer input; the empty outer
  class is allowed by the product).
* `realises_lift` (L162): a realised balanced `(a, b, c)` gives `(b + 2c, c + 2a, a + 2b)` at
  order `3(a + b + c)`.
* `realises_perm`, `realises_swap`: realisation is invariant under permuting the classes.
-/

@[expose] public section

namespace CDRBicolour

open Finset

theorem realises_012 : Realises 0 1 2 := by
  classical
  refine ⟨⟨{univ}, by simp, ?_⟩, fun v => if v = 0 then 1 else 2, ?_, ?_, ?_, ?_⟩
  · intro x y _
    refine ⟨univ, ⟨mem_singleton_self _, mem_univ _, mem_univ _⟩, ?_⟩
    rintro B ⟨hB, -, -⟩; exact mem_singleton.1 hB
  · intro B hB; rw [mem_singleton.1 hB]; decide
  all_goals decide

/-- **L162.** -/
theorem realises_lift {a b c : ℕ} (h : Realises a b c)
    (hbal : 2 * a ≤ a + b + c ∧ 2 * b ≤ a + b + c ∧ 2 * c ≤ a + b + c) :
    Realises (b + 2 * c) (c + 2 * a) (a + 2 * b) := by
  have := realises_product h hbal realises_012
  simpa [add_comm, add_left_comm, mul_comm] using this

/-- Relabelling the colours by a permutation `π` (class `i` of the new system is class
`π.symm i` of the old one). -/
theorem realises_of_perm {a b c a' b' c' : ℕ} (h : Realises a b c) (π : Equiv.Perm (Fin 3))
    (hn : a + b + c = a' + b' + c')
    (h0 : ![a, b, c] (π.symm 0) = a') (h1 : ![a, b, c] (π.symm 1) = b')
    (h2 : ![a, b, c] (π.symm 2) = c') : Realises a' b' c' := by
  classical
  obtain ⟨S, col, hS, ha, hb, hc⟩ := h
  let e : Fin (a + b + c) ≃ Fin (a' + b' + c') := finCongr hn
  have hstrict : IsStrictBicolouring S (π ∘ col) := by
    intro B hB
    rw [← image_image, card_image_of_injective _ π.injective]; exact hS B hB
  have hsz : ∀ i, classSize (π ∘ col) i = ![a, b, c] (π.symm i) := by
    intro i
    have : classSize (π ∘ col) i = classSize col (π.symm i) := by
      unfold classSize; congr 1; ext v
      simp only [mem_filter, mem_univ, true_and, Function.comp_apply]
      exact ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩
    rw [this]
    have : π.symm i = 0 ∨ π.symm i = 1 ∨ π.symm i = 2 := by
      generalize π.symm i = k; revert k; decide
    rcases this with h | h | h <;> rw [h] <;> simp [ha, hb, hc]
  refine ⟨S.map e, (π ∘ col) ∘ e.symm, isStrictBicolouring_map hstrict e, ?_, ?_, ?_⟩
  · rw [classSize_comp_equiv, hsz, h0]
  · rw [classSize_comp_equiv, hsz, h1]
  · rw [classSize_comp_equiv, hsz, h2]

/-- The cyclic permutation `0 ↦ 2 ↦ 1 ↦ 0` (so that class `i` of the new system is class `i+1`
of the old one). -/
def rot3 : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

/-- Cyclic rotation of the classes. -/
theorem realises_rotate {a b c : ℕ} (h : Realises a b c) : Realises b c a :=
  realises_of_perm h rot3 (by omega) rfl rfl rfl

/-- Exchange of the first two classes. -/
theorem realises_swap {a b c : ℕ} (h : Realises a b c) : Realises b a c :=
  realises_of_perm h (Equiv.swap 0 1) (by omega) rfl rfl rfl

end CDRBicolour
