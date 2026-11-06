/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Product

/-!
# The product on profiles

`realises_product` (CDR Theorem 2.4 on profiles): if `(a, b, c)` is realised with every class at
most half of the order (equivalently `max ≤ sum of the other two`) and `(x, y, z)` is realised
(classes may be empty), then

  `(x a + y b + z c, x b + y c + z a, x c + y a + z b)`

is realised, at order `(a + b + c)(x + y + z)`.
-/

@[expose] public section

namespace CDRBicolour

open Finset

variable {V V' : Type*} [DecidableEq V] [DecidableEq V']

/-- Transport of a Steiner triple system along a bijection. -/
def STS.map (P : STS V) (e : V ≃ V') : STS V' where
  blocks := P.blocks.image (Finset.map e.toEmbedding)
  card_eq_three := by
    intro B hB
    obtain ⟨B', hB', rfl⟩ := mem_image.1 hB
    rw [card_map]; exact P.card_eq_three B' hB'
  existsUnique_block := by
    intro x y hxy
    obtain ⟨B, ⟨hB, hx, hy⟩, hu⟩ := P.existsUnique_block (e.symm x) (e.symm y)
      (fun h => hxy (e.symm.injective h))
    refine ⟨B.map e.toEmbedding, ⟨mem_image.2 ⟨B, hB, rfl⟩, ?_, ?_⟩, ?_⟩
    · rw [mem_map]; exact ⟨_, hx, by simp⟩
    · rw [mem_map]; exact ⟨_, hy, by simp⟩
    · rintro Q ⟨hQ, hxQ, hyQ⟩
      obtain ⟨B', hB', rfl⟩ := mem_image.1 hQ
      rw [mem_map] at hxQ hyQ
      obtain ⟨x', hx', rfl⟩ := hxQ
      obtain ⟨y', hy', rfl⟩ := hyQ
      simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply] at hu
      rw [hu B' ⟨hB', hx', hy'⟩]

theorem isStrictBicolouring_map {P : STS V} {col : V → Fin 3} (h : IsStrictBicolouring P col)
    (e : V ≃ V') : IsStrictBicolouring (P.map e) (col ∘ e.symm) := by
  intro B hB
  obtain ⟨B', hB', rfl⟩ := mem_image.1 hB
  rw [map_eq_image, image_image]
  have : (col ∘ e.symm) ∘ e.toEmbedding = col := by ext v; simp
  rw [this]; exact h B' hB'

theorem classSize_comp_equiv [Fintype V] [Fintype V'] (col : V → Fin 3) (e : V ≃ V')
    (i : Fin 3) : classSize (col ∘ e.symm) i = classSize col i := by
  unfold classSize
  rw [← card_map e.symm.toEmbedding]
  congr 1; ext v
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.comp_apply,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨v', h, rfl⟩; exact h
  · intro h; exact ⟨e v, by simpa using h, by simp⟩

variable {U W : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

/-- Class sizes of the product colouring. -/
theorem classSize_prod (cu : U → Fin 3) (cw : W → Fin 3) (j : Fin 3) :
    classSize (fun z : W × U => cu z.2 - cw z.1) j =
      ∑ i : Fin 3, classSize cw i * classSize cu (j + i) := by
  classical
  unfold classSize
  rw [card_filter, Fintype.sum_prod_type]
  have hin : ∀ w, ∑ u, (if cu u - cw w = j then 1 else 0) =
      (univ.filter fun u => cu u = j + cw w).card := by
    intro w
    rw [card_filter]
    refine sum_congr rfl fun u _ => ?_
    have e : ∀ x k j : Fin 3, x - k = j ↔ x = j + k := by decide
    simp only [e]
  simp only [hin]
  have hsplit : ∀ w, (univ.filter fun u => cu u = j + cw w).card =
      ∑ i : Fin 3, if cw w = i then (univ.filter fun u => cu u = j + i).card else 0 := by
    intro w; rw [sum_ite_eq]; simp
  simp only [hsplit]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_filter, sum_const, smul_eq_mul]

/-- **CDR Theorem 2.4 on profiles.** -/
theorem realises_product {a b c x y z : ℕ} (h1 : Realises a b c)
    (hbal : 2 * a ≤ a + b + c ∧ 2 * b ≤ a + b + c ∧ 2 * c ≤ a + b + c) (h2 : Realises x y z) :
    Realises (x * a + y * b + z * c) (x * b + y * c + z * a) (x * c + y * a + z * b) := by
  classical
  obtain ⟨S, cu, hS, ha, hb, hc⟩ := h1
  obtain ⟨T, cw, hT, hx, hy, hz⟩ := h2
  have hbal' : ∀ i, 2 * classSize cu i ≤ Fintype.card (Fin (a + b + c)) := by
    intro i; rw [Fintype.card_fin]
    have : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
    rcases this with rfl | rfl | rfl
    · rw [ha]; exact hbal.1
    · rw [hb]; exact hbal.2.1
    · rw [hc]; exact hbal.2.2
  obtain ⟨P, hP⟩ := cdr_product S cu hS hbal' T cw hT
  set col : Fin (x + y + z) × Fin (a + b + c) → Fin 3 := fun p => cu p.2 - cw p.1
  have hcard : Fintype.card (Fin (x + y + z) × Fin (a + b + c)) =
      (x * a + y * b + z * c) + (x * b + y * c + z * a) + (x * c + y * a + z * b) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; ring
  let e := Fintype.equivFinOfCardEq hcard
  have hsz : ∀ j, classSize col j = ∑ i : Fin 3, classSize cw i * classSize cu (j + i) :=
    classSize_prod cu cw
  refine ⟨P.map e, col ∘ e.symm, isStrictBicolouring_map hP e, ?_, ?_, ?_⟩ <;>
    rw [classSize_comp_equiv, hsz, Fin.sum_univ_three] <;>
    simp only [hx, hy, hz] <;>
    norm_num [ha, hb, hc] <;> ring

end CDRBicolour
