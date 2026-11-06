/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Corners.Necessary
public import CDRBicolour.ProductRealises

/-!
# Relabelling the classes (item 3, corners)

A permutation `π` of the colours with matching class sizes is realised by a bijection of the
points (`exists_relabel`); it transports a strictly bicoloured STS and its type counts
(`typeCount_map`).  With `π = (1 2)` this exchanges the profiles `(a, b, c)` and `(a, c, b)` and
the counts `N_AAC ↔ N_AAB`, so the upper corner of `N_AAC` is the lower corner of `(a, c, b)`.
-/

@[expose] public section

noncomputable section

open Classical

namespace CDRBicolour.Absorption.Corners

open Finset CDRBicolour.Prefix CDRBicolour.Absorption CDRBicolour.BlockTypes

/-- A permutation of the colours with matching class sizes is realised by a bijection. -/
theorem exists_relabel {V V' : Type*} [Fintype V] [Fintype V'] (col : V → Fin 3)
    (col' : V' → Fin 3) (π : Equiv.Perm (Fin 3)) (h : ∀ i, classSize col' (π i) = classSize col i) :
    ∃ e : V ≃ V', ∀ v, col' (e v) = π (col v) := by
  have eqv : ∀ i, {v // col v = i} ≃ {v' // col' v' = π i} := fun i =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact (h i).symm)
  let e : V ≃ V' := (Equiv.sigmaFiberEquiv col).symm.trans
    ((Equiv.sigmaCongrRight eqv).trans
      ((Equiv.sigmaCongrLeft (β := fun j => {v' // col' v' = j}) π).trans
        (Equiv.sigmaFiberEquiv col')))
  refine ⟨e, fun v => ?_⟩
  simp only [e, Equiv.trans_apply, Equiv.sigmaFiberEquiv_apply]
  exact (eqv (col v) ⟨v, rfl⟩).2 ▸ rfl

/-- Colour counts are transported. -/
theorem cnt_map {V V' : Type*} [DecidableEq V] [DecidableEq V'] {col : V → Fin 3}
    {col' : V' → Fin 3} {π : Equiv.Perm (Fin 3)} {e : V ≃ V'} (he : ∀ v, col' (e v) = π (col v))
    (i : Fin 3) (B : Finset V) : cnt col' (π i) (B.map e.toEmbedding) = cnt col i B := by
  unfold cnt
  rw [filter_map, card_map]
  congr 1
  ext v
  simp [he, π.injective.eq_iff]

/-- **Type counts are transported.** -/
theorem typeCount_map {V V' : Type*} [DecidableEq V] [DecidableEq V'] (S : STS V) {col : V → Fin 3}
    {col' : V' → Fin 3} {π : Equiv.Perm (Fin 3)} {e : V ≃ V'} (he : ∀ v, col' (e v) = π (col v))
    (i j : Fin 3) : typeCount (S.map e) col' (π i) (π j) = typeCount S col i j := by
  unfold typeCount STS.map
  rw [filter_image, card_image_of_injOn]
  · congr 1
    ext B
    simp only [mem_filter, Function.comp_apply, cnt_map he]
  · intro B _ B' _ hBB
    exact Finset.map_injective e.toEmbedding hBB

theorem strict_map {V V' : Type*} [DecidableEq V] [DecidableEq V'] {S : STS V} {col : V → Fin 3}
    {col' : V' → Fin 3} {π : Equiv.Perm (Fin 3)} {e : V ≃ V'} (he : ∀ v, col' (e v) = π (col v))
    (h : IsStrictBicolouring S col) : IsStrictBicolouring (S.map e) col' := by
  intro B hB
  obtain ⟨B', hB', rfl⟩ := mem_image.1 hB
  have : (B'.map e.toEmbedding).image col' = (B'.image col).image π := by
    ext k
    simp only [mem_image, mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨col v, ⟨v, hv, rfl⟩, (he v).symm⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨e v, ⟨v, hv, rfl⟩, he v⟩
  rw [this, card_image_of_injective _ π.injective]; exact h B' hB'

/-- The exchange of the last two classes. -/
def sw12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem classSize_col3 (a b c : ℕ) (i : Fin 3) : classSize (col3 a b c) i = ![a, b, c] i := by
  rw [← csz_col3]; rfl

/-- **Exchanging `B` and `C`.** -/
theorem exists_swap12 (a b c : ℕ) :
    ∃ e : Fin (a + b + c) ≃ Fin (a + c + b), ∀ v, col3 a c b (e v) = sw12 (col3 a b c v) := by
  refine exists_relabel _ _ sw12 fun i => ?_
  rw [classSize_col3, classSize_col3]
  fin_cases i <;> rfl

end CDRBicolour.Absorption.Corners
