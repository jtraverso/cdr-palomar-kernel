/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Label67b

/-!
# Pairing `Y` with `X`

`exists_pairing`: if `|X| = |Y|`, `A ⊆ Y`, `B ⊆ X`, and at most half of `Y` (resp. `X`) lies
outside `A` (resp. `B`), there is a bijection `σ : Y → X` sending all of `Y` but a set `Bad` with
`2 |Bad| ≤ |Y|` from `A` into `B`.
-/

@[expose] public section

namespace OneFactor

open Finset

variable {V : Type*} [DecidableEq V]

theorem exists_pairing (X Y A B : Finset V) (hXY : #X = #Y) (hA : A ⊆ Y) (hB : B ⊆ X)
    (hA2 : 2 * #(Y \ A) ≤ #Y) (hB2 : 2 * #(X \ B) ≤ #X) :
    ∃ (σ : V → V) (Bad : Finset V), Bad ⊆ Y ∧ 2 * #Bad ≤ #Y ∧ (∀ y ∈ Y, σ y ∈ X) ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, σ y = σ y' → y = y') ∧ (∀ y ∈ Y, y ∉ Bad → y ∈ A ∧ σ y ∈ B) := by
  obtain ⟨A', hA'A, hA'c⟩ := exists_subset_card_eq (s := A) (n := min #A #B) (min_le_left _ _)
  obtain ⟨B', hB'B, hB'c⟩ := exists_subset_card_eq (s := B) (n := min #A #B) (min_le_right _ _)
  have hA'Y : A' ⊆ Y := hA'A.trans hA
  have hB'X : B' ⊆ X := hB'B.trans hB
  have hc1 : #A' = #B' := by rw [hA'c, hB'c]
  have hc2 : #(Y \ A') = #(X \ B') := by
    rw [card_sdiff_of_subset hA'Y, card_sdiff_of_subset hB'X]; omega
  let e1 := Finset.equivOfCardEq hc1
  let e2 := Finset.equivOfCardEq hc2
  let σ : V → V := fun y =>
    if h : y ∈ A' then (e1 ⟨y, h⟩ : V) else if h2 : y ∈ Y \ A' then (e2 ⟨y, h2⟩ : V) else y
  have hσ1 : ∀ y (h : y ∈ A'), σ y = e1 ⟨y, h⟩ := fun y h => by simp only [σ, dif_pos h]
  have hσ2 : ∀ y (h : y ∈ Y \ A'), σ y = e2 ⟨y, h⟩ := fun y h => by
    simp only [σ, dif_neg (mem_sdiff.1 h).2, dif_pos h]
  refine ⟨σ, Y \ A', sdiff_subset, ?_, fun y hy => ?_, fun y hy y' hy' e => ?_, fun y hy hb => ?_⟩
  · have hAc : #(Y \ A) = #Y - #A := card_sdiff_of_subset hA
    have hBc : #(X \ B) = #X - #B := card_sdiff_of_subset hB
    have hA'' : #(Y \ A') = #Y - #A' := card_sdiff_of_subset hA'Y
    have hAY := card_le_card hA
    have hBX := card_le_card hB
    rw [hA'', hA'c]
    rcases le_total #A #B with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  · by_cases h : y ∈ A'
    · rw [hσ1 y h]; exact hB'X (e1 ⟨y, h⟩).2
    · have h2 : y ∈ Y \ A' := mem_sdiff.2 ⟨hy, h⟩
      rw [hσ2 y h2]; exact (mem_sdiff.1 (e2 ⟨y, h2⟩).2).1
  · by_cases h : y ∈ A' <;> by_cases h' : y' ∈ A'
    · rw [hσ1 y h, hσ1 y' h'] at e
      have := e1.injective (Subtype.ext e)
      exact congrArg Subtype.val this
    · have h2 : y' ∈ Y \ A' := mem_sdiff.2 ⟨hy', h'⟩
      rw [hσ1 y h, hσ2 y' h2] at e
      exact absurd (e ▸ (e1 ⟨y, h⟩).2) (mem_sdiff.1 (e2 ⟨y', h2⟩).2).2
    · have h2 : y ∈ Y \ A' := mem_sdiff.2 ⟨hy, h⟩
      rw [hσ2 y h2, hσ1 y' h'] at e
      exact absurd (e ▸ (e1 ⟨y', h'⟩).2) (mem_sdiff.1 (e2 ⟨y, h2⟩).2).2
    · have h2 : y ∈ Y \ A' := mem_sdiff.2 ⟨hy, h⟩
      have h2' : y' ∈ Y \ A' := mem_sdiff.2 ⟨hy', h'⟩
      rw [hσ2 y h2, hσ2 y' h2'] at e
      have := e2.injective (Subtype.ext e)
      exact congrArg Subtype.val this
  · have h : y ∈ A' := by
      by_contra h; exact hb (mem_sdiff.2 ⟨hy, h⟩)
    rw [hσ1 y h]
    exact ⟨hA'A h, hB'B (e1 ⟨y, h⟩).2⟩

end OneFactor
