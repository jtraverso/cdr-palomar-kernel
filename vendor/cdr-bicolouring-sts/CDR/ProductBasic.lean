/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDR.Basic
public import CDR.ForbiddenCases

/-!
# Ingredients of the product theorem (Colbourn–Dinitz–Rosa, Theorem 2.4)

* `bicolourable3_of_equiv`: bicolourability transfers along a bijection of point sets.
* `Bicolourable3.swap₁₂`: exchanging the colours `1` and `2`.
* `good_two_of_forbidden`, `good_one_of_forbidden'`: in the product, the triples built from a
  pair of points of colour `k` and a point of colour `k + 2` (resp. `k + 1`) use an
  `(a, b, c)`-forbidden (resp. `(b, a, c)`-forbidden) latin square; the forbidden table is exactly
  what makes each such triple receive two colours.
-/

@[expose] public section

namespace CDR

open Finset

/-! ### Transfer and colour permutations -/

theorem isSTS_image_equiv {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) {B : Finset (Finset X)} (hB : IsSTS B) :
    IsSTS (B.image fun t => t.map e.toEmbedding) := by
  refine ⟨fun t ht => ?_, fun x y hxy => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := mem_image.1 ht
    rw [card_map, hB.card_eq s hs]
  · obtain ⟨t, ⟨ht, hx, hy⟩, huniq⟩ :=
      hB.pair (e.symm x) (e.symm y) (fun h => hxy (e.symm.injective h))
    refine ⟨t.map e.toEmbedding,
      ⟨mem_image_of_mem _ ht, mem_map_equiv.2 hx, mem_map_equiv.2 hy⟩, ?_⟩
    rintro t' ⟨ht', hx', hy'⟩
    obtain ⟨s, hs, rfl⟩ := mem_image.1 ht'
    rw [huniq s ⟨hs, mem_map_equiv.1 hx', mem_map_equiv.1 hy'⟩]

theorem card_colourClass_comp_equiv {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (e : X ≃ Y) (φ : X → Fin 3) (k : Fin 3) :
    #(colourClass (φ ∘ e.symm) k) = #(colourClass φ k) :=
  card_bij (fun y _ => e.symm y) (fun y hy => by simpa [colourClass] using hy)
    (fun y _ y' _ h => e.symm.injective h)
    (fun x hx => ⟨e x, by simpa [colourClass] using hx, by simp⟩)

theorem bicolourable3_of_equiv {X : Type*} [Fintype X] [DecidableEq X] {n a b c : ℕ}
    (e : X ≃ Fin n) {B : Finset (Finset X)} {φ : X → Fin 3} (hB : IsSTS B)
    (hφ : IsBicolouring B φ) (ha : #(colourClass φ 0) = a) (hb : #(colourClass φ 1) = b)
    (hc : #(colourClass φ 2) = c) : Bicolourable3 n a b c := by
  refine ⟨_, φ ∘ e.symm, isSTS_image_equiv e hB, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := mem_image.1 ht
    rw [map_eq_image, image_image, ← hφ s hs]
    congr 1
    ext x
    simp
  · rw [card_colourClass_comp_equiv, ha]
  · rw [card_colourClass_comp_equiv, hb]
  · rw [card_colourClass_comp_equiv, hc]

theorem colourClass_comp_perm {X : Type*} [Fintype X] [DecidableEq X] (σ : Equiv.Perm (Fin 3))
    (φ : X → Fin 3) (k : Fin 3) : colourClass (σ ∘ φ) k = colourClass φ (σ.symm k) := by
  ext x
  simp only [colourClass, mem_filter, mem_univ, true_and, Function.comp_apply]
  rw [Equiv.eq_symm_apply]

theorem Bicolourable3.swap₁₂ {n a b c : ℕ} (h : Bicolourable3 n a b c) :
    Bicolourable3 n a c b := by
  obtain ⟨B, φ, hB, hφ, ha, hb, hc⟩ := h
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  refine ⟨B, σ ∘ φ, hB, fun t ht => ?_, ?_, ?_, ?_⟩
  · rw [← image_image, card_image_of_injective _ σ.injective]
    exact hφ t ht
  · rw [colourClass_comp_perm, show σ.symm 0 = 0 by decide, ha]
  · rw [colourClass_comp_perm, show σ.symm 1 = 2 by decide, hc]
  · rw [colourClass_comp_perm, show σ.symm 2 = 1 by decide, hb]

/-! ### Forbidden squares give two-coloured triples -/

theorem good_two_of_forbidden {u : ℕ} {φ : Fin u → Fin 3} {L : Fin u → Fin u → Fin u}
    (hL : IsForbiddenLatin φ L) (r s : Fin u) :
    #({φ r, φ s, φ (L r s) - 2} : Finset (Fin 3)) = 2 := by
  have key : ∀ α β γ : Fin 3, γ ≠ forbiddenClass α β →
      #({α, β, γ - 2} : Finset (Fin 3)) = 2 := by decide
  exact key _ _ _ (hL.2 r s)

theorem good_one_of_forbidden' {u : ℕ} {φ : Fin u → Fin 3} {L : Fin u → Fin u → Fin u}
    (hL : IsForbiddenLatin (fun p => 1 - φ p) L) (r s : Fin u) :
    #({φ r, φ s, φ (L r s) - 1} : Finset (Fin 3)) = 2 := by
  have key : ∀ α β γ : Fin 3, 1 - γ ≠ forbiddenClass (1 - α) (1 - β) →
      #({α, β, γ - 1} : Finset (Fin 3)) = 2 := by decide
  exact key _ _ _ (hL.2 r s)

theorem cls_eq_colourClass {X : Type*} [Fintype X] [DecidableEq X] (φ : X → Fin 3) (k : Fin 3) :
    cls φ k = colourClass φ k := rfl

theorem cls_one_sub {X : Type*} [Fintype X] [DecidableEq X] (φ : X → Fin 3) (k : Fin 3) :
    cls (fun p => 1 - φ p) k = colourClass φ (1 - k) := by
  ext x
  simp only [cls, colourClass, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    rw [← h]
    exact (sub_sub_cancel _ _).symm
  · intro h
    rw [h]
    exact sub_sub_cancel _ _

/-- The two forbidden latin squares used in Theorem 2.4, from Lemma 2.3. -/
theorem exists_good_squares {u : ℕ} {φ : Fin u → Fin 3}
    (ha : #(colourClass φ 0) ≤ #(colourClass φ 2)) (hb : #(colourClass φ 1) ≤ #(colourClass φ 2))
    (hc : #(colourClass φ 2) ≤ #(colourClass φ 0) + #(colourClass φ 1)) :
    ∃ L₁ L₂ : Fin u → Fin u → Fin u, IsLatinSquare L₁ ∧ IsLatinSquare L₂ ∧
      (∀ r s, #({φ r, φ s, φ (L₁ r s) - 1} : Finset (Fin 3)) = 2) ∧
      (∀ r s, #({φ r, φ s, φ (L₂ r s) - 2} : Finset (Fin 3)) = 2) := by
  obtain ⟨L₂, hL₂⟩ := exists_forbidden_latin (lab := φ) ha hb hc
  have h0 : cls (fun p => 1 - φ p) 0 = colourClass φ 1 := by rw [cls_one_sub]; rfl
  have h1 : cls (fun p => 1 - φ p) 1 = colourClass φ 0 := by rw [cls_one_sub]; rfl
  have h2 : cls (fun p => 1 - φ p) 2 = colourClass φ 2 := by rw [cls_one_sub]; rfl
  obtain ⟨L₁, hL₁⟩ := exists_forbidden_latin (lab := fun p => 1 - φ p)
    (by rw [h0, h2]; exact hb) (by rw [h1, h2]; exact ha) (by rw [h0, h1, h2]; omega)
  exact ⟨L₁, L₂, hL₁.1, hL₂.1, good_one_of_forbidden' hL₁, good_two_of_forbidden hL₂⟩

end CDR
