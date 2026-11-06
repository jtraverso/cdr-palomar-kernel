/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDR.ProductBasic

/-!
# The product theorem (Colbourn–Dinitz–Rosa, Theorem 2.4)

**Theorem 2.4.** If there is an `(a, b, c)`-bicolourable STS(`u`) with `c = max(a, b, c)` and
`c ≤ a + b`, and an `(x, y, z)`-bicolourable STS(`v`), then there is an
`(ax + by + cz, ay + bz + cx, az + bx + cy)`-bicolourable STS(`uv`) (`bicolourable3_mul`).

Construction, on the points `Fin v × Fin u` (`v` copies `V_i = {i} × Fin u` of the first
system): the point `(i, p)` gets colour `φ p − ψ i`, where `φ`, `ψ` are the bicolourings of the
two systems. The blocks are the copies of the blocks of the first system in each `V_i`
(`internal`), and, for every block `{f, g, h}` of the second system with `ψ f = ψ g ≠ ψ h`
(oriented by `f < g`), the triples `{(f, r), (g, s), (h, L r s)}` for all `r, s` (`cross`),
where `L` is an `(a, b, c)`-forbidden latin square if `ψ h = ψ f + 2` and a `(b, a, c)`-forbidden
one if `ψ h = ψ f + 1` (Lemma 2.3).
-/

@[expose] public section

namespace CDR

open Finset

variable {u v : ℕ}

/-- The distinct points of a three-element set. -/
theorem ne_of_card_three {α : Type*} [DecidableEq α] {f g h : α} (hc : #({f, g, h} : Finset α) = 3) :
    f ≠ g ∧ f ≠ h ∧ g ≠ h := by
  refine ⟨fun hfg => ?_, fun hfh => ?_, fun hgh => ?_⟩
  · subst hfg
    have := card_le_two (a := f) (b := h)
    simp at hc
    have h2 := card_insert_le f ({h} : Finset α)
    rw [card_singleton] at h2
    omega
  · subst hfh
    have h2 : ({f, g, f} : Finset α) = {f, g} := by ext; simp; tauto
    rw [h2] at hc
    have := card_insert_le f ({g} : Finset α)
    rw [card_singleton] at this
    omega
  · subst hgh
    have h2 : ({f, g, g} : Finset α) = {f, g} := by ext; simp
    rw [h2] at hc
    have := card_insert_le f ({g} : Finset α)
    rw [card_singleton] at this
    omega

/-- A block `{f, g, h}` of the second system, oriented: `f < g` have the same colour, `h` another
one. -/
def Oriented (B₂ : Finset (Finset (Fin v))) (ψ : Fin v → Fin 3) (f g h : Fin v) : Prop :=
  {f, g, h} ∈ B₂ ∧ f < g ∧ ψ f = ψ g ∧ ψ h ≠ ψ f

instance (B₂ : Finset (Finset (Fin v))) (ψ : Fin v → Fin 3) (f g h : Fin v) :
    Decidable (Oriented B₂ ψ f g h) := by
  unfold Oriented
  infer_instance

/-- The latin square used for an oriented block. -/
def sel (ψ : Fin v → Fin 3) (L₁ L₂ : Fin u → Fin u → Fin u) (f h : Fin v) :
    Fin u → Fin u → Fin u :=
  if ψ h - ψ f = 1 then L₁ else L₂

/-- The triple of the product attached to an oriented block and a pair `(r, s)`. -/
def crossTriple (ψ : Fin v → Fin 3) (L₁ L₂ : Fin u → Fin u → Fin u) (f g h : Fin v)
    (r s : Fin u) : Finset (Fin v × Fin u) :=
  {(f, r), (g, s), (h, sel ψ L₁ L₂ f h r s)}

/-- The embedding of the `i`-th copy. -/
def copyEmb (i : Fin v) : Fin u ↪ Fin v × Fin u := ⟨fun p => (i, p), fun _ _ h => (Prod.mk.inj h).2⟩

/-- The copies of the blocks of the first system. -/
def internal (B₁ : Finset (Finset (Fin u))) : Finset (Finset (Fin v × Fin u)) :=
  univ.biUnion fun i => B₁.image fun t => t.map (copyEmb i)

/-- The triples built on the oriented blocks of the second system. -/
def cross (B₂ : Finset (Finset (Fin v))) (ψ : Fin v → Fin 3) (L₁ L₂ : Fin u → Fin u → Fin u) :
    Finset (Finset (Fin v × Fin u)) :=
  (univ.filter fun w : Fin v × Fin v × Fin v => Oriented B₂ ψ w.1 w.2.1 w.2.2).biUnion
    fun w => univ.image fun rs : Fin u × Fin u => crossTriple ψ L₁ L₂ w.1 w.2.1 w.2.2 rs.1 rs.2

/-- The blocks of the product system. -/
def prodBlocks (B₁ : Finset (Finset (Fin u))) (B₂ : Finset (Finset (Fin v))) (ψ : Fin v → Fin 3)
    (L₁ L₂ : Fin u → Fin u → Fin u) : Finset (Finset (Fin v × Fin u)) :=
  internal B₁ ∪ cross B₂ ψ L₁ L₂

/-- The colouring of the product system. -/
def prodColour (φ : Fin u → Fin 3) (ψ : Fin v → Fin 3) (q : Fin v × Fin u) : Fin 3 :=
  φ q.2 - ψ q.1

theorem mem_internal {B₁ : Finset (Finset (Fin u))} {t : Finset (Fin v × Fin u)} :
    t ∈ internal B₁ ↔ ∃ i, ∃ s ∈ B₁, t = s.map (copyEmb i) := by
  simp only [internal, mem_biUnion, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨i, s, hs, rfl⟩
    exact ⟨i, s, hs, rfl⟩
  · rintro ⟨i, s, hs, rfl⟩
    exact ⟨i, s, hs, rfl⟩

theorem mem_cross {B₂ : Finset (Finset (Fin v))} {ψ : Fin v → Fin 3}
    {L₁ L₂ : Fin u → Fin u → Fin u} {t : Finset (Fin v × Fin u)} :
    t ∈ cross B₂ ψ L₁ L₂ ↔
      ∃ f g h, Oriented B₂ ψ f g h ∧ ∃ r s, t = crossTriple ψ L₁ L₂ f g h r s := by
  simp only [cross, mem_biUnion, mem_filter, mem_univ, true_and, mem_image, Prod.exists]
  constructor
  · rintro ⟨f, g, h, hor, r, s, rfl⟩
    exact ⟨f, g, h, hor, r, s, rfl⟩
  · rintro ⟨f, g, h, hor, r, s, rfl⟩
    exact ⟨f, g, h, hor, r, s, rfl⟩

theorem mem_copy {s : Finset (Fin u)} {i j : Fin v} {q : Fin u} :
    (j, q) ∈ s.map (copyEmb i) ↔ j = i ∧ q ∈ s := by
  rw [mem_map]
  constructor
  · rintro ⟨p, hp, he⟩
    simp only [copyEmb, Function.Embedding.coeFn_mk, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, hp⟩
  · rintro ⟨rfl, hq⟩
    exact ⟨q, hq, rfl⟩

theorem mem_crossTriple {ψ : Fin v → Fin 3} {L₁ L₂ : Fin u → Fin u → Fin u} {f g h j : Fin v}
    {r s q : Fin u} :
    (j, q) ∈ crossTriple ψ L₁ L₂ f g h r s ↔
      (j = f ∧ q = r) ∨ (j = g ∧ q = s) ∨ (j = h ∧ q = sel ψ L₁ L₂ f h r s) := by
  simp [crossTriple]

theorem sel_isLatinSquare {ψ : Fin v → Fin 3} {L₁ L₂ : Fin u → Fin u → Fin u}
    (hL₁ : IsLatinSquare L₁) (hL₂ : IsLatinSquare L₂) (f h : Fin v) :
    IsLatinSquare (sel ψ L₁ L₂ f h) := by
  unfold sel
  split_ifs
  · exact hL₁
  · exact hL₂

/-- An oriented block has three distinct points. -/
theorem Oriented.distinct {B₂ : Finset (Finset (Fin v))} {ψ : Fin v → Fin 3} (h₂ : IsSTS B₂)
    {f g h : Fin v} (hor : Oriented B₂ ψ f g h) : f ≠ g ∧ f ≠ h ∧ g ≠ h :=
  ne_of_card_three (h₂.card_eq _ hor.1)

/-- **The orientation of a block is unique.** -/
theorem Oriented.unique {B₂ : Finset (Finset (Fin v))} {ψ : Fin v → Fin 3} (h₂ : IsSTS B₂)
    {f g h f' g' h' : Fin v} (hor : Oriented B₂ ψ f g h) (hor' : Oriented B₂ ψ f' g' h')
    (heq : ({f, g, h} : Finset (Fin v)) = {f', g', h'}) : f = f' ∧ g = g' ∧ h = h' := by
  obtain ⟨d1, d2, d3⟩ := hor.distinct h₂
  obtain ⟨d1', d2', d3'⟩ := hor'.distinct h₂
  obtain ⟨-, hfg, hψfg, hψh⟩ := hor
  obtain ⟨-, hfg', hψfg', hψh'⟩ := hor'
  have mf : f' = f ∨ f' = g ∨ f' = h := by
    have : f' ∈ ({f, g, h} : Finset (Fin v)) := by rw [heq]; simp
    simpa using this
  have mg : g' = f ∨ g' = g ∨ g' = h := by
    have : g' ∈ ({f, g, h} : Finset (Fin v)) := by rw [heq]; simp
    simpa using this
  have mh : h' = f ∨ h' = g ∨ h' = h := by
    have : h' ∈ ({f, g, h} : Finset (Fin v)) := by rw [heq]; simp
    simpa using this
  rcases mf with rfl | rfl | rfl <;> rcases mg with rfl | rfl | rfl <;>
    rcases mh with rfl | rfl | rfl
  all_goals first
    | exact ⟨rfl, rfl, rfl⟩
    | exact absurd rfl d1'
    | exact absurd rfl d2'
    | exact absurd rfl d3'
    | exact absurd (hfg.trans hfg') (lt_irrefl _)
    | exact absurd (hψfg.trans hψfg'.symm) (Ne.symm hψh)
    | exact absurd (hψfg'.symm.trans hψfg.symm) hψh
    | exact absurd hψfg' (fun h' => hψh (h'.symm.trans hψfg.symm).symm)
    | exact absurd hψfg' (fun h' => hψh (h'.trans hψfg.symm))
    | exact absurd hψfg'.symm hψh
    | exact absurd hψfg' hψh
    | exact absurd (hψfg'.trans hψfg) (Ne.symm hψh)
    | exact absurd (hψfg.trans hψfg') hψh
    | exact absurd (hψfg.symm.trans hψfg') hψh
    | (exfalso; simp_all)

end CDR
