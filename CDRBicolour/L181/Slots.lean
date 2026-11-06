/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.L181.Flip

/-!
# L181: ports, links and groups

For colours `p ≠ x`, every row `j` has two *slots* `(j, true)` (the `p`-slot) and `(j, false)`
(the `x`-slot).  The slot graph joins

* the two slots of a row (internal edge);
* `(j, b)` and `(j', b)` if `jj'` is an edge of colour `p` (`b = true`) or `x` (`b = false`);
* `(j, true)` and `(j', false)` if the old pairs `pz ∈ M j` and `xz ∈ M j'` collide (a *link*).

It has maximum degree `2`.  A slot of degree `1` is a *free port*: its colour is missing at the
row and it carries no link.  A connected component is a *group*; by `component_deficit` it has
`0` or `2` free ports.  The flip of the rows of a union of groups is legal (`Flip`), and

  `#(rows missing p) + #(free x-ports) = #(rows missing x) + #(free p-ports)`

in every group (`group_balance`).  This yields the port operator of L181 (`exists_flip_set`).
-/

@[expose] public section

namespace CDRBicolour.L181

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]

/-- A bijection-free equality of cardinalities through a relation which is functional in both
directions. -/
theorem card_eq_of_rel {α : Type*} (s t : Finset α) (R : α → α → Prop)
    (h1 : ∀ a ∈ s, ∃ b ∈ t, R a b) (h2 : ∀ b ∈ t, ∃ a ∈ s, R a b)
    (u1 : ∀ a b b', R a b → R a b' → b = b') (u2 : ∀ a a' b, R a b → R a' b → a = a') :
    s.card = t.card := by
  classical
  refine Finset.card_bij (fun a ha => Classical.choose (h1 a ha))
    (fun a ha => (Classical.choose_spec (h1 a ha)).1) ?_ ?_
  · intro a ha a' ha' h
    have h' := (Classical.choose_spec (h1 a' ha')).2
    rw [← h] at h'
    exact u2 a a' _ (Classical.choose_spec (h1 a ha)).2 h'
  · intro b hb
    obtain ⟨a, ha, hab⟩ := h2 b hb
    exact ⟨a, ha, u1 a _ _ (Classical.choose_spec (h1 a ha)).2 hab⟩

section Slots

variable (G : SimpleGraph Rw) [DecidableRel G.Adj] (p x : Cl) (χ : Sym2 Rw → Cl)
  (M : Rw → Finset (Sym2 Cl))

/-- Colour of a slot. -/
def slotCol (b : Bool) : Cl := if b then p else x

/-- Link between the `p`-port of `j` and the `x`-port of `j'`. -/
def IsLink (j j' : Rw) : Prop := j ≠ j' ∧ ∃ z, s(p, z) ∈ M j ∧ s(x, z) ∈ M j'

/-- The relation generating the slot graph. -/
def slotRel (σ ρ : Rw × Bool) : Prop :=
  (σ.1 = ρ.1 ∧ σ.2 ≠ ρ.2) ∨
    (σ.2 = ρ.2 ∧ G.Adj σ.1 ρ.1 ∧ χ s(σ.1, ρ.1) = slotCol p x σ.2) ∨
    (σ.2 = true ∧ ρ.2 = false ∧ IsLink p x M σ.1 ρ.1)

/-- The slot graph. -/
def slotGraph : SimpleGraph (Rw × Bool) := SimpleGraph.fromRel (slotRel G p x χ M)

noncomputable instance : DecidableRel (slotGraph G p x χ M).Adj := Classical.decRel _

variable {G p x χ M}

theorem slot_adj_internal (j : Rw) (b : Bool) : (slotGraph G p x χ M).Adj (j, b) (j, !b) := by
  rw [slotGraph, SimpleGraph.fromRel_adj]
  refine ⟨by cases b <;> simp, Or.inl (Or.inl ⟨rfl, by cases b <;> simp⟩)⟩

theorem slot_adj_colour {j j' : Rw} {b : Bool} (h : G.Adj j j')
    (hc : χ s(j, j') = slotCol p x b) : (slotGraph G p x χ M).Adj (j, b) (j', b) := by
  rw [slotGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun h' => ?_, Or.inl (Or.inr (Or.inl ⟨rfl, h, hc⟩))⟩
  have h1 : j = j' := congrArg Prod.fst h'
  rw [h1] at h
  exact G.irrefl h

theorem slot_adj_link {j j' : Rw} (h : IsLink p x M j j') :
    (slotGraph G p x χ M).Adj (j, true) (j', false) := by
  rw [slotGraph, SimpleGraph.fromRel_adj]
  exact ⟨by simp, Or.inl (Or.inr (Or.inr ⟨rfl, rfl, h⟩))⟩

theorem slot_adj_cases {j j' : Rw} {b b' : Bool} (h : (slotGraph G p x χ M).Adj (j, b) (j', b')) :
    (j = j' ∧ b' = !b) ∨
      (j ≠ j' ∧ ((b = b' ∧ G.Adj j j' ∧ χ s(j, j') = slotCol p x b) ∨
        (b = true ∧ b' = false ∧ IsLink p x M j j') ∨
        (b = false ∧ b' = true ∧ IsLink p x M j' j))) := by
  rw [slotGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨-, h⟩ := h
  simp only [slotRel] at h
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) | (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
  · left; exact ⟨h1, by cases b <;> cases b' <;> simp_all⟩
  · right; exact ⟨G.ne_of_adj h2, Or.inl ⟨h1, h2, h3⟩⟩
  · right; exact ⟨h3.1, Or.inr (Or.inl ⟨h1, h2, h3⟩)⟩
  · left; exact ⟨h1.symm, by cases b <;> cases b' <;> simp_all⟩
  · right
    refine ⟨(G.ne_of_adj h2).symm, Or.inl ⟨h1.symm, h2.symm, ?_⟩⟩
    rw [Sym2.eq_swap, h3, h1]
  · right; exact ⟨h3.1.symm, Or.inr (Or.inr ⟨h2, h1, h3⟩)⟩

/-! ### Uniqueness of the external neighbour -/

section Unique

variable (hχ : ProperOn G.edgeFinset χ) (hM : ∀ j, IsPartialPairing (M j) (miss G χ j))
  (hd : PairDisjoint M)
include hχ hM hd

theorem colour_unique {j j₁ j₂ : Rw} (h₁ : G.Adj j j₁) (h₂ : G.Adj j j₂)
    (hc : χ s(j, j₁) = χ s(j, j₂)) : j₁ = j₂ := by
  by_contra hne
  have he₁ : s(j, j₁) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.2 h₁
  have he₂ : s(j, j₂) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.2 h₂
  have hne' : s(j, j₁) ≠ s(j, j₂) := fun h => hne (Sym2.congr_right.1 h)
  have := hχ _ he₁ _ he₂ hne' hc
  exact Finset.disjoint_left.1 this (Sym2.mem_toFinset.2 (Sym2.mem_mk_left _ _))
    (Sym2.mem_toFinset.2 (Sym2.mem_mk_left _ _))

theorem pair_unique {j : Rw} {c z z' : Cl} (h : s(c, z) ∈ M j) (h' : s(c, z') ∈ M j) :
    z = z' :=
  Sym2.congr_right.1 ((hM j).2.2 _ h _ h' c (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _))

theorem owner_unique {j j' : Rw} {e : Sym2 Cl} (h : e ∈ M j) (h' : e ∈ M j') : j = j' := by
  by_contra hne
  exact Finset.disjoint_left.1 (hd j j' hne) h h'

theorem link_unique_right {j j₁ j₂ : Rw} (h₁ : IsLink p x M j j₁) (h₂ : IsLink p x M j j₂) :
    j₁ = j₂ := by
  obtain ⟨-, z₁, hp₁, hx₁⟩ := h₁
  obtain ⟨-, z₂, hp₂, hx₂⟩ := h₂
  have := pair_unique hχ hM hd hp₁ hp₂
  subst this
  exact owner_unique hχ hM hd hx₁ hx₂

theorem link_unique_left {j j₁ j₂ : Rw} (h₁ : IsLink p x M j₁ j) (h₂ : IsLink p x M j₂ j) :
    j₁ = j₂ := by
  obtain ⟨-, z₁, hp₁, hx₁⟩ := h₁
  obtain ⟨-, z₂, hp₂, hx₂⟩ := h₂
  have := pair_unique hχ hM hd hx₁ hx₂
  subst this
  exact owner_unique hχ hM hd hp₁ hp₂

omit hd in
theorem miss_of_pair {j : Rw} {c z : Cl} (h : s(c, z) ∈ M j) : c ∈ miss G χ j :=
  (hM j).2.1 _ h c (Sym2.mem_mk_left _ _)

omit hM hd in
theorem not_miss_of_adj {j j' : Rw} (h : G.Adj j j') : χ s(j, j') ∉ miss G χ j := by
  rw [mem_miss]; push_neg
  exact ⟨s(j, j'), SimpleGraph.mem_incidenceFinset.2 ⟨h, Sym2.mem_mk_left _ _⟩, rfl⟩

omit hM hd in
theorem exists_adj_of_not_miss {j : Rw} {c : Cl} (h : c ∉ miss G χ j) :
    ∃ j', G.Adj j j' ∧ χ s(j, j') = c := by
  rw [mem_miss] at h; push_neg at h
  obtain ⟨e, he, hc⟩ := h
  rw [SimpleGraph.mem_incidenceFinset] at he
  obtain ⟨heE, hje⟩ := he
  obtain ⟨j', rfl⟩ := Sym2.mem_iff_exists.1 hje
  exact ⟨j', heE, hc⟩

omit hM hd in
theorem false_of_adj_miss {j j' : Rw} {c : Cl} (h : G.Adj j j') (hc : χ s(j, j') = c)
    (hm : c ∈ miss G χ j) : False :=
  not_miss_of_adj hχ h (hc ▸ hm)

/-- The neighbours of a slot outside its own row: at most one. -/
theorem ext_unique {j : Rw} {b : Bool} {σ₁ σ₂ : Rw × Bool}
    (h₁ : (slotGraph G p x χ M).Adj (j, b) σ₁) (h₂ : (slotGraph G p x χ M).Adj (j, b) σ₂)
    (hn₁ : σ₁.1 ≠ j) (hn₂ : σ₂.1 ≠ j) : σ₁ = σ₂ := by
  obtain ⟨j₁, b₁⟩ := σ₁
  obtain ⟨j₂, b₂⟩ := σ₂
  simp only at hn₁ hn₂
  rcases slot_adj_cases h₁ with ⟨h, -⟩ | ⟨-, ⟨hb₁, ha₁, hc₁⟩ | ⟨hb, hb₁, hl₁⟩ | ⟨hb, hb₁, hl₁⟩⟩
  · exact absurd h.symm hn₁
  all_goals rcases slot_adj_cases h₂ with ⟨h, -⟩ | ⟨-, ⟨hb₂, ha₂, hc₂⟩ | ⟨hb', hb₂, hl₂⟩ | ⟨hb', hb₂, hl₂⟩⟩
  all_goals first | exact absurd h.symm hn₂ | skip
  · subst hb₁ hb₂
    rw [colour_unique hχ hM hd ha₁ ha₂ (hc₁.trans hc₂.symm)]
  · subst hb'
    obtain ⟨-, z, hz, -⟩ := hl₂
    exact (false_of_adj_miss hχ ha₁ hc₁ (miss_of_pair hχ hM hz)).elim
  · subst hb'
    obtain ⟨-, z, -, hz⟩ := hl₂
    exact (false_of_adj_miss hχ ha₁ hc₁ (miss_of_pair hχ hM hz)).elim
  · subst hb
    obtain ⟨-, z, hz, -⟩ := hl₁
    exact (false_of_adj_miss hχ ha₂ hc₂ (miss_of_pair hχ hM hz)).elim
  · subst hb₁ hb₂
    rw [link_unique_right hχ hM hd hl₁ hl₂]
  · subst hb; exact absurd hb' (by simp)
  · subst hb
    obtain ⟨-, z, -, hz⟩ := hl₁
    exact (false_of_adj_miss hχ ha₂ hc₂ (miss_of_pair hχ hM hz)).elim
  · subst hb; exact absurd hb' (by simp)
  · subst hb₁ hb₂
    rw [link_unique_left hχ hM hd hl₁ hl₂]

end Unique

end Slots

end CDRBicolour.L181
