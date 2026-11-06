/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Positive-mode bridge: matching modes of a physical selector give triangles and tokens

Fix a host graph `G`, a root `v`, a finite set `E` of base edges lying in the link of `v`
(every endpoint adjacent to `v`), and the non-port vertices `W` of the physical selector.
The fuel is the SAME for all modes:

  `R = E ∪ {v w : w ∈ W}`.

For a matching mode `M ⊆ E` covering exactly `W ∪ S` (`S` the active ports), the
triangles `v x y` (`x y ∈ M`) are triangles of `G`, pairwise edge-disjoint, and

  `R ∪ {v u : u ∈ S} = (⋃_{xy ∈ M} E(vxy)) ⊔ (E \ M)`

as an exact disjoint union of edge sets (no signed cancellation; `E \ M` are the residual
base tokens).  The inputs `{v u : u ∈ S}` are disjoint from `R` when `S ∩ W = ∅`, and
`|R| = |E| + |W|`, `d_R(v) = |W|`.

This module only uses a matching mode of the PHYSICAL edge set; producing such modes from
an odd-subdivision embedding of a selector into a real link is a separate interface which
is not constructed here.
-/

namespace SelBridge

open Finset

variable {V : Type*} [DecidableEq V]

/-- Radial edges from the root. -/
def radial (v : V) (X : Finset V) : Finset (Sym2 V) := X.image (fun x => s(v, x))

lemma radial_card (v : V) (X : Finset V) : (radial v X).card = X.card := by
  unfold radial
  refine card_image_of_injOn ?_
  intro x _ y _ h
  rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · rw [h2, h1]

/-- The fixed fuel `R = E ∪ {v w : w ∈ W}`. -/
def fuel (v : V) (E : Finset (Sym2 V)) (W : Finset V) : Finset (Sym2 V) := E ∪ radial v W

/-- Edge set of the triangle `v x y` spanned by the base edge `x y`. -/
def triE (v : V) : Sym2 V → Finset (Sym2 V) :=
  Sym2.lift ⟨fun x y => {s(x, y), s(v, x), s(v, y)}, fun x y => by
    ext f; simp only [mem_insert, mem_singleton]; rw [Sym2.eq_swap]; tauto⟩

lemma mem_triE (v : V) (e f : Sym2 V) : f ∈ triE v e ↔ f = e ∨ ∃ x ∈ e, f = s(v, x) := by
  induction e using Sym2.ind with
  | h x y =>
    simp only [triE, Sym2.lift_mk, mem_insert, mem_singleton, Sym2.mem_iff]
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr ⟨x, Or.inl rfl, h⟩
      · exact Or.inr ⟨y, Or.inr rfl, h⟩
    · rintro (h | ⟨z, rfl | rfl, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

variable (G : SimpleGraph V) (v : V) (E : Finset (Sym2 V)) (W S : Finset V)
  (M : Finset (Sym2 V))

/-- Hypotheses: base edges are edges of `G` inside the link of `v`. -/
def InLink : Prop := ∀ e ∈ E, e ∈ G.edgeSet ∧ ∀ x ∈ e, G.Adj v x

/-- Hypotheses: `M ⊆ E` is a matching covering exactly `W ∪ S`. -/
def IsMode : Prop :=
  M ⊆ E ∧ (∀ x ∈ W ∪ S, (M.filter (fun e => x ∈ e)).card = 1) ∧
    (∀ x, x ∉ W ∪ S → ∀ e ∈ M, x ∉ e)

variable {G v E W S M}

omit [DecidableEq V] in
lemma root_not_mem (hE : InLink G v E) {e : Sym2 V} (he : e ∈ E) : v ∉ e := fun hv =>
  G.loopless.irrefl v ((hE e he).2 v hv)

lemma covered_of_mem (hM : IsMode E W S M) {e : Sym2 V} (he : e ∈ M) {x : V} (hx : x ∈ e) :
    x ∈ W ∪ S := by
  by_contra h; exact hM.2.2 x h e he hx

lemma unique_edge (hM : IsMode E W S M) {x : V} {e e' : Sym2 V} (he : e ∈ M) (he' : e' ∈ M)
    (hx : x ∈ e) (hx' : x ∈ e') : e = e' := by
  have h1 := hM.2.1 x (covered_of_mem hM he hx)
  rw [card_eq_one] at h1
  obtain ⟨a, ha⟩ := h1
  have h2 : e ∈ M.filter (fun e => x ∈ e) := mem_filter.mpr ⟨he, hx⟩
  have h3 : e' ∈ M.filter (fun e => x ∈ e) := mem_filter.mpr ⟨he', hx'⟩
  rw [ha, mem_singleton] at h2 h3
  rw [h2, h3]

/-- Every triangle of the mode is a triangle of `G`. -/
theorem mode_triangle (hE : InLink G v E) (hM : IsMode E W S M) {e : Sym2 V} (he : e ∈ M) :
    ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ G.Adj v x ∧ G.Adj v y := by
  have heE := hM.1 he
  induction e using Sym2.ind with
  | h x y =>
    exact ⟨x, y, rfl, (hE _ heE).1, (hE _ heE).2 x (Sym2.mem_mk_left x y),
      (hE _ heE).2 y (Sym2.mem_mk_right x y)⟩

/-- The triangles of a mode are pairwise edge-disjoint. -/
theorem mode_pairwiseDisjoint (hE : InLink G v E) (hM : IsMode E W S M) :
    (M : Set (Sym2 V)).PairwiseDisjoint (triE v) := by
  intro e he e' he' hne
  rw [Function.onFun, disjoint_left]
  intro f hf hf'
  have hvE := root_not_mem hE (hM.1 he)
  have hvE' := root_not_mem hE (hM.1 he')
  rw [mem_triE] at hf hf'
  rcases hf with rfl | ⟨x, hx, rfl⟩
  · rcases hf' with h | ⟨x', _, h⟩
    · exact hne h
    · exact hvE (h ▸ Sym2.mem_mk_left _ _)
  · rcases hf' with h | ⟨x', hx', h⟩
    · exact hvE' (h ▸ Sym2.mem_mk_left _ _)
    · have hxx : x = x' := by
        rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · exact absurd (h2 ▸ hx) hvE
      subst hxx
      exact hne (unique_edge hM he he' hx hx')

/-- The edges of all triangles of a mode: the base edges of `M` and the radial edges to
the covered vertices `W ∪ S`. -/
theorem mode_biUnion_triE (hM : IsMode E W S M) :
    M.biUnion (triE v) = M ∪ radial v (W ∪ S) := by
  ext f
  simp only [mem_biUnion, mem_union, radial, mem_image]
  constructor
  · rintro ⟨e, he, hf⟩
    rcases (mem_triE v e f).mp hf with rfl | ⟨x, hx, rfl⟩
    · exact Or.inl he
    · exact Or.inr ⟨x, mem_union.mp (covered_of_mem hM he hx), rfl⟩
  · rintro (hf | ⟨x, hx, rfl⟩)
    · exact ⟨f, hf, (mem_triE v f f).mpr (Or.inl rfl)⟩
    · have h1 := hM.2.1 x (mem_union.mpr hx)
      obtain ⟨e, he⟩ := card_pos.mp (by omega : 0 < (M.filter (fun e => x ∈ e)).card)
      rw [mem_filter] at he
      exact ⟨e, he.1, (mem_triE v e _).mpr (Or.inr ⟨x, he.2, rfl⟩)⟩

/-- Triangles and residual tokens are disjoint. -/
theorem mode_disjoint_tokens (hE : InLink G v E) (hM : IsMode E W S M) :
    Disjoint (M.biUnion (triE v)) (E \ M) := by
  rw [mode_biUnion_triE hM, disjoint_left]
  intro f hf hf'
  rw [mem_sdiff] at hf'
  rcases mem_union.mp hf with h | h
  · exact hf'.2 h
  · obtain ⟨x, _, rfl⟩ := mem_image.mp h
    exact root_not_mem hE hf'.1 (Sym2.mem_mk_left _ _)

/-- **Exact positive partition** `R ∪ {vu : u ∈ S} = E(D_S) ⊔ K_S`, with `K_S = E \ M`. -/
theorem mode_partition (hM : IsMode E W S M) :
    fuel v E W ∪ radial v S = M.biUnion (triE v) ∪ (E \ M) := by
  rw [mode_biUnion_triE hM]
  ext f
  simp only [fuel, radial, mem_union, mem_image, mem_sdiff]
  constructor
  · rintro ((hE | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
    · by_cases hfM : f ∈ M
      · exact Or.inl (Or.inl hfM)
      · exact Or.inr ⟨hE, hfM⟩
    · exact Or.inl (Or.inr ⟨x, Or.inl hx, rfl⟩)
    · exact Or.inl (Or.inr ⟨x, Or.inr hx, rfl⟩)
  · rintro ((hfM | ⟨x, hx | hx, rfl⟩) | ⟨hE, _⟩)
    · exact Or.inl (Or.inl (hM.1 hfM))
    · exact Or.inl (Or.inr ⟨x, hx, rfl⟩)
    · exact Or.inr ⟨x, hx, rfl⟩
    · exact Or.inl (Or.inl hE)

/-- The input edges `{vu : u ∈ S}` are disjoint from the fuel when ports are not
auxiliaries (`S ∩ W = ∅`). -/
theorem fuel_disjoint_inputs (hE : InLink G v E) (hSW : Disjoint S W) :
    Disjoint (fuel v E W) (radial v S) := by
  rw [disjoint_left]
  intro f hf hf'
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hf'
  rcases mem_union.mp hf with h | h
  · exact root_not_mem hE h (Sym2.mem_mk_left _ _)
  · obtain ⟨w, hw, hwu⟩ := mem_image.mp h
    have : w = u := by
      rcases Sym2.eq_iff.mp hwu with ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · rw [h2, h1]
    subst this
    exact disjoint_left.mp hSW hu hw

/-- Residual tokens are base edges in the link. -/
theorem tokens_sub (hE : InLink G v E) {f : Sym2 V} (hf : f ∈ E \ M) :
    f ∈ G.edgeSet ∧ ∀ x ∈ f, G.Adj v x :=
  hE f (mem_sdiff.mp hf).1

/-- **Counts.** `|R| = |E| + |W|`, and the radial part (`d_R(v)`) has `|W|` edges. -/
theorem fuel_card (hE : InLink G v E) :
    (fuel v E W).card = E.card + W.card ∧ (radial v W).card = W.card := by
  have hdisj : Disjoint E (radial v W) := by
    rw [disjoint_left]; intro f hf hf'
    obtain ⟨w, _, rfl⟩ := mem_image.mp hf'
    exact root_not_mem hE hf (Sym2.mem_mk_left _ _)
  refine ⟨?_, radial_card v W⟩
  rw [fuel, card_union_of_disjoint hdisj, radial_card]

/-- **Empty mode.** `R = E(D_∅) ⊔ K_∅` with the same fuel. -/
theorem empty_mode_partition (hE : InLink G v E) (hM : IsMode E W ∅ M) :
    fuel v E W = M.biUnion (triE v) ∪ (E \ M) ∧
      Disjoint (M.biUnion (triE v)) (E \ M) := by
  refine ⟨?_, mode_disjoint_tokens hE hM⟩
  have := mode_partition (v := v) hM
  simpa [radial] using this

/-- Bundled form for one mode: permitted triangles, pairwise disjointness, exact disjoint
edge union with the residual tokens. -/
theorem positive_mode (hE : InLink G v E) (hM : IsMode E W S M) (hSW : Disjoint S W) :
    (∀ e ∈ M, ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ G.Adj v x ∧ G.Adj v y) ∧
    (M : Set (Sym2 V)).PairwiseDisjoint (triE v) ∧
    Disjoint (fuel v E W) (radial v S) ∧
    fuel v E W ∪ radial v S = M.biUnion (triE v) ∪ (E \ M) ∧
    Disjoint (M.biUnion (triE v)) (E \ M) ∧
    (fuel v E W).card = E.card + W.card :=
  ⟨fun _ he => mode_triangle hE hM he, mode_pairwiseDisjoint hE hM,
    fuel_disjoint_inputs hE hSW, mode_partition hM, mode_disjoint_tokens hE hM,
    (fuel_card hE).1⟩

end SelBridge
