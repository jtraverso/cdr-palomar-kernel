/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Balanced.RSc
public import LeanPool.Vizing.Main

/-!
# Rudašová–Soták, Theorem 3.1, for colourings of the line graph

An edge colouring is a colouring `C : G.lineGraph.Coloring (Fin k)`. The *palette* of `v` is the
set of colours of the edges at `v`; `C` is *strong* if distinct vertices have distinct palettes,
and *equitable* if its colour classes differ in size by at most one.

`exists_equitable_strong`: if `G` has a strong `m`-colouring and `m ≤ k`, then it has an
equitable strong `k`-colouring (**Rudašová–Soták 2008, Theorem 3.1**, with `k ≥ s(G)`).
-/

@[expose] public section

namespace Balanced

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

/-- The set of colours of the edges at `v`. -/
def palette (C : G.lineGraph.Coloring (Fin k)) (v : V) : Set (Fin k) :=
  {θ | ∃ e : G.edgeSet, v ∈ (e : Sym2 V) ∧ C e = θ}

/-- Distinct vertices see distinct sets of colours. -/
def IsStrong (C : G.lineGraph.Coloring (Fin k)) : Prop := Function.Injective (palette C)

/-- The colour classes differ in size by at most one. -/
def IsEquitable (C : G.lineGraph.Coloring (Fin k)) : Prop :=
  ∀ x y : Fin k, (C.colorClass x).ncard ≤ (C.colorClass y).ncard + 1

section Dec

variable [DecidableRel G.Adj]

/-! ### From a line-graph colouring to a partial edge colouring -/

/-- The partial edge colouring with the colours of `C`. -/
noncomputable def ofColoring (C : G.lineGraph.Coloring (Fin k)) : PEC G (Fin k) where
  col u v := if h : G.Adj u v then some (C ⟨s(u, v), h⟩) else none
  col_symm u v := by
    by_cases h : G.Adj u v
    · rw [dif_pos h, dif_pos h.symm]
      congr 2
      exact Subtype.ext Sym2.eq_swap
    · rw [dif_neg h, dif_neg fun h' => h h'.symm]
  col_adj {u v γ} h := by
    by_cases h' : G.Adj u v
    · exact h'
    · rw [dif_neg h'] at h; cases h
  col_proper {u v w γ} h₁ h₂ := by
    by_cases hv : G.Adj u v
    · by_cases hw : G.Adj u w
      · rw [dif_pos hv] at h₁
        rw [dif_pos hw] at h₂
        by_contra hvw
        have hadj : G.lineGraph.Adj ⟨s(u, v), hv⟩ ⟨s(u, w), hw⟩ := by
          rw [lineGraph_adj_iff_exists]
          refine ⟨fun h => hvw ?_, u, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
          have h' := congrArg Subtype.val h
          simp only at h'
          rcases Sym2.eq_iff.1 h' with ⟨-, h⟩ | ⟨h1, h2⟩
          · exact h
          · rw [← h1, h2]
        exact C.valid hadj (Option.some_injective _ (h₁.trans h₂.symm))
      · rw [dif_neg hw] at h₂; cases h₂
    · rw [dif_neg hv] at h₁; cases h₁

theorem ofColoring_col {C : G.lineGraph.Coloring (Fin k)} {u v : V} {θ : Fin k} :
    (ofColoring C).col u v = some θ ↔ ∃ h : G.Adj u v, C ⟨s(u, v), h⟩ = θ := by
  simp only [ofColoring]
  by_cases h : G.Adj u v
  · rw [dif_pos h]; simp [h]
  · rw [dif_neg h]; simp [h]

theorem total_ofColoring (C : G.lineGraph.Coloring (Fin k)) : Total (ofColoring C) := by
  intro u v h
  simp only [ofColoring, dif_pos h, ne_eq, reduceCtorEq, not_false_eq_true]

/-- Membership in `S(v)` is membership in the palette. -/
theorem mem_colSet_ofColoring {C : G.lineGraph.Coloring (Fin k)} {v : V} {θ : Fin k} :
    θ ∈ colSet (ofColoring C) v ↔ θ ∈ palette C v := by
  rw [mem_colSet]
  simp only [IsFree, not_forall, not_not, ofColoring_col, palette, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, h, rfl⟩
    exact ⟨⟨s(v, u), h⟩, Sym2.mem_mk_left _ _, rfl⟩
  · rintro ⟨⟨e, he⟩, hv, rfl⟩
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hv
    exact ⟨u, he, rfl⟩

theorem strong_ofColoring {C : G.lineGraph.Coloring (Fin k)} (hC : IsStrong C) :
    Strong (ofColoring C) := by
  refine ⟨total_ofColoring C, fun v w h => hC ?_⟩
  ext θ
  rw [← mem_colSet_ofColoring, ← mem_colSet_ofColoring, h]

/-! ### From a total partial edge colouring to a line-graph colouring -/

theorem lineGraphColoring_eq {c : PEC G (Fin k)} (htot : Total c) (e : G.edgeSet) (θ : Fin k) :
    c.lineGraphColoring htot e = θ ↔ c.edgeOption e.1 = some θ := by
  have h := c.edgeOption_eq_some_edgeColor htot e
  change c.edgeColor htot e = θ ↔ _
  rw [h]
  exact ⟨fun h => h ▸ rfl, fun h => Option.some_injective _ h⟩

theorem mem_palette_lineGraphColoring {c : PEC G (Fin k)} (htot : Total c) {v : V}
    {θ : Fin k} : θ ∈ palette (c.lineGraphColoring htot) v ↔ θ ∈ colSet c v := by
  rw [mem_colSet]
  simp only [palette, Set.mem_setOf_eq, IsFree, not_forall, not_not]
  constructor
  · rintro ⟨⟨e, he⟩, hv, h⟩
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hv
    rw [lineGraphColoring_eq] at h
    exact ⟨u, h⟩
  · rintro ⟨u, h⟩
    refine ⟨⟨s(v, u), c.col_adj h⟩, Sym2.mem_mk_left _ _, ?_⟩
    rw [lineGraphColoring_eq]
    exact h

open Classical in
/-- The edges of colour `θ`. -/
noncomputable def edgesOf (c : PEC G (Fin k)) (θ : Fin k) : Finset (Sym2 V) :=
  univ.filter fun e => c.edgeOption e = some θ

theorem ncard_colorClass {c : PEC G (Fin k)} (htot : Total c) (θ : Fin k) :
    ((c.lineGraphColoring htot).colorClass θ).ncard = #(edgesOf c θ) := by
  classical
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext e
  simp only [Set.mem_image, Coloring.colorClass, Set.mem_setOf_eq, edgesOf, coe_filter,
    mem_univ, true_and]
  constructor
  · rintro ⟨e, h, rfl⟩
    exact (lineGraphColoring_eq htot e θ).1 h
  · intro h
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hadj : G.Adj u v := c.col_adj (by simpa using h)
      exact ⟨⟨s(u, v), hadj⟩, (lineGraphColoring_eq htot _ θ).2 h, rfl⟩

open Classical in
/-- `vcnt` counts both ends of every edge of colour `θ`. -/
theorem vcnt_eq_two_mul (c : PEC G (Fin k)) (θ : Fin k) :
    vcnt c θ = 2 * #(edgesOf c θ) := by
  have hU : (univ.filter fun v => θ ∈ colSet c v) = (edgesOf c θ).biUnion Sym2.toFinset := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_colSet, IsFree, not_forall, not_not,
      mem_biUnion, edgesOf, Sym2.mem_toFinset]
    constructor
    · rintro ⟨u, h⟩
      exact ⟨s(v, u), by simpa using h, Sym2.mem_mk_left _ _⟩
    · rintro ⟨e, he, hv⟩
      obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hv
      exact ⟨u, by simpa using he⟩
  have hdisj : (↑(edgesOf c θ) : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf hef
    rw [Function.onFun, Finset.disjoint_left]
    intro v hve hvf
    rw [Sym2.mem_toFinset] at hve hvf
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hve
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hvf
    simp only [edgesOf, coe_filter, mem_univ, true_and, Set.mem_setOf_eq, edgeOption_mk] at he hf
    exact hef (by rw [c.col_proper he hf])
  unfold vcnt
  rw [hU, card_biUnion hdisj, sum_congr rfl (g := fun _ => 2), sum_const, smul_eq_mul, mul_comm]
  intro e he
  apply Sym2.card_toFinset_of_not_isDiag
  induction e using Sym2.inductionOn with
  | hf u v =>
    simp only [edgesOf, mem_filter, mem_univ, true_and, edgeOption_mk] at he
    rw [Sym2.mk_isDiag_iff]
    exact (c.col_adj he).ne

end Dec

/-! ### Theorem 3.1 -/

/-- Recolour through `Fin.castLE`. -/
def castColoring {m : ℕ} (hmk : m ≤ k) (C : G.lineGraph.Coloring (Fin m)) :
    G.lineGraph.Coloring (Fin k) :=
  Coloring.mk (fun e => Fin.castLE hmk (C e)) fun h hc => C.valid h (Fin.castLE_injective hmk hc)

theorem palette_castColoring {m : ℕ} (hmk : m ≤ k) (C : G.lineGraph.Coloring (Fin m)) (v : V) :
    palette (castColoring hmk C) v = Fin.castLE hmk '' palette C v := by
  ext θ
  simp only [palette, castColoring, Coloring.mk, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨e, hv, rfl⟩
    exact ⟨C e, ⟨e, hv, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨e, hv, rfl⟩, rfl⟩
    exact ⟨e, hv, rfl⟩

theorem IsStrong.castColoring {m : ℕ} (hmk : m ≤ k) {C : G.lineGraph.Coloring (Fin m)}
    (hC : IsStrong C) : IsStrong (castColoring hmk C) := by
  intro v w h
  rw [palette_castColoring, palette_castColoring] at h
  exact hC (Set.image_injective.2 (Fin.castLE_injective hmk) h)

/-- **Rudašová–Soták 2008, Theorem 3.1.** If `G` has a strong `m`-colouring and `m ≤ k`, then
`G` has an equitable strong `k`-colouring. -/
theorem exists_equitable_strong {m : ℕ} (hmk : m ≤ k) (C : G.lineGraph.Coloring (Fin m))
    (hC : IsStrong C) :
    ∃ C' : G.lineGraph.Coloring (Fin k), IsStrong C' ∧ IsEquitable C' := by
  classical
  obtain ⟨c, hs, he⟩ := exists_equitable (strong_ofColoring (hC.castColoring hmk))
  refine ⟨c.lineGraphColoring hs.1, fun v w h => hs.2 ?_, fun x y => ?_⟩
  · ext θ
    rw [← mem_palette_lineGraphColoring hs.1, ← mem_palette_lineGraphColoring hs.1, h]
  · rw [ncard_colorClass, ncard_colorClass]
    have := he x y
    rw [vcnt_eq_two_mul, vcnt_eq_two_mul] at this
    omega

end Balanced
