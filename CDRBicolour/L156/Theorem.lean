/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.L156.MaxMatching

/-!
# L156: the uniform row theorem (fixed quotas)

`l156`: in a row system (a proper colouring of a simple graph on the rows, colours on `Cl`), let
`ρ` be an upper bound of the multiplicities and `H` a set of at least `6ρ` colours of
multiplicity exactly `ρ`.  Suppose some rows are already completed (perfect pairings of their
missing sets, pairwise disjoint) and every other row is empty with an even missing set of size
`≥ 4`.  Then, after a recolouring of the graph which keeps EVERY multiplicity, all rows carry
pairwise disjoint perfect pairings of their missing sets.
-/

@[expose] public section

namespace CDRBicolour.L156

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.Prefix CDRBicolour.L181

/-- **L156.** -/
theorem l156 {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
    (G : SimpleGraph Rw) [DecidableRel G.Adj] (χ : Sym2 Rw → Cl) (ρ : ℕ) (H : Finset Cl)
    (D₀ : Finset Rw) (M₀ : Rw → Finset (Sym2 Cl)) (hχ : ProperOn G.edgeFinset χ)
    (heven : ∀ j, Even (miss G χ j).card)
    (hdone : ∀ j ∈ D₀, IsPerfectPairing (M₀ j) (miss G χ j))
    (hopen : ∀ j, j ∉ D₀ → M₀ j = ∅ ∧ 4 ≤ (miss G χ j).card) (hdisj : PairDisjoint M₀)
    (hρ : ∀ v, mult G χ v ≤ ρ) (hH : ∀ v ∈ H, mult G χ v = ρ) (h6 : 6 * ρ ≤ H.card) :
    ∃ χ' : Sym2 Rw → Cl, ProperOn G.edgeFinset χ' ∧ (∀ v, mult G χ' v = mult G χ v) ∧
      ∃ M : Rw → Finset (Sym2 Cl), (∀ j, IsPerfectPairing (M j) (miss G χ' j)) ∧
        PairDisjoint M := by
  classical
  have hs : RowStateQ G ∅ (fun v => mult G χ v) ρ 0 (fun j => (miss G χ j).card) D₀ χ M₀ := by
    refine ⟨⟨hχ, by simp, fun j => ?_, hdisj, fun v _ => rfl⟩, fun v _ => hρ v, hdone,
      fun j _ => by simp, fun j hj => by simp [(hopen j hj).1, cover_empty], fun j hj => ?_,
      fun j => rfl⟩
    · by_cases hj : j ∈ D₀
      · exact isPartialPairing_of_perfect (hdone j hj)
      · rw [(hopen j hj).1]; exact isPartialPairing_empty _
    · rw [(hopen j hj).1, cover_empty, card_empty, zero_add]; exact (hopen j hj).2
  have hR : RoomHypQ G ∅ (fun v => mult G χ v) ρ 0 (fun j => (miss G χ j).card) H :=
    roomHypQ_of heven (by omega)
  obtain ⟨χ', M', hs'⟩ := complete_allQ (H := H) (fun v hv => hH v hv) hR heven _ D₀ χ M₀ hs rfl
  exact ⟨χ', hs'.good.proper, fun v => hs'.good.fix v (notMem_empty v), M',
    fun j => hs'.done j (mem_univ j), hs'.good.disj⟩

end CDRBicolour.L156
