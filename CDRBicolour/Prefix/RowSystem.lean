/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.EdgeColouring.Basic

/-!
# Row systems and the statement of L181

A **row system** is a simple graph `G` on a set of rows `Rw`, properly edge-coloured by `χ`
with colours in `Cl`.  Row `j` *misses* the colours not used at `j`; the *multiplicity* of a
colour is the number of rows missing it.  In L182 two row systems occur:

* AAB stage: rows = class `A`, colours = class `B`, `G = K_A − M_A`;
* BBC stage: rows = class `B`, colours = class `C`, `G` = the BB pairs left after ABB.

Completing a row means choosing a perfect pairing of its missing colours (ABB, resp. BCC blocks);
pairings of different rows must use different pairs.

`L181_NoAnchor` and `L181_Star` are the two completion statements of L181 (candidate route,
`work/concentrated-aac-universal-candidate.txt`), with exactly the scope stated there: all rows
start empty (no-anchor), resp. with only the star pair through an unused colour `w`
(star version, the stars given by an injective choice `t`).  The conclusions keep the row
graph, properness, the empty colour `w`, and the two-level multiset of multiplicities.
-/

@[expose] public section

namespace CDRBicolour.Prefix

open Finset LeanPool.Vizing.ColourClasses

universe u

section Defs

variable {Rw Cl : Type*} [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]

/-- Colours present at row `j`. -/
def present (G : SimpleGraph Rw) [DecidableRel G.Adj] (χ : Sym2 Rw → Cl) (j : Rw) :
    Finset Cl :=
  (G.incidenceFinset j).image χ

/-- Colours missing at row `j`. -/
def miss (G : SimpleGraph Rw) [DecidableRel G.Adj] (χ : Sym2 Rw → Cl) (j : Rw) : Finset Cl :=
  univ \ present G χ j

/-- Number of rows missing the colour `v`. -/
def mult (G : SimpleGraph Rw) [DecidableRel G.Adj] (χ : Sym2 Rw → Cl) (v : Cl) : ℕ :=
  (univ.filter fun j => v ∈ miss G χ j).card

/-- `M` is a perfect pairing of `S`: non-degenerate pairs inside `S`, each point of `S` in
exactly one pair. -/
def IsPerfectPairing (M : Finset (Sym2 Cl)) (S : Finset Cl) : Prop :=
  (∀ e ∈ M, ¬ e.IsDiag) ∧ (∀ e ∈ M, ∀ v ∈ e, v ∈ S) ∧ (∀ v ∈ S, ∃! e, e ∈ M ∧ v ∈ e)

/-- Different rows use different pairs. -/
def PairDisjoint (M : Rw → Finset (Sym2 Cl)) : Prop :=
  ∀ j j', j ≠ j' → Disjoint (M j) (M j')

theorem mem_present {G : SimpleGraph Rw} [DecidableRel G.Adj] {χ : Sym2 Rw → Cl} {j : Rw}
    {v : Cl} : v ∈ present G χ j ↔ ∃ e ∈ G.incidenceFinset j, χ e = v := by
  simp [present]

theorem mem_miss {G : SimpleGraph Rw} [DecidableRel G.Adj] {χ : Sym2 Rw → Cl} {j : Rw}
    {v : Cl} : v ∈ miss G χ j ↔ ∀ e ∈ G.incidenceFinset j, χ e ≠ v := by
  simp [miss, present]

end Defs

/-- **L181, no-anchor version** (rows start empty). -/
def L181_NoAnchor : Prop :=
  ∀ (Rw Cl : Type u) [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
    (G : SimpleGraph Rw) [DecidableRel G.Adj] (χ : Sym2 Rw → Cl) (m : ℕ),
    ProperOn G.edgeFinset χ →
    (∀ j, Even (miss G χ j).card ∧ 4 ≤ (miss G χ j).card) →
    (∀ v, mult G χ v = m ∨ mult G χ v = m + 2) →
    6 * (m + 2) ≤ Fintype.card Cl →
    ∃ χ' : Sym2 Rw → Cl, ProperOn G.edgeFinset χ' ∧
      (∀ v, mult G χ' v = m ∨ mult G χ' v = m + 2) ∧
      (univ.filter fun v => mult G χ' v = m + 2).card =
        (univ.filter fun v => mult G χ v = m + 2).card ∧
      ∃ M : Rw → Finset (Sym2 Cl), (∀ j, IsPerfectPairing (M j) (miss G χ' j)) ∧ PairDisjoint M

/-- **L181, star version**: an unused colour `w`, distinct star partners `t j`. -/
def L181_Star : Prop :=
  ∀ (Rw Cl : Type u) [Fintype Rw] [DecidableEq Rw] [Fintype Cl] [DecidableEq Cl]
    (G : SimpleGraph Rw) [DecidableRel G.Adj] (χ : Sym2 Rw → Cl) (m : ℕ) (w : Cl) (t : Rw → Cl),
    ProperOn G.edgeFinset χ → (∀ e ∈ G.edgeFinset, χ e ≠ w) →
    Function.Injective t → (∀ j, t j ∈ miss G χ j ∧ t j ≠ w) →
    (∀ j, Even (miss G χ j).card ∧ 6 ≤ (miss G χ j).card) →
    (∀ v, v ≠ w → mult G χ v = m ∨ mult G χ v = m + 2) →
    6 * (m + 2) ≤ Fintype.card Cl - 1 →
    ∃ χ' : Sym2 Rw → Cl, ProperOn G.edgeFinset χ' ∧ (∀ e ∈ G.edgeFinset, χ' e ≠ w) ∧
      (∀ v, v ≠ w → mult G χ' v = m ∨ mult G χ' v = m + 2) ∧
      (univ.filter fun v => v ≠ w ∧ mult G χ' v = m + 2).card =
        (univ.filter fun v => v ≠ w ∧ mult G χ v = m + 2).card ∧
      ∃ M : Rw → Finset (Sym2 Cl), (∀ j, IsPerfectPairing (M j) (miss G χ' j)) ∧ PairDisjoint M

end CDRBicolour.Prefix
