/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Absorption.Extremes.PlantCopies

/-!
# Planting `AAC` blocks, part 2: residue gadgets (item 3, extremes)

Three small independent models (each checked by `decide` on its own; a single 21-point model with
a selection over `(r, nst)` blew up the kernel):

* `R4m` on `Fin 8` (`A` = `0 … 3`, `C` = `4 … 7`): a 4-cycle of `AAC` blocks;
* `R5m` on `Fin 10` (`A` = `0 … 4`, `C` = `5 … 9`): a 5-cycle;
* `S1m` on `Fin 7` (`A` = `0 … 3`, `C` = `4 … 6`): a star, centre `0` in three blocks, leaves in one.

In the cycles every `A` point is in exactly two blocks; in the star every `A` point is in an odd
number of blocks.  The gadgets are placed on disjoint `A` points in `PlantFinal`.
-/

@[expose] public section

namespace CDRBicolour.Absorption.Extremes

open Finset CDRBicolour.Absorption.Exact

def R4m : Finset (Finset (Fin 8)) := {{0, 1, 4}, {1, 2, 5}, {2, 3, 6}, {3, 0, 7}}
def R5m : Finset (Finset (Fin 10)) := {{0, 1, 5}, {1, 2, 6}, {2, 3, 7}, {3, 4, 8}, {4, 0, 9}}
def S1m : Finset (Finset (Fin 7)) := {{0, 1, 4}, {0, 2, 5}, {0, 3, 6}}

theorem R4m_facts :
    R4m.card = 4 ∧
    (∀ T ∈ R4m, T.card = 3 ∧ (T.filter (·.val < 4)).card = 2) ∧
    (∀ T ∈ R4m, ∀ T' ∈ R4m, T ≠ T' → Disjoint (te T) (te T')) ∧
    (∀ i : Fin 8, i.val < 4 → (R4m.filter (i ∈ ·)).card = 2) := by
  decide +kernel

theorem R5m_facts :
    R5m.card = 5 ∧
    (∀ T ∈ R5m, T.card = 3 ∧ (T.filter (·.val < 5)).card = 2) ∧
    (∀ T ∈ R5m, ∀ T' ∈ R5m, T ≠ T' → Disjoint (te T) (te T')) ∧
    (∀ i : Fin 10, i.val < 5 → (R5m.filter (i ∈ ·)).card = 2) := by
  decide +kernel

theorem S1m_facts :
    S1m.card = 3 ∧
    (∀ T ∈ S1m, T.card = 3 ∧ (T.filter (·.val < 4)).card = 2) ∧
    (∀ T ∈ S1m, ∀ T' ∈ S1m, T ≠ T' → Disjoint (te T) (te T')) ∧
    (∀ i : Fin 7, i.val < 4 → (S1m.filter (i ∈ ·)).card % 2 = 1) := by
  decide +kernel

end CDRBicolour.Absorption.Extremes
