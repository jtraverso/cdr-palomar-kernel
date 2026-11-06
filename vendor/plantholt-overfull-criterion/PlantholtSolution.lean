/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import Plantholt.Main
public import OneFactor.Plantholt
public import OneFactor.Plantholt67

/-!
# Solution

`Plantholt.HasOverfullSubgraph`, `Plantholt.RegularOneFactorable` and `Plantholt.theorem_1_2` are
in `Plantholt.Main` (Lemma 2.1 in `Plantholt.Basic`, the cases of the induction in
`Plantholt.Cases*`). `OneFactor.lineGraph_colorable_of_isRegular` and
`OneFactor.overfull_criterion` are in `OneFactor.Plantholt`, from `OneFactor.colorable_of_regular`
(`OneFactor.Main`): pivots and Fournier's theorem (`OneFactor.Pivot`), near 1-factors through
prescribed matchings (`OneFactor.Factors`), round-robin classes (`OneFactor.Classes`), and the
re-insertion of a vertex of a regular graph (`OneFactor.Extend`).
`OneFactor.lineGraph_colorable_of_isRegular67` and `OneFactor.overfull_criterion67` are in
`OneFactor.Plantholt67`, from `OneFactor.colorable_of_regular67` (`OneFactor.Main67`): the
staircase matchings of Chetwynd–Hilton 1989 (`OneFactor.Stair`, labelling in `OneFactor.Label67`,
`OneFactor.Label67b`), the pairing of `Y` with `X` (`OneFactor.Pair67`), near 1-factors with a
bound for each step (`OneFactor.Factors2`), and the core of their Theorem 5 coloured by adding the
core edges by rank with pivots (`OneFactor.CoreRank`, `OneFactor.Core67`).
-/
