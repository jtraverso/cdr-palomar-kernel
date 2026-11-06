/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Plantholt's overfull criterion and 1-factorizations of dense regular graphs

* `Plantholt.theorem_1_2`: **M. Plantholt, *Overfull conjecture for graphs with high minimum
  degree*, J. Graph Theory 47 (2004) 73–80, Theorem 1.2.** Let `c ≥ 3/4` be such that every
  regular graph of even order `n` and degree at least `c n` is 1-factorizable. If `G` has even
  order `n` and `(3δ − Δ)/2 ≥ c n`, then `G` is Class 1 (`χ′ = Δ`) if and only if it has no
  `Δ`-overfull subgraph.
* `OneFactor.lineGraph_colorable_of_isRegular`: a `d`-regular graph of even order `2n` with
  `11 n ≤ 6 d` (degree at least `11/12` of the order) is `d`-edge-colourable, i.e. 1-factorizable.
  This is a weaker form of Chetwynd–Hilton, *1-factorizing regular graphs of high degree — an
  improved bound* (Discrete Math. 75 (1989)), Theorem 2 (`d ≥ ½(√7 − 1)|V|`), with the same
  architecture of proof.
* `OneFactor.overfull_criterion`: Plantholt's theorem with `c = 11/12`: if `G` has even order `n`
  and `11 n ≤ 6 (3δ − Δ)`, then `G` is Class 1 if and only if it has no `Δ`-overfull subgraph.
* `OneFactor.lineGraph_colorable_of_isRegular67`: **A. G. Chetwynd and A. J. W. Hilton, *Regular
  graphs of high degree are 1-factorizable*, Proc. London Math. Soc. (3) 50 (1985) 193–206.** A
  `d`-regular graph of even order `2n` with `12 n ≤ 7 d` (degree at least `6/7` of the order) is
  1-factorizable.
* `OneFactor.overfull_criterion67`: Plantholt's theorem with `c = 6/7`: if `G` has even order `n`
  and `12 n ≤ 7 (3δ − Δ)`, then `G` is Class 1 if and only if it has no `Δ`-overfull subgraph.

A `Δ`-overfull subgraph is a subgraph `H` with an odd number `≥ 3` of vertices and
`|E(H)| > Δ ⌊|V(H)|/2⌋`; an edge colouring of `G` with `k` colours is a colouring of its line graph.
-/

@[expose] public section

namespace Plantholt

universe u

/-- `G` contains a `Δ(G)`-overfull subgraph: a subgraph `H` with an odd number `≥ 3` of vertices
and `|E(H)| > Δ(G) ⌊|V(H)|/2⌋`. -/
def HasOverfullSubgraph {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  ∃ H : G.Subgraph, Odd H.verts.ncard ∧ 3 ≤ H.verts.ncard ∧
    G.maxDegree * (H.verts.ncard - 1) < 2 * H.edgeSet.ncard

/-- Every `d`-regular graph of even order `n` with `d ≥ c n` is 1-factorable, i.e. its edges
split into `d` perfect matchings (equivalently, it is `d`-edge-colourable). -/
def RegularOneFactorable (c : ℝ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] (d : ℕ),
    Even (Fintype.card W) → H.IsRegularOfDegree d → c * Fintype.card W ≤ d →
      H.lineGraph.Colorable d

/-- **Plantholt 2004, Theorem 1.2.** -/
theorem theorem_1_2 {c : ℝ} (hc : 3 / 4 ≤ c) (hC : RegularOneFactorable.{u} c)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hev : Even (Fintype.card V))
    (hdeg : 2 * c * Fintype.card V ≤ 3 * (G.minDegree : ℝ) - G.maxDegree) :
    G.lineGraph.Colorable G.maxDegree ↔ ¬ HasOverfullSubgraph G := by
  sorry

end Plantholt

namespace OneFactor

open SimpleGraph

universe u

/-- **Regular graphs of degree at least `11/12` of the (even) order are 1-factorizable.** -/
theorem lineGraph_colorable_of_isRegular {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d n : ℕ} (hcard : Fintype.card V = 2 * n)
    (hreg : G.IsRegularOfDegree d) (hd : 11 * n ≤ 6 * d) : G.lineGraph.Colorable d := by
  sorry

/-- **Plantholt's criterion with `c* = 11/12`.** -/
theorem overfull_criterion {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hev : Even (Fintype.card V))
    (hdeg : 11 * Fintype.card V ≤ 6 * (3 * G.minDegree - G.maxDegree)) :
    G.lineGraph.Colorable G.maxDegree ↔ ¬ Plantholt.HasOverfullSubgraph G := by
  sorry

/-- **Regular graphs of degree at least `6/7` of the (even) order are 1-factorizable.** -/
theorem lineGraph_colorable_of_isRegular67 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d n : ℕ} (hcard : Fintype.card V = 2 * n)
    (hreg : G.IsRegularOfDegree d) (hd : 12 * n ≤ 7 * d) : G.lineGraph.Colorable d := by
  sorry

/-- **Plantholt's criterion with `c* = 6/7`.** -/
theorem overfull_criterion67 {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hev : Even (Fintype.card V))
    (hdeg : 12 * Fintype.card V ≤ 7 * (3 * G.minDegree - G.maxDegree)) :
    G.lineGraph.Colorable G.maxDegree ↔ ¬ Plantholt.HasOverfullSubgraph G := by
  sorry

end OneFactor
