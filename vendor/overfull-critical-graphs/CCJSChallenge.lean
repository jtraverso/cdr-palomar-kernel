/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Overfullness of edge-chromatic critical graphs (Cao–Chen–Jing–Shan, Theorem 1.2)

Y. Cao, G. Chen, G. Jing and S. Shan, *The overfullness of graphs with small minimum degree and
large maximum degree* (arXiv:2105.05333), Theorem 1.2: a `Δ`-critical graph `G` of order `n` with
`4Δ(G) − 7δ(G) ≥ 3n − 17` is overfull. Stated here with the constant `−10` in place of `−17`:

* `Overfull.overfull_of_critical`: if `G` is `Δ`-critical and `3n + 7δ(G) ≤ 4Δ(G) + 10`, then
  `|E(G)| > Δ(G) ⌊n/2⌋`.
* `Overfull.overfull_of_critical_cc`: **Chen–Cao (arXiv:2512.07252), Theorem 1.3**, with `−6` in
  place of `−12`: if `G` is `Δ`-critical and `2n + 5δ(G) ≤ 3Δ(G) + 6`, then `G` is overfull.
* `Overfull.overfull_of_critical_ccjs`: CCJS Theorem 1.2 with its original constant: if `G` is
  `Δ`-critical, `4Δ(G) − 7δ(G) ≥ 3n − 17` and `n + δ(G) ≥ 27`, then `G` is overfull.

`G` is `Δ`-critical when it is connected, of class two (its line graph is not
`Δ(G)`-colourable), and `G − e` is `Δ(G)`-edge-colourable for every edge `e`.
-/

@[expose] public section

namespace Overfull

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `G` is of class two: no proper edge colouring with `Δ(G)` colours. -/
def IsClassTwo (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ¬ G.lineGraph.Colorable G.maxDegree

/-- `G` is `Δ`-critical: connected, of class two, and every edge-deleted subgraph is
`Δ(G)`-edge-colourable. -/
def IsDeltaCritical (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ IsClassTwo G ∧
    ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).lineGraph.Colorable G.maxDegree

/-- `G` is overfull: `|E(G)| > Δ(G) ⌊|V(G)|/2⌋`. -/
def IsOverfull (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.maxDegree * (Fintype.card V / 2) < #G.edgeFinset

/-- **CCJS Theorem 1.2 (variant).** A `Δ`-critical graph with `3n + 7δ ≤ 4Δ + 10` is
overfull. -/
theorem overfull_of_critical (hG : IsDeltaCritical G)
    (hcond : 3 * Fintype.card V + 7 * G.minDegree ≤ 4 * G.maxDegree + 10) : IsOverfull G := by
  sorry

/-- **Chen–Cao Theorem 1.3 (variant).** A `Δ`-critical graph with `2n + 5δ ≤ 3Δ + 6` is
overfull. -/
theorem overfull_of_critical_cc (hG : IsDeltaCritical G)
    (hcond : 2 * Fintype.card V + 5 * G.minDegree ≤ 3 * G.maxDegree + 6) : IsOverfull G := by
  sorry

/-- **CCJS Theorem 1.2 for `n + δ ≥ 27`.** A `Δ`-critical graph with `3n + 7δ ≤ 4Δ + 17`
(i.e. `4Δ − 7δ ≥ 3n − 17`) and `n + δ ≥ 27` is overfull. -/
theorem overfull_of_critical_ccjs (hG : IsDeltaCritical G)
    (hcond : 3 * Fintype.card V + 7 * G.minDegree ≤ 4 * G.maxDegree + 17)
    (hn : 27 ≤ Fintype.card V + G.minDegree) : IsOverfull G := by
  sorry

end Overfull
