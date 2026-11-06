/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.KiteG

/-!
# CCJS Theorem 1.2 (variant constant)

Cao, Chen, Jing and Shan (arXiv:2105.05333, Theorem 1.2): a `Δ`-critical graph `G` with
`4Δ(G) − 7δ(G) ≥ 3|V(G)| − 17` is overfull. Their Case 2 (and the fork branch of Case 1) counts
common neighbours as in (1), which needs one more unit of degree than is available; we prove the
theorem under `3|V(G)| + 7δ(G) ≤ 4Δ(G) + 10`, where every count closes. The kite lemmas
(CCJS Lemmas 2.7 and 2.8) are proved in `ShortKite` and `KiteG`.
-/

@[expose] public section

namespace Overfull

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **CCJS Theorem 1.2 (variant).** A `Δ`-critical graph with `3n + 7δ ≤ 4Δ + 10` is
overfull. -/
theorem overfull_of_critical (hG : IsDeltaCritical G)
    (hcond : 3 * Fintype.card V + 7 * G.minDegree ≤ 4 * G.maxDegree + 10) : IsOverfull G :=
  overfull_of_kites hG (kiteProp hG.2.1) (shortKiteProp hG.2.1) hcond

end Overfull
