/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.CCd
public import Overfull.Theorem12

/-!
# Chen–Cao Theorem 1.3 (variant constant) and CCJS Theorem 1.2 for `n + δ ≥ 27`

Chen and Cao (arXiv:2512.07252, Theorem 1.3): a `Δ`-critical graph with
`3Δ ≥ 2n + 5δ − 12` is overfull. We prove it with `−6` in place of `−12`
(`overfull_of_critical_cc`), with the three-centre counts of Chen–Cao in their coarse form, the
broom lemma (their Lemma 3.1, `broomProp`), the kite lemma without `c` (their Lemma 4.2 in robust
form, `kite0Prop`) and the fork lemma.

Since `n + δ ≥ 27` and `4Δ − 7δ ≥ 3n − 17` give `3Δ ≥ 2n + 5δ − 6`, this yields CCJS Theorem 1.2
with its original constant `−17` for `n + δ ≥ 27` (`overfull_of_critical_ccjs`).
-/

@[expose] public section

namespace Overfull

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Chen–Cao Theorem 1.3 (variant).** A `Δ`-critical graph with `2n + 5δ ≤ 3Δ + 6` is
overfull. -/
theorem overfull_of_critical_cc (hG : IsDeltaCritical G)
    (hcond : 2 * Fintype.card V + 5 * G.minDegree ≤ 3 * G.maxDegree + 6) : IsOverfull G :=
  overfull_of_kites_cc hG (kite0Prop hG.2.1) (broomProp hG.2.1) hcond

/-- **CCJS Theorem 1.2 for `n + δ ≥ 27`.** A `Δ`-critical graph with `3n + 7δ ≤ 4Δ + 17`
(i.e. `4Δ − 7δ ≥ 3n − 17`) and `n + δ ≥ 27` is overfull. -/
theorem overfull_of_critical_ccjs (hG : IsDeltaCritical G)
    (hcond : 3 * Fintype.card V + 7 * G.minDegree ≤ 4 * G.maxDegree + 17)
    (hn : 27 ≤ Fintype.card V + G.minDegree) : IsOverfull G :=
  overfull_of_critical_cc hG (by omega)

end Overfull
