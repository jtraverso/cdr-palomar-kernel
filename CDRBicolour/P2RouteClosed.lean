/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.P2Route
public import CDRBicolour.L181.MaxMatching

/-!
# The P2 route with L181 proved

`P2_realises` with both completion statements of L181 discharged (`l181_noAnchor`,
`l181_star`).  The only remaining hypotheses are the two external edge-colouring theorems used
by L183 (CCJS Theorem 1.2 and Plantholt 2004 Theorem 1.2, both proved; Chetwynd–Hilton 1985,
stated as a literal `Prop`).
-/

@[expose] public section

namespace CDRBicolour.Prefix

/-- **P2 route, conditional only on Chetwynd–Hilton 1985.** -/
theorem P2_realises' (k : ℕ)
    (hk : 4 ≤ k) : Realises (pa k) (pb k) (pc k) :=
  P2_realises CDRBicolour.L181.l181_noAnchor CDRBicolour.L181.l181_star k hk

end CDRBicolour.Prefix
