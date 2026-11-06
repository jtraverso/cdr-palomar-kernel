/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Pseudorandom.Defs
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

/-! # Tuple weight functions

An `ℓ`-tuple weight function on the edges of a hypergraph is a function
`ω : Finset (Finset V) → ℝ`, evaluated on `ℓ`-sets of edges. For a set `X` of edges,
`ω(X) = ∑_{S ⊆ X, |S| = ℓ} ω(S)` (`tweight`), and for a set `T` of edges of `H`,
`ω(T) = ∑_{T ⊆ S ⊆ E(H), |S| = ℓ} ω(S)` (`tdeg`); `‖ω‖_k` is the maximum of `tdeg` over
`k`-sets `T`. `ω` is clean if it vanishes on `ℓ`-sets of edges that are not matchings.
-/

@[expose] public section

namespace Pseudorandom

open Finset

variable {V : Type*} [DecidableEq V]

/-- `ω(X) = ∑_{S ∈ (X choose ℓ)} ω(S)`. -/
def tweight (ℓ : ℕ) (ω : Finset (Finset V) → ℝ) (X : Finset (Finset V)) : ℝ :=
  ∑ S ∈ X.powersetCard ℓ, ω S

/-- `ω(T) = ∑_{S ⊇ T} ω(S)`, over the `ℓ`-sets `S` of edges of `H` containing `T`. -/
def tdeg (ℓ : ℕ) (ω : Finset (Finset V) → ℝ) (H T : Finset (Finset V)) : ℝ :=
  ∑ S ∈ (H.powersetCard ℓ).filter (fun S => T ⊆ S), ω S

end Pseudorandom
