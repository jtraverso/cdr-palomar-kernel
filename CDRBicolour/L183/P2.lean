/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.L183.Residual

/-!
# L183 for the P2 family (`y = 6k+3 ≥ 27`, i.e. `k ≥ 4`)

`a = 12k²+14k+4`, `c = 12k²+20k+9`, root degree `s = y-1 = 6k+2`, `|P| = s/2`.
All numerical hypotheses of `l183` are discharged here.  No external hypothesis: CCJS 1.2 and Plantholt's criterion with `c = 6/7` are proved (Palomar
formalizations); both need `k ≥ 4`.
-/

@[expose] public section

namespace CDRBicolour.L183

open Finset

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]

theorem l183_P2
    (k : ℕ) (hk : 4 ≤ k) (F : SimpleGraph W) [DecidableRel F.Adj] (w : W) (P : Finset W)
    (hcard : Fintype.card W = 12 * k ^ 2 + 20 * k + 9)
    (hdw : F.degree w = 6 * k + 2) (hwP : w ∉ P)
    (hdP : ∀ v ∈ P, F.degree v = 12 * k ^ 2 + 14 * k + 2)
    (hdR : ∀ v, v ≠ w → v ∉ P → F.degree v = 12 * k ^ 2 + 14 * k + 4)
    (hPs : 2 * P.card = 6 * k + 2) :
    EdgeColourable F (12 * k ^ 2 + 14 * k + 4) := by
  have hk2 : 16 ≤ k ^ 2 := by nlinarith
  refine l183 F w ccjs_large (12 * k ^ 2 + 14 * k + 4) (6 * k + 2) P hdw hwP ?_ hdR hPs ?_ ?_ ?_
    (by omega) (by nlinarith) ?_ ?_ (by nlinarith) (by nlinarith)
  · intro v hv; rw [hdP v hv]; omega
  · rw [hcard]; exact ⟨6 * k ^ 2 + 10 * k + 4, by ring⟩
  · rw [hcard, show 12 * k ^ 2 + 20 * k + 9 - 1 = 12 * k ^ 2 + 20 * k + 8 by omega]
    nlinarith
  · rw [hcard]; omega
  · rw [hcard]; nlinarith
  · rw [hcard]; nlinarith

end CDRBicolour.L183
