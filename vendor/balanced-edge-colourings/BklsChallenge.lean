/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Balanced edge colourings (Balister–Kostochka–Li–Schelp 2004)

P. N. Balister, A. V. Kostochka, H. Li and R. H. Schelp, *Balanced edge colorings*, J. Combin.
Theory Ser. B 90 (2004) 3–20.

An edge colouring of `G` with `k` colours is a colouring `C : G.lineGraph.Coloring (Fin k)`; the
*palette* of a vertex is the set of colours of its edges; `C` is *strong* (vertex-distinguishing)
if distinct vertices have distinct palettes. `numPal C S` is the number of vertices with palette
`S`, and `cost C = Σ_S (numPal C S)²`.

* `theorem1` (**Theorem 1**): in a `k`-colouring of least cost, palettes of the same size are used
  numbers of times differing by at most two.
* `theorem6` (**Theorem 6**): a proper 3-edge-colouring can be recoloured with 4 colours so that
  vertices with the same key get different colour sets, provided that two vertices with the same
  key, degree and colour set have degree 3, and no three vertices of degree 3 share a key.
* `theorem10` (**Theorem 10, part 2**): conditions on the numbers of vertices of each degree giving
  a strong edge colouring with `k + 1` colours (`k ≥ Δ(G)`, `k ≥ 3`).
* `corollary12` (**Corollary 12**): if `Δ(G) ≥ √(2n) + 4`, `δ(G) ≥ 5` and `k` is least with
  `n_d ≤ C(k, d)` for all `d`, then the strong chromatic index lies in `{k, k + 1}`.
-/

@[expose] public section

namespace Balanced

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

/-- The set of colours of the edges at `v`. -/
def palette (C : G.lineGraph.Coloring (Fin k)) (v : V) : Set (Fin k) :=
  {θ | ∃ e : G.edgeSet, v ∈ (e : Sym2 V) ∧ C e = θ}

/-- Distinct vertices see distinct sets of colours. -/
def IsStrong (C : G.lineGraph.Coloring (Fin k)) : Prop := Function.Injective (palette C)

end Balanced

namespace BklsPalomar

open SimpleGraph Finset Balanced

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

open Classical in
/-- `n_S`: the number of vertices with palette `S`. -/
noncomputable def numPal (C : G.lineGraph.Coloring (Fin k)) (S : Finset (Fin k)) : ℕ :=
  #(univ.filter fun v => palette C v = ↑S)

/-- `Σ_S n_S²`. -/
noncomputable def cost (C : G.lineGraph.Coloring (Fin k)) : ℕ :=
  ∑ S : Finset (Fin k), numPal C S ^ 2

/-- **BKLS 2004, Theorem 1.** -/
theorem theorem1 (C : G.lineGraph.Coloring (Fin k))
    (hC : ∀ C' : G.lineGraph.Coloring (Fin k), cost C ≤ cost C') {P Q : Finset (Fin k)}
    (h : #P = #Q) : numPal C P ≤ numPal C Q + 2 := by
  sorry

/-- **BKLS 2004, Theorem 6.** -/
theorem theorem6 [DecidableRel G.Adj] {κ : Type*} (c : Sym2 V → Fin 3) (key : V → κ)
    (hc : ∀ v e e', e ∈ G.incidenceFinset v → e' ∈ G.incidenceFinset v → e ≠ e' → c e ≠ c e')
    (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v →
      (G.incidenceFinset u).image c = (G.incidenceFinset v).image c → G.degree u = 3)
    (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
      G.degree w = 3 → u = v ∨ v = w ∨ u = w) :
    ∃ col : Sym2 V → Fin 4,
      (∀ v e e', e ∈ G.incidenceFinset v → e' ∈ G.incidenceFinset v → e ≠ e' → col e ≠ col e') ∧
      ∀ u v, u ≠ v → key u = key v →
        (G.incidenceFinset u).image col ≠ (G.incidenceFinset v).image col := by
  sorry

/-- **BKLS 2004, Theorem 10 (part 2).** -/
theorem theorem10 [DecidableRel G.Adj] (hk3 : 3 ≤ k) (hΔ : G.maxDegree ≤ k)
    (h012 : ∀ d, d ≤ 2 → #(univ.filter fun v => G.degree v = d) ≤ 1)
    (h3 : #(univ.filter fun v => G.degree v = 3) ≤ 2)
    (h4 : #(univ.filter fun v => G.degree v = 4) ≤ 2)
    (hkk : #(univ.filter fun v => G.degree v = k) ≤ 2)
    (hk1 : #(univ.filter fun v => G.degree v = k - 1) ≤ k + 1)
    (h6 : ∀ d, 5 ≤ d → d + 2 ≤ k → (#(univ.filter fun v => G.degree v = d) : ℚ) ≤
      ((d : ℚ) - 4) / ((d : ℚ) - 3) *
        min (2 * (((k - 3).choose (d - 3) : ℕ) : ℚ)) ((k.choose d : ℕ) : ℚ) - 2) :
    ∃ C : G.lineGraph.Coloring (Fin (k + 1)), IsStrong C := by
  sorry

/-- **BKLS 2004, Corollary 12.** -/
theorem corollary12 [DecidableRel G.Adj] (hn : Real.sqrt (2 * Fintype.card V) + 4 ≤ G.maxDegree)
    (hδ : 5 ≤ G.minDegree) {k : ℕ}
    (hk : ∀ d, #(univ.filter fun v => G.degree v = d) ≤ k.choose d)
    (hkmin : ∀ k' < k, ∃ d, k'.choose d < #(univ.filter fun v => G.degree v = d)) :
    (∃ C : G.lineGraph.Coloring (Fin (k + 1)), IsStrong C) ∧
      ∀ m (C : G.lineGraph.Coloring (Fin m)), IsStrong C → k ≤ m := by
  sorry

end BklsPalomar
