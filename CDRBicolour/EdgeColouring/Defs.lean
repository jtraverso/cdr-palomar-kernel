/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Edge colourings, overfull sets and critical graphs

Definitions fixed against the literal sources read in the audit:

* Cao–Chen–Jing–Shan (SIAM J. Discrete Math. 36 (2022), arXiv:2105.05333v1, §1):
  "G is overfull if |E(G)| > Δ⌊|V(G)|/2⌋"; "G is Δ-critical if χ′(G) = Δ+1 and
  χ′(H) ≤ Δ for every proper subgraph H of G".
* Bongard–Hoffmann–Volkmann (Australas. J. Combin. 28 (2003), §1): an odd-order subgraph
  `H` is `Δ(G)`-overfull if `2|E(H)|/(|V(H)|-1) > Δ(G)`, and `Δ(G)`-full on equality.

Edge colourings are vertex colourings of the line graph (Mathlib), as in Lean Pool's Vizing.
-/

@[expose] public section

namespace CDRBicolour

open Finset

universe u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G` has a proper edge colouring with at most `k` colours. -/
def EdgeColourable (G : SimpleGraph V) (k : ℕ) : Prop := G.lineGraph.Colorable k

/-- Edges of `G` with both ends in `S`. -/
def edgesIn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ S

/-- CCJS: the whole graph is overfull, `|E| > Δ·⌊n/2⌋`. -/
def IsOverfull (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.maxDegree * (Fintype.card V / 2) < G.edgeFinset.card

/-- BHV: the odd set `S`, `|S| ≥ 3`, induces a `k`-overfull subgraph,
`k·(|S|-1) < 2·e(G[S])`.  (BHV only consider odd orders `≥ 3`; without this a singleton
would be "full" and Plantholt's Lemma 1.3 would be false.) -/
def InducesOverfull (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (S : Finset V) : Prop :=
  Odd S.card ∧ 3 ≤ S.card ∧ k * (S.card - 1) < 2 * (edgesIn G S).card

/-- BHV: the odd set `S` induces a `k`-full or `k`-overfull subgraph. -/
def InducesFullOrOverfull (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (S : Finset V) :
    Prop :=
  Odd S.card ∧ 3 ≤ S.card ∧ k * (S.card - 1) ≤ 2 * (edgesIn G S).card

/-- `Δ`-critical in the CCJS sense, for a graph WITHOUT isolated vertices: not
`Δ`-edge-colourable, but every proper spanning subgraph is.  (For graphs without isolated
vertices every proper subgraph lies in some `G - e`, so this agrees with CCJS.) -/
def IsCritical (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ v, 0 < G.degree v) ∧ ¬ EdgeColourable G G.maxDegree ∧
    ∀ H : SimpleGraph V, H < G → EdgeColourable H G.maxDegree

/-! ## External theorems, stated exactly; to be FORMALIZED (never assumed in final results). -/

/-- **Cao–Chen–Jing–Shan, Theorem 1.2** (verbatim: "Let G be a Δ-critical graph of order n.
If Δ(G) − 7δ(G)/4 ≥ (3n−17)/4, then G is overfull."). -/
def CCJS_Theorem_1_2 : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    IsCritical G →
      (3 * Fintype.card W : ℤ) - 17 ≤ 4 * G.maxDegree - 7 * G.minDegree →
        IsOverfull G

/-- **Plantholt, Lemma 1.3** (as quoted in BHV 2003): even order `n`, `δ(G) > n/2`; an odd
set inducing a `Δ(G)`-full or `Δ(G)`-overfull subgraph is `V(G) - x`. -/
def Plantholt_Lemma_1_3 : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    Even (Fintype.card W) → Fintype.card W < 2 * G.minDegree →
      ∀ S : Finset W, InducesFullOrOverfull G G.maxDegree S →
        ∃ x, S = Finset.univ.erase x

/-- **Plantholt, Corollary 1.7** (as quoted in BHV 2003): even order `n` and
`δ(G)+1 ≥ (√7/3)·n` (written `7n² ≤ 9(δ+1)²`); then `G` is Class 2 iff some odd set induces a
`Δ(G)`-overfull subgraph. -/
def Plantholt_Corollary_1_7 : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    Even (Fintype.card W) → 7 * Fintype.card W ^ 2 ≤ 9 * (G.minDegree + 1) ^ 2 →
      (¬ EdgeColourable G G.maxDegree ↔ ∃ S : Finset W, InducesOverfull G G.maxDegree S)

end CDRBicolour
