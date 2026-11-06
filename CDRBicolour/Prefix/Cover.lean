/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Prefix.RowSystem
public import CDRBicolour.L184.Assembly

/-!
# L182: the prefix AAB/ABB/BBC/BCC covers exactly the non-reserved pairs

Stage data (`PrefixData`): a fixed-point-free involution `μ` of `A` (the reserved matching
`M_A`), a proper colouring `χA` of `GA = K_A − M_A` by `B`, perfect pairings `MA i` of the
`B`-colours missing at each `A`-row (ABB), a proper colouring `χB` of the remaining BB graph `GB`
by `C`, and perfect pairings `MB j` of the `C`-colours missing at each `B`-row (BCC).
The residual `F` is the graph of CC pairs not used by BCC.

`prefix_cover` proves that the blocks
`AAB = {χA e} ∪ e`, `ABB = {i} ∪ p`, `BBC = {χB e} ∪ e`, `BCC = {j} ∪ p`
form a family `P` meeting all hypotheses of `L184.l184_assembly`: 3-sets seeing exactly two
classes, no block through a reserved pair (AC, `M_A`, edges of `F`), and exactly one block
through every other pair.
-/

@[expose] public section

namespace CDRBicolour.Prefix

open Finset LeanPool.Vizing.ColourClasses CDRBicolour.L184

variable {V : Type*} [Fintype V] [DecidableEq V] (col : V → Fin 3)

abbrev BType := {v : V // col v = 1}

/-- The stage data of L182. -/
structure PrefixData where
  μ : AType col → AType col
  χA : Sym2 (AType col) → BType col
  MA : AType col → Finset (Sym2 (BType col))
  χB : Sym2 (BType col) → CType col
  MB : BType col → Finset (Sym2 (CType col))

variable {col} (d : PrefixData col)

/-- The graph of pairs of colours not used by any row pairing. -/
def unusedGraph {Rw Cl : Type*} [Fintype Rw] [DecidableEq Cl] (M : Rw → Finset (Sym2 Cl)) :
    SimpleGraph Cl :=
  SimpleGraph.fromRel fun u v => ∀ j, s(u, v) ∉ M j

instance {Rw Cl : Type*} [Fintype Rw] [DecidableEq Cl] (M : Rw → Finset (Sym2 Cl)) :
    DecidableRel (unusedGraph M).Adj := by
  unfold unusedGraph; infer_instance

/-- `K_A − M_A`. -/
def GA (μ : AType col → AType col) : SimpleGraph (AType col) :=
  SimpleGraph.fromRel fun x y => y ≠ μ x

instance (μ : AType col → AType col) : DecidableRel (GA μ).Adj := by unfold GA; infer_instance

/-- BB pairs not used by ABB. -/
abbrev GB (MA : AType col → Finset (Sym2 (BType col))) : SimpleGraph (BType col) :=
  unusedGraph MA

/-- CC pairs not used by BCC: the residual of L182. -/
abbrev resid (MB : BType col → Finset (Sym2 (CType col))) : SimpleGraph (CType col) :=
  unusedGraph MB

/-- Validity of the stage data. -/
structure PrefixData.Valid : Prop where
  hμ : ∀ u, d.μ (d.μ u) = u
  hμ' : ∀ u, d.μ u ≠ u
  hχA : ProperOn (GA d.μ).edgeFinset d.χA
  hMA : ∀ i, IsPerfectPairing (d.MA i) (miss (GA d.μ) d.χA i)
  hMAd : PairDisjoint d.MA
  hχB : ProperOn (GB d.MA).edgeFinset d.χB
  hMB : ∀ j, IsPerfectPairing (d.MB j) (miss (GB d.MA) d.χB j)
  hMBd : PairDisjoint d.MB

/-- A block: a point `z` together with a pair of points of one class. -/
def blk {P : V → Prop} [DecidablePred P] (z : V) (p : Sym2 {v // P v}) : Finset V :=
  insert z (p.toFinset.map (Function.Embedding.subtype _))

theorem mem_blk {P : V → Prop} [DecidablePred P] (z : V) (p : Sym2 {v // P v}) (x : V) :
    x ∈ blk z p ↔ x = z ∨ ∃ q ∈ p, q.1 = x := by
  simp [blk, Sym2.mem_toFinset]

end CDRBicolour.Prefix
