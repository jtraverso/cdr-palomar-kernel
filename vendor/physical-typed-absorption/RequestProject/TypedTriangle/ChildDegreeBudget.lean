/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V28.AbsorberPlacement
public import RequestProject.S07V42.Setting
public import RequestProject.TypedTriangle.Defs
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Any edge set contained in one induced child has maximum degree at most
the child size. This is the quantitative input for exact seed persistence
after reserving a decomposable dense reference inside that child. -/

open Finset Classical
noncomputable section
namespace TypedTriangle

theorem degree_le_child_card {V I : Type*} [Fintype V]
    (H : Host V I) (W : Finset V) (B : Finset (Sym2 V))
    (hB : B ⊆ SparseEdge.edges (S07V42.indG H.G W)) :
    ∀ v, SparseEdge.degIn B v ≤ W.card := by
  have hSupp : SparseEdge.support B ⊆ W := by
    intro x hx
    obtain ⟨e,he,hxe⟩ := (Finset.mem_filter.mp hx).2
    induction e using Sym2.ind with
    | _ u w =>
      have hAdj : (S07V42.indG H.G W).Adj u w := by
        simpa [SparseEdge.edges] using hB he
      have hEnds : u ∈ W ∧ w ∈ W := hAdj.2
      rcases (by simpa using hxe : x = u ∨ x = w) with rfl | rfl
      · exact hEnds.1
      · exact hEnds.2
  intro v
  exact (S07V28.degIn_le_card_support B v).trans (Finset.card_le_card hSupp)

#print axioms degree_le_child_card

end TypedTriangle
