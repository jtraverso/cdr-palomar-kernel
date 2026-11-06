/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4HingeAfterChild
public import RequestProject.TypedTriangle.CoreEdgeGraph
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Translate edge deletion in the V49 graph interface to the host used by
the exact seed and packing modules. -/

open Finset Classical
noncomputable section
namespace TypedTriangle.StockEntry
open CorePaid

variable {V I : Type*} [Fintype V]

theorem g4_graph_sdiff_eq_subHost (H : Host V I) (C : Finset (Sym2 V)) :
    H.G \ SimpleGraph.fromEdgeSet (C : Set (Sym2 V)) =
      (subHost H (edges H\C)).G := by
  apply (SimpleGraph.edgeSet_inj).mp
  ext e
  simp [subHost, edges, SimpleGraph.edgeSet_sdiff,
    SimpleGraph.edgeSet_fromEdgeSet,
    SimpleGraph.edgeSet_sdiff_sdiff_isDiag]

theorem g4_hinge_after_edge_set_deletion {I : Type} (F : Set (Multiset I))
    (α Cseed δ : ℝ) (h : ℕ) (hα : 0 < α) (hC : 0 < Cseed)
    (hδ : 0 < δ) (hh : 6 ≤ h) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ)
        (C : Finset (Sym2 V)) (d : ℕ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F Cseed φ →
        CommonNbrCond H F α → HingeCond H F α h →
        C ⊆ edges H → (∀ v, degIn C v ≤ d) →
        (d:ℝ) ≤ η*Fintype.card V →
        HingeCond (subHost H (edges H\C)) F
          (S07V49.hingeConstB α 1 h) (2*h-3) := by
  obtain ⟨η,hη,n₀,hDelete⟩ :=
    g4_hinge_after_graph_deletion F α Cseed δ h hα hC hδ hh
  refine ⟨η,hη,n₀,?_⟩
  intro V _ H φ C d hn hSeed h3 h4 hCE hDeg hd
  let B := SimpleGraph.fromEdgeSet (C : Set (Sym2 V))
  letI : DecidableRel B.Adj := Classical.decRel _
  have hDiag : ∀ e ∈ C, ¬e.IsDiag := edges_diagonal_free hCE
  have hBDeg : ∀ v, B.degree v ≤ d := by
    intro v
    rw [← SimpleGraph.card_incidenceFinset_eq_degree,
      SimpleGraph.incidenceFinset_eq_filter, edgeFinset_fromEdges C hDiag]
    exact hDeg v
  have hh' := hDelete H φ B d hn hSeed h3 h4 hBDeg hd
  have hEq := g4_graph_sdiff_eq_subHost H C
  rw [hEq] at hh'
  simpa only [subHost] using hh'

end TypedTriangle.StockEntry
