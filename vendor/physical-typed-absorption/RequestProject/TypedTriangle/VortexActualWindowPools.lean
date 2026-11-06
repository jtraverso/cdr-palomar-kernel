/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexCleanHingeGeometry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex

/-- Preplanned completion pools lose only the deleted vertices and the two
paid spoke neighbourhoods. Roots may lie outside the retained window. -/
theorem commonNbr_pool_after_vertex_and_edge_payment {V I : Type*} [Fintype V]
    (H : Host V I) (W Z : Finset V)
    (C : Finset (Sym2 V)) (d : ℕ) (hDegree : ∀ v, SparseEdge.degIn C v ≤ d)
    (u v : V) (k : I) :
    (((commonNbrs H k u v) ∩ W).card : ℝ) - Z.card - 2*(d : ℝ) ≤
      ((commonNbrs (subHost H (edges H \ C)) k u v) ∩ (W \ Z)).card := by
  let Bad := SparseEdge.nbrIn C u ∪ SparseEdge.nbrIn C v
  let New := (commonNbrs (subHost H (edges H \ C)) k u v) ∩ (W \ Z)
  have hBad : Bad.card ≤ 2*d := by
    have hu := (SparseEdge.card_nbrIn_le C u).trans (hDegree u)
    have hv := (SparseEdge.card_nbrIn_le C v).trans (hDegree v)
    exact (card_union_le _ _).trans (by omega)
  have hCover : (commonNbrs H k u v) ∩ W ⊆ New ∪ (Z ∪ Bad) := by
    intro w hw
    obtain ⟨hwPool,hwW⟩ := mem_inter.mp hw
    by_cases hwZ : w ∈ Z
    · exact mem_union_right _ (mem_union_left _ hwZ)
    by_cases hu : s(u,w) ∈ C
    · exact mem_union_right _ (mem_union_right _
        (mem_union_left _ (by simp [SparseEdge.nbrIn,hu])))
    by_cases hv : s(v,w) ∈ C
    · exact mem_union_right _ (mem_union_right _
        (mem_union_right _ (by simp [SparseEdge.nbrIn,hv])))
    · apply mem_union_left
      refine mem_inter.mpr ⟨?_,mem_sdiff.mpr ⟨hwW,hwZ⟩⟩
      rw [Residual.commonNbrs_sdiff]
      exact mem_filter.mpr ⟨hwPool,hu,hv⟩
  have hCards : ((commonNbrs H k u v ∩ W).card : ℝ) ≤
      New.card + (Z.card + Bad.card) := by
    exact_mod_cast (card_le_card hCover).trans
      ((card_union_le _ _).trans (Nat.add_le_add_left (card_union_le Z Bad) New.card))
  have hBadR : (Bad.card : ℝ) ≤ 2*(d : ℝ) := by exact_mod_cast hBad
  change _ ≤ (New.card : ℝ)
  linarith

#print axioms commonNbr_pool_after_vertex_and_edge_payment
end TypedTriangle.Vortex
