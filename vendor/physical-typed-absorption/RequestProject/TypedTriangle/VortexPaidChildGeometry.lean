/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexEdgeCommonNoSeed
public import RequestProject.TypedTriangle.VortexEdgeHingeNoSeed
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! A single sparse payment leaves both H3 and H4 on its actual complement.
This is geometric re-entry; H1 and H2 are handled on the paid child separately. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem geometry_after_edge_payment_uniform (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type*} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (B : Finset (Sym2 V)) (d : ℕ),
        n₀ ≤ Fintype.card V →
        CommonNbrCond H F α → HingeCond H F α h →
        B ⊆ edges H →
        (∀ v, SparseEdge.degIn B v ≤ d) →
        (d : ℝ) ≤ η * Fintype.card V →
        CommonNbrCond (subHost H (edges H \ B)) F (α / 2) ∧
        HingeCond (subHost H (edges H \ B)) F
          (S07V49.hingeConstB α 1 h) (2*h-3) := by
  obtain ⟨η3,hη3,h3⟩ := commonNbr_after_edge_payment_uniform α hα
  obtain ⟨η4,hη4,n₀,h4⟩ :=
    hinge_after_edge_set_deletion_no_seed_uniform α h hα hh
  refine ⟨min η3 η4, lt_min hη3 hη4, n₀, ?_⟩
  intro V I _ H F B d hnCard hH3 hH4 hBE hDeg hSmall
  have hnReal : (0 : ℝ) ≤ Fintype.card V := by positivity
  have h3Small : (d : ℝ) ≤ η3 * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hnReal)
  have h4Small : (d : ℝ) ≤ η4 * Fintype.card V :=
    hSmall.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hnReal)
  exact ⟨h3 H F B d hH3 hDeg h3Small,
    h4 H F hnCard hH3 hH4 B d hBE hDeg h4Small⟩

#print axioms geometry_after_edge_payment_uniform

end TypedTriangle.Vortex
