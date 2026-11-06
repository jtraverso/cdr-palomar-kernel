/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.PhysicalResidual

@[expose] public section

/-! Uniform H3 re-entry after a sparse edge payment. The input need not
carry a diffuse seed; the exact seed is recovered later on the paid child. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem commonNbr_after_edge_payment_uniform (α : ℝ) (hα : 0 < α) :
    ∃ η : ℝ, 0 < η ∧
      ∀ {V I : Type*} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (B : Finset (Sym2 V)) (d : ℕ),
        CommonNbrCond H F α →
        (∀ v, SparseEdge.degIn B v ≤ d) →
        (d : ℝ) ≤ η * Fintype.card V →
        CommonNbrCond (subHost H (edges H \ B)) F (α / 2) := by
  refine ⟨α / 4, by positivity, ?_⟩
  intro V I _ H F B d h3 hdeg hsmall
  apply TypedTriangle.Residual.commonNbrCond_sdiff h3 B d hdeg
  exact_mod_cast (show (4 : ℝ) * d ≤ α * Fintype.card V by nlinarith [hsmall])

#print axioms commonNbr_after_edge_payment_uniform

end TypedTriangle.Vortex
