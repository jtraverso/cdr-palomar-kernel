/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.VortexLossBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Relative sample counts give a child H3/H4 constant with an additive
loss budget. The simultaneous sample event is an input here. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem relative_sample_child_geometry {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) {α q η : ℝ} {h : ℕ}
    (hα : 0 < α) (hq : 0 < q) (hη : 0 ≤ η)
    (hη1 : η < 1) (hh : 1 ≤ h)
    (hH4 : HingeCond H F α h) (W : Finset V)
    (hW : (W.card : ℝ) ≤ (1 + η) * q * Fintype.card V)
    (hpool : ∀ u v, u ≠ v → ∀ k,
      ({H.lab u,H.lab v,k} : Multiset I) ∈ F →
      (1 - η) * α * q * Fintype.card V ≤
        ((commonNbrs H k u v) ∩ W).card)
    (hhinge : ∀ u v a b,
      S07V24.HingeTest H.G H.lab F u v a b →
      (1 - η) * α * q ^ (S07V24.hOrd hH4 u v a b - 4) *
        (Fintype.card V : ℝ) ^ (S07V24.hOrd hH4 u v a b - 4) ≤
          ((SparseEdge.hinges H.G H.lab F u v a b
            (S07V24.hOrd hH4 u v a b)).filter
              (fun J => S07V24.freeV u v a b J ⊆ W)).card) :
    CommonNbrCond (restrictedHost H (univ \ W)) F
      (α * (1 - ((h : ℝ) + 1) * η)) ∧
    HingeCond (restrictedHost H (univ \ W)) F
      (α * (1 - ((h : ℝ) + 1) * η)) h := by
  have hc : 0 < 1 - η := by linarith
  have hr : 1 ≤ 1 + η := by linarith
  have hGeom := CorePaid.sampled_core_geometry_scaled H F hα hq hc hr hh hH4 W
    hW hpool hhinge
  have hbound : α * (1 - ((h : ℝ) + 1) * η) ≤
      (1 - η) * α / (1 + η) ^ h := by
    have hs := one_step_relative_geometry_loss h hη
    have hscaled := mul_le_mul_of_nonneg_left hs hα.le
    convert hscaled using 1 <;> ring
  exact ⟨commonNbrCond_mono hGeom.1 hbound,
    hingeCond_mono hGeom.2 hbound⟩

#print axioms relative_sample_child_geometry

end TypedTriangle.Vortex
