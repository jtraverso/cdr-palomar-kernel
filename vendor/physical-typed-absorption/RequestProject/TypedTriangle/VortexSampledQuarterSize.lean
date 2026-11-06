/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexSubtypeLift
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The adaptive preparation retains a quarter-size window for the
existing positive raw-weight interface. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem sampled_quarter_size_after_relative_trim {V : Type} [Fintype V]
    (W : Finset V) (A : Finset (Survivors (univ \ W)))
    (q τ : ℝ) (hW : q * Fintype.card V / 2 ≤ W.card)
    (hA : (A.card : ℝ) ≤ τ * W.card) (hτ : τ ≤ 1 / 2) :
    q * Fintype.card V / 4 ≤
      (W \ liftVertexSet (univ \ W) A).card := by
  have hgeom := lifted_prepared_deletion_geometry W A
  have hcard : (W \ liftVertexSet (univ \ W) A).card +
      (liftVertexSet (univ \ W) A).card = W.card :=
    card_sdiff_add_card_eq_card hgeom.2.1
  rw [hgeom.1] at hcard
  have hcardR : ((W \ liftVertexSet (univ \ W) A).card : ℝ) +
      A.card = W.card := by exact_mod_cast hcard
  have hτW := mul_le_mul_of_nonneg_right hτ
    (show (0 : ℝ) ≤ W.card by positivity)
  have hAhalf : (A.card : ℝ) ≤ W.card / 2 :=
    hA.trans (by nlinarith [hτW])
  nlinarith

#print axioms sampled_quarter_size_after_relative_trim

end TypedTriangle.Vortex
