/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.CertDispersal
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Lowering the geometric density required of a prepared core preserves its
integer persistence and order guarantees. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Dispersal

theorem preparedCore_weaken_alpha {V I : Type*} [Fintype V]
    {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {α α' β : ℝ} {h N : ℕ} (hα' : α' ≤ α)
    (P : PreparedCore G lab F α h N β) :
    PreparedCore G lab F α' h N β := by
  refine ⟨?_, ?_, P.order, P.lattice_persist⟩
  · intro Z hZ u v huv k hk
    have hOld := P.h3 Z hZ u v huv k hk
    have hn : (0 : ℝ) ≤ Fintype.card (Surv Z) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hα' hn
    exact hmul.trans hOld
  · intro Z hZ u v a b hab ha hb
    obtain ⟨i, hi6, hih, hOld⟩ := P.h4 Z hZ u v a b hab ha hb
    refine ⟨i, hi6, hih, ?_⟩
    have hn : (0 : ℝ) ≤ (Fintype.card (Surv Z) : ℝ) ^ (i - 4) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hα' hn
    exact hmul.trans hOld

#print axioms preparedCore_weaken_alpha

end TypedTriangle.Dispersal
