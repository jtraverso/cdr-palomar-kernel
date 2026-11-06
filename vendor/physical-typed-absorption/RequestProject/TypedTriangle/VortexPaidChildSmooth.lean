/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexPaidPreparedOrder
public import RequestProject.TypedTriangle.VortexPreparedSmooth
public import RequestProject.TypedTriangle.VariablePreparedAlpha
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A smooth inverse on the actual edge-paid child, with its order threshold
chosen before the host. The child geometry is supplied separately by the
edge-payment theorem. No second vertex deletion is made. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex

theorem smooth_on_paid_prepared_child (α β : ℝ) (h : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hβhalf : β ≤ 1 / 2) (hh : 6 ≤ h) :
    ∃ K : ℝ, 0 < K ∧ ∃ η : ℝ, 0 < η ∧ ∃ Nbase Ns n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V →
        Dispersal.PreparedCore H.G H.lab F α h (max Nbase Ns) β →
        CommonNbrCond H F α → HingeCond H F α h →
        ∀ (B : Finset (Sym2 V)) (d : ℕ), B ⊆ edges H →
          (∀ v, SparseEdge.degIn B v ≤ d) →
          (d : ℝ) ≤ η * Fintype.card V →
          let J := subHost H (edges H \ B)
          CommonNbrCond J F (min (α / 2) (S07V49.hingeConstB α 1 h)) →
          HingeCond J F (min (α / 2) (S07V49.hingeConstB α 1 h))
            (2 * h - 3) →
          NativeSmooth.Smooth J F K := by
  let αp := min (α / 2) (S07V49.hingeConstB α 1 h)
  let hp := 2 * h - 3
  have hαp : 0 < αp := by
    dsimp [αp]
    exact lt_min (by positivity)
      (S07V49.hingeConstB_pos hα (by norm_num) (by omega))
  have hhp : 6 ≤ hp := by dsimp [hp]; omega
  obtain ⟨K, hK, Ns, n₀, hSmooth⟩ :=
    NativeSmooth.smooth_on_prepared_host αp β hp hαp hβ hhp
  obtain ⟨η, hη, Nbase, hPaid⟩ :=
    paid_prepared_core_with_required_order α h hα hh
  refine ⟨K, hK, η, hη, Nbase, Ns, n₀, ?_⟩
  intro V I _ H F hn P h3 h4 B d hBE hDeg hSmall
  dsimp only
  intro h3J h4J
  let J := subHost H (edges H \ B)
  have Q : Dispersal.PreparedCore J.G J.lab F αp hp
      (max Nbase Ns) β := by
    exact hPaid H F Ns β hβ hβhalf P h3 h4 B d hBE hDeg hSmall
  have Qweak : Dispersal.PreparedCore J.G J.lab F (αp / 4) hp Ns β := by
    have Qα := Dispersal.preparedCore_weaken_alpha
      (show αp / 4 ≤ αp by linarith) Q
    exact
      { h3 := Qα.h3
        h4 := Qα.h4
        order := fun Z hZ => (le_max_right Nbase Ns).trans (Qα.order Z hZ)
        lattice_persist := Qα.lattice_persist }
  exact hSmooth J F hn h3J h4J Qweak

#print axioms smooth_on_paid_prepared_child

end TypedTriangle.Vortex
