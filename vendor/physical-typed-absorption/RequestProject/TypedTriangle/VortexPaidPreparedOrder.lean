/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexPaidPreparedCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Edge payment changes the geometric and lattice clauses of a prepared
core, but not its vertex type. A parent order bound can therefore be retained
when the paid child is built. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

theorem paid_prepared_core_with_required_order (α : ℝ) (h : ℕ)
    (hα : 0 < α) (hh : 6 ≤ h) :
    ∃ η : ℝ, 0 < η ∧ ∃ Nbase : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (Nreq : ℕ) (β : ℝ),
        0 < β → β ≤ 1 / 2 →
        Dispersal.PreparedCore H.G H.lab F α h (max Nbase Nreq) β →
        CommonNbrCond H F α → HingeCond H F α h →
        ∀ (B : Finset (Sym2 V)) (d : ℕ), B ⊆ edges H →
          (∀ v, SparseEdge.degIn B v ≤ d) →
          (d : ℝ) ≤ η * Fintype.card V →
          Dispersal.PreparedCore
            (subHost H (edges H \ B)).G (subHost H (edges H \ B)).lab F
            (min (α / 2) (S07V49.hingeConstB α 1 h)) (2 * h - 3)
            (max Nbase Nreq) β := by
  obtain ⟨η, hη, Nbase, hpaid⟩ := paid_prepared_core_uniform α h hα hh
  refine ⟨η, hη, Nbase, ?_⟩
  intro V I _ H F Nreq β hβ hβhalf P h3 h4 B d hBE hDeg hSmall
  have Pbase : Dispersal.PreparedCore H.G H.lab F α h Nbase β :=
    { h3 := P.h3
      h4 := P.h4
      order := fun Z hZ => (le_max_left Nbase Nreq).trans (P.order Z hZ)
      lattice_persist := P.lattice_persist }
  have Qbase := hpaid H F β hβ hβhalf Pbase h3 h4 B d hBE hDeg hSmall
  exact
    { h3 := Qbase.h3
      h4 := Qbase.h4
      order := P.order
      lattice_persist := Qbase.lattice_persist }

#print axioms paid_prepared_core_with_required_order

end TypedTriangle.Vortex
