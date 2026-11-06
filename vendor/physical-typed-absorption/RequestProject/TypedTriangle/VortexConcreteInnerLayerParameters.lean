/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexGlobalNakedReferenceScheduleEarly
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Vortex

/-- Only the globally scheduled scalar certificates used by the concrete
inner-layer factory. This contains no host, local-step or packing provider.
Its fields are outputs of the actual early naked-reference agenda. -/
structure ConcreteInnerLayerSchedule {I : Type} (F : Set (Multiset I))
    (αRaw C ρFuture ζState : ℝ) (β : ℕ → ℝ) (h N L : ℕ) where
  K : ℕ → ℝ
  ηSpec : ℕ → ℝ
  ζRef : ℕ → ℝ
  εRef : ℕ → ℝ
  γRef : ℕ → ℝ
  Nbase : ℕ → ℕ
  Ns : ℕ → ℕ
  nPaid : ℕ → ℕ
  nRef : ℕ → ℕ
  nGeometry : ℕ
  K_pos : ∀ r ≤ L, 0 < K r
  ηSpec_pos : ∀ r ≤ L, 0 < ηSpec r
  ζRef_pos : ∀ r ≤ L, 0 < ζRef r
  εRef_pos : ∀ r ≤ L, 0 < εRef r
  γRef_pos : ∀ r ≤ L, 0 < γRef r
  ref_state : ∀ r ≤ L, ζRef r ≤ ζState
  ref_spec : ∀ r ≤ L, ζRef r ≤ ηSpec r
  ref_clean : ∀ r ≤ L, ζRef r ≤ αRaw/(10*(2:ℝ)^h.choose 2)
  paid_cap : ∀ r ≤ L, PaidReferenceCap αRaw h (ηSpec r) nGeometry
  paid_smooth : ∀ r ≤ L,
    PaidSmoothAt αRaw (β r) (K r) (ηSpec r) h (Nbase r) (Ns r) (nPaid r)
  reference : ∀ r ≤ L,
    NakedReferenceAt F (3/(4*C)) (2*C) αRaw ρFuture (ζRef r)
      (εRef r) (γRef r) h (nRef r)
  orders : ∀ r ≤ L, max (max (max (Nbase r) (Ns r)) (nPaid r)) (nRef r) ≤ N
  geometry_order : nGeometry ≤ N
  hole_inverse : ∀ r ≤ L, K r*(8*C*ζRef r) ≤ 1/(16*C)
  prefix_inverse : ∀ r ≤ L,
    K r*(4*C*(∑ j ∈ range r,β j)) ≤ 1/(16*C)
  prefix_reference : ∀ r ≤ L,
    4*C*(∑ j ∈ range r,β j) ≤ εRef r/8

end TypedTriangle.Vortex
