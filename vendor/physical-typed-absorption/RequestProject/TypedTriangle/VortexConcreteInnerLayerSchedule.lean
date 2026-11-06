/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexConcreteInnerLayerParameters
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Vortex

/-- Construct every scalar certificate of the concrete layer factory.
The future density precedes the state-hole tolerance and the reference cap;
the finite order threshold follows the actual reference precision list. -/
theorem exists_concrete_inner_layer_schedule {I : Type} (F : Set (Multiset I))
    (αRaw C : ℝ) (h L : ℕ) (hα : 0 < αRaw) (hC : 1 ≤ C) (hh : 6 ≤ h) :
    ∃ ρFuture : ℝ, 0 < ρFuture ∧
      ∀ cap ζState ηGlobal : ℝ, 0 < cap → 0 < ζState → 0 < ηGlobal →
      ∃ β : ℕ → ℝ, ∃ N : ℕ,
        (∀ j, 0 ≤ β j) ∧ (∀ j ≤ L, 0 < β j ∧ β j ≤ cap) ∧
        (∀ j < L, β j ≤ β (j+1)/2) ∧
        (∑ j ∈ range (L+1), β j) ≤ ηGlobal/2 ∧
        Nonempty (ConcreteInnerLayerSchedule F αRaw C ρFuture ζState β h N L) := by
  have hCpos : 0 < C := by linarith
  have ha : 0 < 3/(4*C) := by positivity
  have hab : 3/(4*C) ≤ 2*C := by
    apply (div_le_iff₀ (by positivity : 0 < 4*C)).mpr
    nlinarith
  obtain ⟨ρFuture,hρFuture,hMake⟩ := exists_global_naked_reference_schedule_early
    F (3/(4*C)) (2*C) αRaw C h L ha hab hα hC hh
  refine ⟨ρFuture,hρFuture,?_⟩
  intro cap ζState ηGlobal hcap hζ hGlobal
  let ηCap := min ζState (αRaw/(10*(2:ℝ)^h.choose 2))
  have hηCap : 0 < ηCap := lt_min hζ (by positivity)
  obtain ⟨nGeometry,K,ηSpec,ηHole,ζRef,εRef,γRef,Nbase,Ns,nPaid,nRef,hParameters,
    β,hβ,hβCap,hStep,hCross,hPrior,hSum,N,hNGeometry,hOrders⟩ :=
      hMake cap ηCap ηGlobal hcap hηCap hGlobal
  refine ⟨β,N,hβ,hβCap,hStep,hSum,?_⟩
  refine ⟨{
    K := fun r => K (β r)
    ηSpec := fun r => ηSpec (β r)
    ζRef := fun r => ζRef (β r)
    εRef := fun r => εRef (β r)
    γRef := fun r => γRef (β r)
    Nbase := fun r => Nbase (β r)
    Ns := fun r => Ns (β r)
    nPaid := fun r => nPaid (β r)
    nRef := fun r => nRef (β r)
    nGeometry := nGeometry
    K_pos := ?_
    ηSpec_pos := ?_
    ζRef_pos := ?_
    εRef_pos := ?_
    γRef_pos := ?_
    ref_state := ?_
    ref_spec := ?_
    ref_clean := ?_
    paid_cap := ?_
    paid_smooth := ?_
    reference := ?_
    orders := by
      intro r hr
      exact hOrders ⟨r,by omega⟩
    geometry_order := hNGeometry
    hole_inverse := ?_
    prefix_inverse := by
      intro r hr
      convert (hPrior r hr).1 using 1 <;> ring
    prefix_reference := by
      intro r hr
      convert (hPrior r hr).2 using 1 <;> ring }⟩
  all_goals
    intro r hr
    obtain ⟨hK,hηSpec,hDom,hCap,hSmooth,hHoleEq,hHolePos,hHoleMax,hHoleInv,
      hRefPos,hRefCap,hRefMax,hRefHole,hRefBudget,hε,hγ,hReference⟩ :=
        hParameters (β r) (hβCap r hr).1
    have hState : ζRef (β r) ≤ ζState := hRefCap.trans (min_le_left _ _)
    have hCleanCap : ζRef (β r) ≤ αRaw/(10*(2:ℝ)^h.choose 2) :=
      hRefCap.trans (min_le_right _ _)
    have hSpec : ζRef (β r) ≤ ηSpec (β r) := by linarith
    have hInverse : K (β r)*(8*C*ζRef (β r)) ≤ 1/(16*C) := by
      calc
        K (β r)*(8*C*ζRef (β r)) ≤ K (β r)*(8*C*ηHole (β r)) := by
          gcongr
          linarith
        _ = 1/(16*C) := hHoleInv
    assumption

#print axioms exists_concrete_inner_layer_schedule
end TypedTriangle.Vortex
