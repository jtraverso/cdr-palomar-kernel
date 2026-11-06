/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexConcreteInnerLayerSchedule
public import RequestProject.TypedTriangle.VortexUniformInnerRate
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Vortex

/-- Choose the actual global agenda after both path lengths are known.
The inner rate pays the outer path loss too; the outer sampling rate and
the terminal reserve order have not yet been chosen. -/
theorem exists_global_assembly_parameters {I : Type} (F : Set (Multiset I))
    (α C ε δOuter εBank γStock ηBank aInner aOuter : ℝ) (h L mInner mOuter : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hh : 6 ≤ h) (hε : 0 < ε)
    (hδ : 0 < δOuter) (hBank : 0 < εBank) (hStock : 0 < γStock)
    (hηBank : 0 < ηBank) (haInner : 0 < aInner) (haOuter : 0 < aOuter)
    (hmInner : 0 < mInner) (hmOuter : 0 < mOuter) :
    ∃ ρ q ζ B : ℝ, ∃ β : ℕ → ℝ, ∃ N : ℕ,
      0 < ρ ∧ 0 < q ∧ q ≤ 1/32 ∧ 4*q ≤ εBank ∧
      2*q ≤ ρ ∧ q ≤ ηBank/16 ∧ q ≤ γStock/8 ∧
      q ≤ α/(64*(2:ℝ)^h.choose 2) ∧
      q*mInner*(2:ℝ)^mInner ≤ aInner/64 ∧
      q*mOuter*(2:ℝ)^mOuter ≤ aOuter/128 ∧
      0 < ζ ∧ ζ ≤ windowRouteRate aInner q mInner/4 ∧ ζ ≤ α*q/128 ∧
      0 < B ∧ B ≤ 1/8 ∧ B ≤ α/128 ∧
      B*mInner*(2:ℝ)^mInner ≤ aInner/64 ∧
      B*mOuter*(2:ℝ)^mOuter ≤ aOuter/128 ∧
      B ≤ min δOuter (min ε (min (α/(4*(2:ℝ)^h.choose 2)) (1/(8*max 1 (2*C))))) ∧
      (∀ j, 0 ≤ β j) ∧ (∀ j ≤ L, 0 < β j ∧ β j ≤ ε) ∧
      (∑ j ∈ range (L+1), β j) ≤ B ∧
      Nonempty (ConcreteInnerLayerSchedule F (α/8) C ρ ζ β h N L) := by
  have hmI : (0:ℝ) < mInner := by exact_mod_cast hmInner
  have hmO : (0:ℝ) < mOuter := by exact_mod_cast hmOuter
  let prepCap := min δOuter (min ε (min (α/(4*(2:ℝ)^h.choose 2)) (1/(8*max 1 (2*C)))))
  have hPrep : 0 < prepCap := by dsimp [prepCap]; positivity
  let B : ℝ := min (1/8) (min (α/128)
    (min (aInner/(64*(mInner:ℝ)*(2:ℝ)^mInner))
      (min (aOuter/(128*(mOuter:ℝ)*(2:ℝ)^mOuter)) prepCap)))
  have hB : 0 < B := by dsimp [B]; positivity
  have hBCaps : B ≤ 1/8 ∧ B ≤ α/128 ∧
      B ≤ aInner/(64*(mInner:ℝ)*(2:ℝ)^mInner) ∧
      B ≤ aOuter/(128*(mOuter:ℝ)*(2:ℝ)^mOuter) ∧ B ≤ prepCap := by
    have hAll : B ≤ min (1/8) (min (α/128)
        (min (aInner/(64*(mInner:ℝ)*(2:ℝ)^mInner))
          (min (aOuter/(128*(mOuter:ℝ)*(2:ℝ)^mOuter)) prepCap))) := le_rfl
    simpa only [le_min_iff] using hAll
  have hBInner : B*mInner*(2:ℝ)^mInner ≤ aInner/64 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 64*(mInner:ℝ)*(2:ℝ)^mInner)).mp
      hBCaps.2.2.1
    nlinarith
  have hBOuter : B*mOuter*(2:ℝ)^mOuter ≤ aOuter/128 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 128*(mOuter:ℝ)*(2:ℝ)^mOuter)).mp
      hBCaps.2.2.2.1
    nlinarith
  obtain ⟨ρ,hρ,hAgenda⟩ := exists_concrete_inner_layer_schedule F (α/8) C h L
    (by positivity) hC hh
  let εAdjusted := min εBank (aOuter/(32*(mOuter:ℝ)*(2:ℝ)^mOuter))
  have hAdjusted : 0 < εAdjusted := lt_min hBank (by positivity)
  obtain ⟨q,ζ,hq,hq32,hqBank,hqρ,hqη,hqStock,hqα,hqInner,hζ,hζRoute,hζPool⟩ :=
    exists_uniform_inner_rate α aInner εAdjusted γStock ηBank ρ h mInner
      hα haInner hAdjusted hStock hηBank hρ hmInner
  have hqOuter : q*mOuter*(2:ℝ)^mOuter ≤ aOuter/128 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 32*(mOuter:ℝ)*(2:ℝ)^mOuter)).mp
      (hqBank.trans (min_le_right _ _))
    nlinarith
  obtain ⟨β,N,hβ,hβCap,hStep,hSum,hSchedule⟩ := hAgenda ε ζ (2*B) hε hζ (by positivity)
  have hTotal : (∑ j ∈ range (L+1), β j) ≤ B := by linarith
  exact ⟨ρ,q,ζ,B,β,N,hρ,hq,hq32,hqBank.trans (min_le_left _ _),hqρ,hqη,hqStock,hqα,
    hqInner,hqOuter,hζ,hζRoute,hζPool,hB,hBCaps.1,hBCaps.2.1,hBInner,hBOuter,
    hBCaps.2.2.2.2,hβ,hβCap,hTotal,hSchedule⟩

#print axioms exists_global_assembly_parameters
end TypedTriangle.Vortex
