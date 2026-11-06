/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexWindowRouteRate
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace TypedTriangle.Vortex

/-- Fix the inner sampling rate and actual-state hole cap after the early
stock, bank and reference densities, and before the reference precision. -/
theorem exists_uniform_inner_rate (α a εOuter γStock ηBank ρFuture : ℝ) (h m : ℕ)
    (hα : 0 < α) (ha : 0 < a) (hε : 0 < εOuter)
    (hγ : 0 < γStock) (hη : 0 < ηBank) (hρ : 0 < ρFuture) (hm : 0 < m) :
    ∃ q ζState : ℝ, 0 < q ∧ q ≤ 1 / 32 ∧ 4*q ≤ εOuter ∧
      2*q ≤ ρFuture ∧ q ≤ ηBank/16 ∧ q ≤ γStock/8 ∧
      q ≤ α/(64*(2:ℝ)^h.choose 2) ∧
      q*m*(2:ℝ)^m ≤ a/64 ∧ 0 < ζState ∧
      ζState ≤ windowRouteRate a q m/4 ∧ ζState ≤ α*q/128 := by
  let q : ℝ := min (1/32) (min (εOuter/4) (min (ρFuture/2)
    (min (ηBank/16) (min (γStock/8)
      (min (α/(64*(2:ℝ)^h.choose 2)) (a/(64*(m:ℝ)*(2:ℝ)^m)))))))
  have hmReal : (0:ℝ) < m := by exact_mod_cast hm
  have hq : 0 < q := by dsimp [q]; positivity
  have hCaps : q ≤ 1/32 ∧ q ≤ εOuter/4 ∧ q ≤ ρFuture/2 ∧
      q ≤ ηBank/16 ∧ q ≤ γStock/8 ∧
      q ≤ α/(64*(2:ℝ)^h.choose 2) ∧ q ≤ a/(64*(m:ℝ)*(2:ℝ)^m) := by
    have hqAll : q ≤ min (1/32) (min (εOuter/4) (min (ρFuture/2)
        (min (ηBank/16) (min (γStock/8)
          (min (α/(64*(2:ℝ)^h.choose 2)) (a/(64*(m:ℝ)*(2:ℝ)^m))))))) := le_rfl
    simpa only [le_min_iff] using hqAll
  have hPath : q*m*(2:ℝ)^m ≤ a/64 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 64*(m:ℝ)*(2:ℝ)^m)).mp
      hCaps.2.2.2.2.2.2
    nlinarith
  let ζ := min (windowRouteRate a q m/4) (α*q/128)
  have hRate := windowRouteRate_pos m ha hq
  have hζ : 0 < ζ := lt_min (by positivity) (by positivity)
  refine ⟨q,ζ,hq,hCaps.1,?_,?_,hCaps.2.2.2.1,hCaps.2.2.2.2.1,
    hCaps.2.2.2.2.2.1,hPath,hζ,min_le_left _ _,min_le_right _ _⟩ <;> linarith [hCaps.2.1,hCaps.2.2.1]

#print axioms exists_uniform_inner_rate
end TypedTriangle.Vortex
