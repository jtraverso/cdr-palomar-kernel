/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexScheduledPreparedBankBridge
public import RequestProject.TypedTriangle.VortexSampleRenormalize
public import RequestProject.TypedTriangle.VortexSampleTrimming
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section

namespace TypedTriangle.Vortex

/-- A relative first-entry deletion preserves the quantitative completion
pool and halves the route tolerance on the same sampled window. The extra
restriction `τ≤α/16` is a choice of the proof's trim budget, not a stronger
host hypothesis. -/
theorem scheduled_pool_route_after_relative_trim {V I : Type*} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    (A : Finset (Survivors (univ \ W))) (q α ε τ : ℝ) (t : ℕ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hα : 0 < α)
    (hε : 0 < ε) (hτ : 0 ≤ τ)
    (hτq : τ ≤ q / 8) (hτα : τ ≤ α / 16)
    (hτε : τ ≤ ε / 4)
    (hWlo : q * Fintype.card V / 2 ≤ W.card)
    (hWhi : (W.card : ℝ) < 2 * q * Fintype.card V)
    (hA : (A.card : ℝ) ≤ τ * W.card)
    (hRoute : S07V27.RouteProp H.G H.lab F t ε W)
    (hPool : ∀ u v : V, u ≠ v → ∀ k : I,
      ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
      q * α * Fintype.card V / 2 ≤
        ((commonNbrs H k u v) ∩ W).card) :
    let W' := W \ liftVertexSet (univ \ W) A
    (q / 2) * Fintype.card V / 2 ≤ W'.card ∧
    S07V27.RouteProp H.G H.lab F t (ε / 2) W' ∧
    ∀ u v : V, u ≠ v → ∀ k : I,
      ({H.lab u, H.lab v, k} : Multiset I) ∈ F →
      (q / 2) * (α / 2) * Fintype.card V / 2 ≤
        ((commonNbrs H k u v) ∩ W').card := by
  let Aamb := liftVertexSet (univ \ W) A
  let W' := W \ Aamb
  have hAc : Aamb.card = A.card := card_liftVertexSet (univ \ W) A
  have hAambient : (Aamb.card : ℝ) ≤ (2 * q * τ) * Fintype.card V := by
    rw [hAc]
    have hτW := mul_le_mul_of_nonneg_left hWhi.le hτ
    nlinarith [hA,hτW]
  have hAroute : (Aamb.card : ℝ) ≤ ε / 2 * Fintype.card V := by
    have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
    have hcap : 2 * q * τ ≤ ε / 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hτ]
    nlinarith [mul_le_mul_of_nonneg_right hcap hn, hAambient]
  have hAalpha : 4 * (2 * q * τ) ≤ q * α := by
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr (show 8*τ ≤ α by linarith))]
  have hPool' := completion_pool_after_trim H F W Aamb q α (2*q*τ)
    hα (by positivity) hAalpha hAambient hPool
  have hquarter : q * Fintype.card V / 4 ≤ W'.card := by
    have hgeom := lifted_prepared_deletion_geometry W A
    have hcard : W'.card + A.card = W.card := by
      simpa only [W', Aamb, hgeom.1] using
        (card_sdiff_add_card_eq_card hgeom.2.1)
    have hcardR : (W'.card : ℝ) + A.card = W.card := by
      exact_mod_cast hcard
    have hτhalf : τ ≤ 1/2 := by nlinarith [hτq,hq1]
    have hτW := mul_le_mul_of_nonneg_right hτhalf
      (show (0 : ℝ) ≤ W.card by positivity)
    nlinarith [hA,hτW,hWlo]
  refine ⟨?_, routeProp_sdiff hε.le hRoute Aamb hAroute, ?_⟩
  · convert hquarter using 1 <;> ring
  · intro u v huv k hk
    have hp := hPool' u v huv k hk
    have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
    have hτsmall : 4*τ ≤ 1/2 := by nlinarith [hτq,hq1]
    nlinarith [mul_nonneg (sub_nonneg.mpr hτsmall) hn]

#print axioms scheduled_pool_route_after_relative_trim

end TypedTriangle.Vortex
