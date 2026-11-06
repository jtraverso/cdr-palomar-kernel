/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativePreparedTerminalAbsorber
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false

namespace TypedTriangle.Vortex

/-- The stock and bank tolerances precede the inner sampling rate. Their
structured future-clique costs are paid relative to the ambient host and
the resource window respectively, with no selector degree cap for that clique. -/
theorem structured_future_core_budgets (γ ηBank ρFuture : ℝ)
    (hγ : 0 < γ) (hηBank : 0 < ηBank) (hρFuture : 0 < ρFuture) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1/32 ∧
      ∀ {V : Type*} [Fintype V] (W U : Finset V) (S : Finset (Sym2 V)),
        (U.card : ℝ) ≤ 2*q*W.card →
        S ⊆ triEdges U →
        (W.card : ℝ)/2 ≤ (W \ U).card ∧
        (U.card : ℝ) ≤ ρFuture*W.card ∧
        (∀ v, (degIn S v : ℝ) ≤ γ*Fintype.card V) ∧
        (∀ v, (degIn S v : ℝ) ≤ ηBank/2*(W \ U).card) := by
  let q := min (1/32) (min (γ/4) (min (ηBank/16) (ρFuture/4)))
  have hq : 0 < q := lt_min (by norm_num)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hq32 : q ≤ 1/32 := min_le_left _ _
  have hqγ : 2*q ≤ γ := by
    have h : q ≤ γ/4 := (min_le_right (1/32 : ℝ)
      (min (γ/4) (min (ηBank/16) (ρFuture/4)))).trans
        (min_le_left (γ/4) (min (ηBank/16) (ρFuture/4)))
    linarith
  have hqη : 8*q ≤ ηBank := by
    have h : q ≤ ηBank/16 := (min_le_right (1/32 : ℝ)
      (min (γ/4) (min (ηBank/16) (ρFuture/4)))).trans
        ((min_le_right (γ/4) (min (ηBank/16) (ρFuture/4))).trans
          (min_le_left (ηBank/16) (ρFuture/4)))
    linarith
  have hqρ : 2*q ≤ ρFuture := by
    have h : q ≤ ρFuture/4 := (min_le_right (1/32 : ℝ)
      (min (γ/4) (min (ηBank/16) (ρFuture/4)))).trans
        ((min_le_right (γ/4) (min (ηBank/16) (ρFuture/4))).trans
          (min_le_right (ηBank/16) (ρFuture/4)))
    linarith
  refine ⟨q,hq,hq32,?_⟩
  intro V _ W U S hU hS
  have hCard : (W.card : ℝ) ≤ (W \ U).card + U.card := by
    exact_mod_cast (show W.card ≤ (W \ U).card + U.card from card_le_card_sdiff_add_card)
  have hWnonneg : (0 : ℝ) ≤ W.card := by positivity
  have hWhalf : (U.card : ℝ) ≤ (W.card : ℝ)/2 := by
    have h := mul_le_mul_of_nonneg_right hq32 hWnonneg
    nlinarith [hU]
  have hW0 : (W.card : ℝ)/2 ≤ (W \ U).card := by linarith
  have hDegree : ∀ v, (degIn S v : ℝ) ≤ U.card := by
    intro v
    have hFilter := card_le_card (filter_subset_filter (p := fun e : Sym2 V => v ∈ e) hS)
    exact_mod_cast hFilter.trans (S07V31.degIn_triEdges_le U v)
  have hWparent : (W.card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast (show W.card ≤ Fintype.card V by simpa using card_le_card (subset_univ W))
  refine ⟨hW0,hU.trans (mul_le_mul_of_nonneg_right hqρ hWnonneg),?_,?_⟩
  · intro v
    exact (hDegree v).trans (hU.trans
      ((mul_le_mul_of_nonneg_right hqγ hWnonneg).trans
        (mul_le_mul_of_nonneg_left hWparent hγ.le)))
  · intro v
    have hScale := mul_le_mul_of_nonneg_left hW0 (show (0 : ℝ) ≤ 4*q by positivity)
    have hCap := mul_le_mul_of_nonneg_right hqη
      (show (0 : ℝ) ≤ (W \ U).card by positivity)
    have hDeg := (hDegree v).trans hU
    nlinarith

#print axioms structured_future_core_budgets
end TypedTriangle.Vortex
