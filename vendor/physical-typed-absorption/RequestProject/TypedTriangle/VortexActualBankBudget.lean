/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4SampledReferenceComplement
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false

namespace TypedTriangle.Vortex
open BasalIncidence

/-- The actual stock, selector, old terminal stock and bank fit the original
sampled-complement tolerance. The floor avoids an additive rounding cost. -/
theorem actual_bank_union_budget {V : Type} [Fintype V]
    (D : Finset (Finset V)) (R T Bank : Finset (Sym2 V))
    (W Wcore : Finset V) (q ε : ℝ) (hq : 0 < q)
    (hqε : 4 * q ≤ ε) (hCore : Wcore ⊆ W)
    (hW : (W.card : ℝ) ≤ 2 * q * Fintype.card V)
    (hD : ∀ v, (SparseEdge.degIn (cover D) v : ℝ) ≤ q / 64 * Fintype.card V)
    (hR : ∀ v, (SparseEdge.degIn R v : ℝ) ≤ q / 64 * Fintype.card V)
    (hT : ∀ v, (SparseEdge.degIn T v : ℝ) ≤ q / 64 * Fintype.card V)
    (hBank : ∀ v, (SparseEdge.degIn Bank v : ℝ) ≤ (Wcore.card : ℝ) / 4) :
    ∃ dU : ℕ,
      (∀ v, SparseEdge.degIn (((cover D ∪ R) ∪ T) ∪ Bank) v ≤ dU) ∧
      ((dU + W.card : ℕ) : ℝ) ≤ ε * Fintype.card V := by
  have hCoreCard : (Wcore.card : ℝ) ≤ W.card := by
    exact_mod_cast Finset.card_le_card hCore
  have hU : ∀ v, (SparseEdge.degIn (((cover D ∪ R) ∪ T) ∪ Bank) v : ℝ) ≤
      q * Fintype.card V := by
    intro v
    have h1 := SelSimul.edeg_union_le (cover D) R v
    have h2 := SelSimul.edeg_union_le (cover D ∪ R) T v
    have h3 := SelSimul.edeg_union_le ((cover D ∪ R) ∪ T) Bank v
    change SparseEdge.degIn (cover D ∪ R) v ≤
      SparseEdge.degIn (cover D) v + SparseEdge.degIn R v at h1
    change SparseEdge.degIn ((cover D ∪ R) ∪ T) v ≤
      SparseEdge.degIn (cover D ∪ R) v + SparseEdge.degIn T v at h2
    change SparseEdge.degIn (((cover D ∪ R) ∪ T) ∪ Bank) v ≤
      SparseEdge.degIn ((cover D ∪ R) ∪ T) v + SparseEdge.degIn Bank v at h3
    have hNat := h3.trans (Nat.add_le_add_right
      (h2.trans (Nat.add_le_add_right h1 _)) _)
    have hReal : (SparseEdge.degIn (((cover D ∪ R) ∪ T) ∪ Bank) v : ℝ) ≤
        SparseEdge.degIn (cover D) v + SparseEdge.degIn R v +
          SparseEdge.degIn T v + SparseEdge.degIn Bank v := by
      exact_mod_cast hNat
    have hd := hD v
    have hr := hR v
    have ht := hT v
    have hb := hBank v
    have hqn : 0 ≤ q * Fintype.card V := by positivity
    nlinarith
  let dU := ⌊q * Fintype.card V⌋₊
  refine ⟨dU,fun v => Nat.le_floor (hU v),?_⟩
  have hdU : (dU : ℝ) ≤ q * Fintype.card V := Nat.floor_le (by positivity)
  have hScale := mul_le_mul_of_nonneg_right hqε
    (show (0 : ℝ) ≤ Fintype.card V by positivity)
  push_cast
  nlinarith

#print axioms actual_bank_union_budget

end TypedTriangle.Vortex
