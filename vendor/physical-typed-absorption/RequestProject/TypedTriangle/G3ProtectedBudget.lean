/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeSharedResources
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
open SelSimul

/-- Charge the inherited stock, the new reserve and the positive selector
once each against the *same* protected-bank window on W. The inherited-stock
coefficient `θ` need not depend on the thin selector coefficient `τ`. -/
theorem protected_bank_cap_of_three_resources {V : Type} [Fintype V]
    (W : Finset V) (S D R : Finset (Sym2 V)) (q θ ρ τ η : ℝ)
    (hW : q*Fintype.card V/2 ≤ W.card)
    (hbudget : θ+ρ+τ ≤ η*q/2)
    (hη : 0 ≤ η)
    (hS : ∀ v, (SparseEdge.degIn S v:ℝ) ≤ θ*Fintype.card V)
    (hD : ∀ v, (SparseEdge.degIn D v:ℝ) ≤ ρ*Fintype.card V)
    (hR : ∀ v, (SparseEdge.degIn R v:ℝ) ≤ τ*Fintype.card V) :
    ∀ v, (SparseEdge.degIn ((S∪D)∪R) v:ℝ) ≤ η*W.card := by
  intro v
  have h1 := SelSimul.edeg_union_le (S∪D) R v
  have h2 := SelSimul.edeg_union_le S D v
  change SparseEdge.degIn ((S∪D)∪R) v ≤
    SparseEdge.degIn (S∪D) v + SparseEdge.degIn R v at h1
  change SparseEdge.degIn (S∪D) v ≤
    SparseEdge.degIn S v + SparseEdge.degIn D v at h2
  have hu : (SparseEdge.degIn ((S∪D)∪R) v:ℝ) ≤
      SparseEdge.degIn S v + SparseEdge.degIn D v + SparseEdge.degIn R v := by
    exact_mod_cast (show SparseEdge.degIn ((S∪D)∪R) v ≤
      SparseEdge.degIn S v + SparseEdge.degIn D v + SparseEdge.degIn R v by omega)
  have hn : (0:ℝ) ≤ Fintype.card V := by positivity
  have hb := mul_le_mul_of_nonneg_right hbudget hn
  have hw := mul_le_mul_of_nonneg_left hW hη
  nlinarith only [hu,hS v,hD v,hR v,hb,hw]

end TypedTriangle.CatalogNative
