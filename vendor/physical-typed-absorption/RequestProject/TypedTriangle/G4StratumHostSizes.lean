/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4StrataGeometry
public import RequestProject.TypedTriangle.RestrictedVertexBounds
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The core sample bound keeps both localization hosts above their threshold. -/

open Finset Classical
noncomputable section

namespace TypedTriangle

theorem native_stratum_host_sizes {V : Type*} [Fintype V]
    (W outer bad : Finset V) (hW : W = univ \ outer)
    (z n₀ : ℕ) (q : ℝ)
    (hbad : bad.card ≤ z) (hz : (z : ℝ) ≤ W.card / 2)
    (hWlo : q * Fintype.card V / 2 ≤ W.card)
    (hn₀ : (n₀ : ℝ) ≤ q * Fintype.card V / 4) :
    n₀ ≤ Fintype.card (Survivors bad) ∧
      n₀ ≤ Fintype.card (Survivors (outer ∪ bad)) := by
  have hOuter := card_survivors_add_card outer
  have hBad := card_survivors_add_card bad
  have hJoint := card_survivors_add_card (outer ∪ bad)
  have hWcard : W.card + outer.card = Fintype.card V := by
    rw [hW]
    simpa only [card_univ] using
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ outer))
  have hUnion : (outer ∪ bad).card ≤ outer.card + bad.card :=
    Finset.card_union_le outer bad
  have hBadUnion : bad.card ≤ (outer ∪ bad).card :=
    Finset.card_le_card (Finset.subset_union_right)
  have hReal : (n₀ : ℝ) ≤ Fintype.card (Survivors (outer ∪ bad)) := by
    have h₁ : (bad.card : ℝ) ≤ z := by exact_mod_cast hbad
    have h₂ : ((outer ∪ bad).card : ℝ) ≤ outer.card + bad.card := by
      exact_mod_cast hUnion
    have h₃ : (Fintype.card (Survivors (outer ∪ bad)) : ℝ) +
        (outer ∪ bad).card = Fintype.card V := by exact_mod_cast hJoint
    have h₄ : (W.card : ℝ) + outer.card = Fintype.card V := by
      exact_mod_cast hWcard
    nlinarith only [h₁, h₂, h₃, h₄, hz, hWlo, hn₀]
  have hNJoint : n₀ ≤ Fintype.card (Survivors (outer ∪ bad)) := by
    exact_mod_cast hReal
  have hNBad : Fintype.card (Survivors (outer ∪ bad)) ≤
      Fintype.card (Survivors bad) := by omega
  exact ⟨hNJoint.trans hNBad, hNJoint⟩

theorem native_stratum_deletion_window {V : Type*} [Fintype V]
    (W outer bad : Finset V) (hW : W = univ \ outer)
    (z : ℕ) (β : ℝ) (h : ℕ) (hbad : bad.card ≤ z)
    (hz : (z : ℝ) ≤ S07V37.delOf (β/2) h * W.card) :
    ((bad.subtype (· ∉ outer)).card : ℝ) ≤
      S07V37.delOf (β/2) h * Fintype.card (Survivors outer) := by
  have hWcard : W.card + outer.card = Fintype.card V := by
    rw [hW]
    simpa only [card_univ] using
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ outer))
  have hSurv : Fintype.card (Survivors outer) = W.card := by
    have hc := card_survivors_add_card outer
    omega
  have hsub : (bad.subtype (· ∉ outer)).card ≤ bad.card := by
    rw [Finset.card_subtype]
    exact Finset.card_filter_le _ _
  have hsubR : ((bad.subtype (· ∉ outer)).card : ℝ) ≤ bad.card := by
    exact_mod_cast hsub
  have hbadR : (bad.card : ℝ) ≤ z := by exact_mod_cast hbad
  rw [hSurv]
  exact hsubR.trans (hbadR.trans hz)

end TypedTriangle

#print axioms TypedTriangle.native_stratum_host_sizes
#print axioms TypedTriangle.native_stratum_deletion_window
