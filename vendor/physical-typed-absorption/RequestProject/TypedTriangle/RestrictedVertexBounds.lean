/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.RestrictedHingeGeometry

@[expose] public section

/-! Uniform quotient bounds after vertex deletion, from original H3--H4.
Local candidate; NOT kernel-checked. No remaining-host geometry is an input.
-/

open Finset
noncomputable section
open Classical

namespace TypedTriangle

variable {V : Type*} [Fintype V]

lemma card_survivors_add_card (Z : Finset V) :
    Fintype.card (Survivors Z) + Z.card = Fintype.card V := by
  have hN : Fintype.card (Survivors Z) = Fintype.card V - Z.card := by
    simpa only [Survivors, Fintype.card_coe] using
      Fintype.card_subtype_compl (fun v : V => v ∈ Z)
  have hZ : Z.card ≤ Fintype.card V := by
    simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ Z)
  omega

/-- Original-host H3--H4 supply uniform quotient bounds throughout a vertex-deletion window. -/
theorem physQuot_vertexDeleted_bounds_of_original_geometry (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ d T n₀ : ℕ, 1 ≤ T ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (Z : Finset V),
        n₀ ≤ Fintype.card V → CommonNbrCond H F α → HingeCond H F α h →
        (Z.card : ℝ) ≤ δ * Fintype.card V →
        Module.finrank ℤ (physQuot (vertexDeleted H Z) F) ≤ d ∧
          Nat.card (Submodule.torsion ℤ (physQuot (vertexDeleted H Z) F)) ≤ T := by
  obtain ⟨d,T,n₁,hT,hbound⟩ := physQuot_bounds_of_H3H4 (α/2) h (by positivity)
  obtain ⟨δ,hδ,hδhalf,hbudget⟩ := original_geometry_vertex_budget hα h
  refine ⟨δ,hδ,d,T,2*n₁,hT,fun {V I} _ H F Z hn hH3 hH4 hZ => ?_⟩
  obtain ⟨hZ3,hZ4⟩ := hbudget (show (0 : ℝ) ≤ Fintype.card V by positivity) hZ
  have hhalf : (Z.card : ℝ) ≤ (Fintype.card V : ℝ)/2 := by
    have := mul_le_mul_of_nonneg_right hδhalf
      (show (0 : ℝ) ≤ Fintype.card V by positivity)
    linarith
  have hhalfN : 2*Z.card ≤ Fintype.card V := by
    have : (2 : ℝ)*Z.card ≤ Fintype.card V := by linarith
    exact_mod_cast this
  have hcard := card_survivors_add_card Z
  have hN : n₁ ≤ Fintype.card (Survivors Z) := by omega
  have hg := original_geometry_restrictedHost hα.le hH3 hH4 Z hZ3 hZ4
  obtain ⟨hr,ht⟩ := hbound (restrictedHost H Z) F hN hg.1 hg.2
  exact physQuot_bounds_surviving_ambient H F Z d T hr ht

end TypedTriangle
