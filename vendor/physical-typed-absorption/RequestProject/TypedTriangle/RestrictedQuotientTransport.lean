/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.RestrictedLocalGroup

@[expose] public section

/-!
# Transport quotient bounds to a fixed ambient vertex type

Local proof candidate; NOT kernel-checked in this campaign.
The geometry is explicitly required on the actual surviving subtype. Its H4
inheritance from the original host is a separate, still pending adapter.
-/

open Finset
noncomputable section
open Classical

namespace TypedTriangle
open Incidence

variable {V I : Type*} [Fintype V]

/-- Zero extension preserves the integer edge l1 norm exactly. -/
lemma l1E_edgeZeroExtend (Z : Finset V) (x : Sym2 (Survivors Z) → ℤ) :
    l1E (edgeZeroExtend Z x) = l1E x := by
  let S : Finset (Sym2 V) := univ.filter (fun e => ∀ v ∈ e, v ∉ Z)
  have hsum : (∑ e : Sym2 (Survivors Z), |x e|) = ∑ e ∈ S, |edgeZeroExtend Z x e| := by
    refine Finset.sum_bij (fun e _ => Sym2.map Subtype.val e) ?_ ?_ ?_ ?_
    · intro e _
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      intro v hv
      obtain ⟨w, -, rfl⟩ := Sym2.mem_map.1 hv
      exact w.2
    · intro e _ e' _ heq
      exact Sym2.map.injective Subtype.val_injective heq
    · intro e he
      have hav := (Finset.mem_filter.1 he).2
      exact ⟨e.attachWith hav, Finset.mem_univ _, Sym2.attachWith_map_subtypeVal hav⟩
    · intro e _
      rw [edgeZeroExtend_apply_map]
  have hout : ∑ e ∈ S, |edgeZeroExtend Z x e| = ∑ e : Sym2 V, |edgeZeroExtend Z x e| := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have hav : ¬ ∀ v ∈ e, v ∉ Z := fun h => he (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    push_neg at hav
    obtain ⟨v, hve, hvZ⟩ := hav
    rw [edgeZeroExtend_vanish Z x e ⟨v, hvZ, hve⟩, abs_zero]
  change (∑ e : Sym2 V, |edgeZeroExtend Z x e|) = ∑ e : Sym2 (Survivors Z), |x e|
  exact (hsum.trans hout).symm

/-- Bounds are unchanged by replacing the subtype with its ambient zero extension. -/
theorem physQuot_bounds_surviving_ambient (H : Host V I) (F : Set (Multiset I))
    (Z : Finset V) (d T : ℕ)
    (hr : Module.finrank ℤ (physQuot (restrictedHost H Z) F) ≤ d)
    (ht : Nat.card (Submodule.torsion ℤ (physQuot (restrictedHost H Z) F)) ≤ T) :
    Module.finrank ℤ (physQuot (vertexDeleted H Z) F) ≤ d ∧
      Nat.card (Submodule.torsion ℤ (physQuot (vertexDeleted H Z) F)) ≤ T := by
  constructor
  · rw [← finrank_survivingPhysQuot H F Z]
    exact hr
  · rw [← torsion_card_survivingPhysQuot H F Z]
    exact ht

end TypedTriangle

namespace TypedTriangle

/-- Uniform bound transport. This is a bridge, not a proof of H4 inheritance. -/
theorem physQuot_vertexDeleted_bounds_of_restricted_geometry (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ d T n₀ : ℕ, 1 ≤ T ∧
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (Z : Finset V),
        n₀ ≤ Fintype.card (Survivors Z) →
        CommonNbrCond (restrictedHost H Z) F α →
        HingeCond (restrictedHost H Z) F α h →
        Module.finrank ℤ (physQuot (vertexDeleted H Z) F) ≤ d ∧
          Nat.card (Submodule.torsion ℤ (physQuot (vertexDeleted H Z) F)) ≤ T := by
  obtain ⟨d, T, n₀, hT, hbound⟩ := physQuot_bounds_of_H3H4 α h hα
  refine ⟨d, T, n₀, hT, fun {V I} _ H F Z hn hH3 hH4 => ?_⟩
  obtain ⟨hr, ht⟩ := hbound (restrictedHost H Z) F hn hH3 hH4
  exact physQuot_bounds_surviving_ambient H F Z d T hr ht

end TypedTriangle
