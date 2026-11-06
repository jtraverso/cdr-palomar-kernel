/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.RetainedActualChild
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Joining a paid physical mode to a dense basal reference cannot increase
the degree of the complement. This is the intrinsic-H2 terminal adapter. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

theorem intrinsic_H2_of_physical_reference_and_mode
    {V I : Type} [Fintype V] (J : Host V I) (F : Set (Multiset I))
    (C Y : Finset (Sym2 V)) (δ : ℝ)
    (hC : C ⊆ edges J) (hY : Y ⊆ edges J)
    (hCPhys : IsPhysical J F C) (hYPhys : IsPhysical J F Y)
    (hDisj : Disjoint C Y)
    (hHole : ∀ v, (degIn (edges J \ C) v : ℝ) ≤ δ * Fintype.card V)
    (hDense : ∀ E : Finset (Sym2 V), E ⊆ edges J → IsPhysical J F E →
      (∀ v, (degIn (edges J \ E) v : ℝ) ≤ δ * Fintype.card V) →
      IsPhysical (subHost J E) F (edges (subHost J E))) :
    IsPhysical (subHost J (C ∪ Y)) F (edges (subHost J (C ∪ Y))) := by
  have hPhys : IsPhysical J F (C ∪ Y) :=
    isPhysical_union hCPhys hYPhys hDisj
  have hSmall : ∀ v, (degIn (edges J \ (C ∪ Y)) v : ℝ) ≤
      δ * Fintype.card V := by
    intro v
    have hIncl : edges J \ (C ∪ Y) ⊆ edges J \ C := by
      intro e he
      exact mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,
        fun hc => (mem_sdiff.mp he).2 (mem_union_left _ hc)⟩
    have hc := card_le_card
      (filter_subset_filter (p := fun e => v ∈ e) hIncl)
    exact (show (degIn (edges J \ (C ∪ Y)) v : ℝ) ≤
        degIn (edges J \ C) v by exact_mod_cast hc).trans (hHole v)
  exact hDense (C ∪ Y) (union_subset hC hY) hPhys hSmall

#print axioms TypedTriangle.CatalogNative.intrinsic_H2_of_physical_reference_and_mode

end TypedTriangle.CatalogNative
