/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4ReferenceH2Generic
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! The intrinsic-H2 tolerance for a paid physical mode is fixed by the
common-neighbour and hinge constants before the mode is selected. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

theorem intrinsic_H2_after_paid_mode (β : ℝ) (h : ℕ) (hβ : 0 < β) :
    ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (J : Host V I)
        (F : Set (Multiset I)),
        n₀ ≤ Fintype.card V →
        CommonNbrCond J F β → HingeCond J F β h →
        ∀ C Y : Finset (Sym2 V),
          C ⊆ edges J → Y ⊆ edges J →
          IsPhysical J F C → IsPhysical J F Y →
          Disjoint C Y →
          (∀ v, (degIn (edges J \ C) v : ℝ) ≤ η * Fintype.card V) →
          IsPhysical (subHost J (C ∪ Y)) F
            (edges (subHost J (C ∪ Y))) := by
  obtain ⟨η,hη,n₀,hDense⟩ :=
    RawReference.intrinsic_dense_child β h hβ
  refine ⟨η,hη,n₀,?_⟩
  intro V I _ J F hn h3 h4 C Y hC hY hCPhys hYPhys hDisj hHole
  exact intrinsic_H2_of_physical_reference_and_mode J F C Y η
    hC hY hCPhys hYPhys hDisj hHole
    (hDense J F hn h3 h4)

#print axioms TypedTriangle.CatalogNative.intrinsic_H2_after_paid_mode

end TypedTriangle.CatalogNative
