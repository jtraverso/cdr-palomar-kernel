/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.DeletedCompressionData
public import RequestProject.TypedTriangle.NestedVertexQuotients
public import RequestProject.S07V41.Extension
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle
open Incidence

/-- A monitor on the remaining core extends to the remaining ambient physical
host with a uniform norm, while annihilating its actual lattice. Coordinates,
bounded relations and bounded atoms are all constructed from true-host geometry;
none is an additional provider hypothesis. -/
theorem native_deleted_bounded_extension (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (outer bad : Finset V), n₀ ≤ Fintype.card (Survivors bad) →
        n₀ ≤ Fintype.card (Survivors (outer∪bad)) →
        CommonNbrCond (restrictedHost H bad) F α → HingeCond (restrictedHost H bad) F α h →
        CommonNbrCond (restrictedHost H (outer∪bad)) F β → HingeCond (restrictedHost H (outer∪bad)) F β h →
        ∀ (A : ℝ), 0 ≤ A →
        ∀ f : localGroup (vertexDeleted H (outer∪bad)) F →ₗ[ℤ] ℝ,
          (∀ x : localGroup (vertexDeleted H (outer∪bad)) F, |f x| ≤ A*Dispersal.l1E (x:Sym2 V → ℤ)) →
          (∀ x : localGroup (vertexDeleted H (outer∪bad)) F, (x:Sym2 V → ℤ) ∈ lattice (vertexDeleted H bad) F → f x = 0) →
          ∃ f0 : localGroup (vertexDeleted H bad) F →ₗ[ℤ] ℝ,
            (∀ x : localGroup (vertexDeleted H (outer∪bad)) F, f0 (Submodule.inclusion
              (localGroup_mono (vertexDeleted_antitone H subset_union_right) rfl) x) = f x) ∧
            (∀ x : localGroup (vertexDeleted H bad) F, (x:Sym2 V → ℤ) ∈ lattice (vertexDeleted H bad) F → f0 x = 0) ∧
            ∀ x : localGroup (vertexDeleted H bad) F, |f0 x| ≤ B0*A*Dispersal.l1E (x:Sym2 V → ℤ) := by
  obtain ⟨s,H₀,D₀,nC,hC⟩ := compression_of_H3H4 α h hα
  let R := 3*RoutingConstants.routeD β
  obtain ⟨B0,hB0,hExt⟩ := S07V41.uniform_bounded_extension ((s+1)^2) D₀ (3*D₀) R
  refine ⟨B0,hB0,max nC (max (RoutingConstants.routeN0 β h) (S07V25.n1Of β)),?_⟩
  intro V I _ H F outer bad hnG hnJ hG3 hG4 hJ3 hJ4 A hA f hf hfL
  obtain ⟨cmp⟩ := hC (restrictedHost H bad) F ((le_max_left _ _).trans hnG) hG3 hG4
  obtain ⟨q,hker,hq,S,hS,himg⟩ := surviving_compression_coordinate_data H F bad cmp
  obtain ⟨B,hB,hspan,hR⟩ := surviving_routing_atoms hβ H F (outer∪bad) hJ3 hJ4
    ((le_max_left _ _).trans ((le_max_right _ _).trans hnJ))
    ((le_max_right _ _).trans ((le_max_right _ _).trans hnJ))
  have hspanEq : span ℤ B = localGroup (vertexDeleted H (outer∪bad)) F :=
    le_antisymm (span_le.mpr hB) hspan
  exact hExt A hA (Sym2 V)
    (localGroup (vertexDeleted H (outer∪bad)) F) (localGroup (vertexDeleted H bad) F)
    (lattice (vertexDeleted H bad) F)
    (localGroup_mono (vertexDeleted_antitone H subset_union_right) rfl)
    q S B f hker hq hS himg hspanEq hR hf hfL

end TypedTriangle
