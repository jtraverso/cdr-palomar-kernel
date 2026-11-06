/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeDeletedExtension
public import RequestProject.TypedTriangle.CorePhysicalGluing
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CoreMonitor
variable {V I : Type*} [Fintype V]

/-- Restrict a surviving core vector to the original true core vertex type. -/
def coreRestriction (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V) :
    localGroup (vertexDeleted H (outer∪bad)) F →ₗ[ℤ] localGroup (restrictedHost H outer) F :=
  (survivingLocalEquiv H F outer).symm.toLinearMap.comp
    (Submodule.inclusion (localGroup_mono (vertexDeleted_antitone H subset_union_left) rfl))

lemma coreRestriction_l1_le (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V)
    (x : localGroup (vertexDeleted H (outer∪bad)) F) :
    Dispersal.l1E (coreRestriction H F outer bad x:Sym2 (Survivors outer) → ℤ) ≤
      Dispersal.l1E (x:Sym2 V → ℤ) :=
  Dispersal.l1E_restr_le (Z:=outer) (x:Sym2 V → ℤ)

lemma deleted_core_lift_mem_nested (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V)
    {x : Sym2 (Survivors outer) → ℤ}
    (hx : x ∈ Composition.localProfile
      (S07V39.delG (restrictedHost H outer).G (bad.subtype (· ∉ outer)))
      (restrictedHost H outer).lab F) :
    edgeZeroExtend outer x ∈ localGroup (vertexDeleted H (outer∪bad)) F := by
  have heq : restrictedHost (vertexDeleted H bad) outer =
      (⟨S07V39.delG (restrictedHost H outer).G (bad.subtype (· ∉ outer)),
        (restrictedHost H outer).lab⟩ : Host (Survivors outer) I) := by
    rw [restrictedHost_vertexDeleted]
    rfl
  have hc : x ∈ localGroup (restrictedHost (vertexDeleted H bad) outer) F := by
    rw [heq,localGroup_eq_localProfile]
    exact hx
  have hh := edgeZeroExtend_mem_localGroup (vertexDeleted H bad) F outer hc
  rwa [vertexDeleted_vertexDeleted] at hh

/-- Construct the ambient deleted functional used by physical gluing. Its
existence, compatibility and uniform norm follow from native geometry and V41;
there is no ambient functional provider among the premises. -/
theorem native_core_deleted_functional (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V),
        n₀ ≤ Fintype.card (Survivors bad) → n₀ ≤ Fintype.card (Survivors (outer∪bad)) →
        CommonNbrCond (restrictedHost H bad) F α → HingeCond (restrictedHost H bad) F α h →
        CommonNbrCond (restrictedHost H (outer∪bad)) F β → HingeCond (restrictedHost H (outer∪bad)) F β h →
        ∀ (A : ℝ), 0 ≤ A →
        ∀ f : localGroup (restrictedHost H outer) F →ₗ[ℤ] ℝ,
          (∀ x : localGroup (restrictedHost H outer) F,
            |f x| ≤ A*Dispersal.l1E (x:Sym2 (Survivors outer) → ℤ)) →
          (∀ x : localGroup (vertexDeleted H (outer∪bad)) F,
            (x:Sym2 V → ℤ) ∈ lattice (vertexDeleted H bad) F →
              f (coreRestriction H F outer bad x) = 0) →
          ∃ f0 : Composition.localProfile (S07V39.delG H.G bad) H.lab F →ₗ[ℤ] ℝ,
            (∀ x : Composition.localProfile (S07V39.delG H.G bad) H.lab F,
              |f0 x| ≤ B0*A*Dispersal.l1E (x:Sym2 V → ℤ)) ∧
            (∀ x, f (Submodule.inclusion (S07V39.localProfile_delG_le (restrictedHost H outer).G
              (bad.subtype (· ∉ outer))) x) = f0 (deletedCoreMap H F outer bad x)) ∧
            ∀ x (hx : x ∈ SparseEdge.lattice (S07V39.delG H.G bad) H.lab F),
              f0 ⟨x,Composition.lattice_le_localProfile _ _ _ hx⟩ = 0 := by
  obtain ⟨B0,hB0,n₀,hExt⟩ := native_deleted_bounded_extension α β h hα hβ
  refine ⟨B0,hB0,n₀,?_⟩
  intro V I _ H F outer bad hnG hnJ hG3 hG4 hJ3 hJ4 A hA f hf hkill
  let fc := f.comp (coreRestriction H F outer bad)
  have hfc : ∀ x : localGroup (vertexDeleted H (outer∪bad)) F,
      |fc x| ≤ A*Dispersal.l1E (x:Sym2 V → ℤ) := by
    intro x
    exact (hf (coreRestriction H F outer bad x)).trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast coreRestriction_l1_le H F outer bad x) hA)
  obtain ⟨f0,hagree,hann,hbound⟩ := hExt H F outer bad hnG hnJ hG3 hG4 hJ3 hJ4 A hA fc hfc hkill
  refine ⟨f0,hbound,?_,?_⟩
  · intro x
    let y : localGroup (vertexDeleted H (outer∪bad)) F :=
      ⟨edgeZeroExtend outer x.1,deleted_core_lift_mem_nested H F outer bad x.2⟩
    have hy : coreRestriction H F outer bad y =
        Submodule.inclusion (S07V39.localProfile_delG_le (restrictedHost H outer).G
          (bad.subtype (· ∉ outer))) x :=
      Subtype.ext (edgeRestrict_zeroExtend outer x.1)
    rw [←hy]
    exact (hagree y).symm
  · intro x hx
    exact hann ⟨x,Composition.lattice_le_localProfile _ _ _ hx⟩ hx

end TypedTriangle.CoreMonitor
