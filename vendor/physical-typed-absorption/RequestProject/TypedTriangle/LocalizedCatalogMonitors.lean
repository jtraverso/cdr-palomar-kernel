/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativePhysicalMonitor
public import RequestProject.TypedTriangle.NativeCatalogCompression
public import RequestProject.S07V44.Uniform
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
open S07V42 S07V44 CoreMonitor
variable {V I : Type*} [Fintype V]

/-- Zero extension from the true core to V44's fixed ambient core module. -/
def catalogCoreMap (H : Host V I) (F : Set (Multiset I)) (outer : Finset V) :
    localGroup (restrictedHost H outer) F →ₗ[ℤ] MCore H.G H.lab F (univ\outer) where
  toFun x := ⟨edgeZeroExtend outer x.1,by
    rw [MCore,indG_complement_eq_vertexDeleted]
    exact edgeZeroExtend_mem_localGroup H F outer x.2⟩
  map_add' _ _ := Subtype.ext ((edgeZeroExtend outer).map_add _ _)
  map_smul' _ _ := Subtype.ext ((edgeZeroExtend outer).map_smul _ _)

lemma catalogCoreMap_l1 (H : Host V I) (F : Set (Multiset I)) (outer : Finset V)
    (x : localGroup (restrictedHost H outer) F) :
    Dispersal.l1E (catalogCoreMap H F outer x:Sym2 V → ℤ) =
      Dispersal.l1E (x:Sym2 (Survivors outer) → ℤ) := l1E_edgeZeroExtend outer x.1

lemma catalogCoreMap_restriction (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V)
    (x : localGroup (vertexDeleted H (outer∪bad)) F) :
    (catalogCoreMap H F outer (coreRestriction H F outer bad x):Sym2 V → ℤ) = x :=
  congrArg Subtype.val ((survivingLocalEquiv H F outer).apply_symm_apply
    (Submodule.inclusion (localGroup_mono (vertexDeleted_antitone H subset_union_left) rfl) x))

lemma indG_core_deleted (H : Host V I) (outer bad : Finset V) :
    indG H.G ((univ\outer)\bad) = (vertexDeleted H (outer∪bad)).G := by
  ext u v
  simp [indG,vertexDeleted]

/-- V44's actual finite family of physical monitors supplies the functionals
for native gluing. No arbitrary real functional or ambient extension is a
premise. All resulting edge weights are uniformly bounded, represent the
physical monitors and vanish on triangles outside the deleted set. -/
theorem physical_monitors_localize (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ n₀ : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V),
        n₀ ≤ Fintype.card (Survivors bad) → n₀ ≤ Fintype.card (Survivors (outer∪bad)) →
        CommonNbrCond (restrictedHost H bad) F α → HingeCond (restrictedHost H bad) F α h →
        CommonNbrCond (restrictedHost H (outer∪bad)) F β → HingeCond (restrictedHost H (outer∪bad)) F β h →
        CommonNbrCond (restrictedHost H outer) F β → HingeCond (restrictedHost H outer) F β h →
        ((bad.subtype (· ∉ outer)).card:ℝ) ≤ S07V37.delOf β h*Fintype.card (Survivors outer) →
        ∀ {d c E R A M K : ℕ} (C0 : CoreCompression H.G H.lab F (univ\outer) d c E),
        ∀ Mon : PhysicalMonitors C0 R bad A M K,
        ∃ lam : Fin K → Sym2 V → ℝ,
          (∀ j e, |lam j e| ≤ S07V39.glueConst β (B*(M*(d*c):ℕ))) ∧
          (∀ j (x : localGroup (restrictedHost H outer) F),
            ∑ e, lam j e*(edgeZeroExtend outer x.1 e:ℝ) =
              physMonReal C0 (Dset C0 R bad) Mon.psi j
                (catalogCoreMap H F outer x)) ∧
          (∀ j T, IsAllowed (vertexDeleted H bad) F T → ∑ e ∈ triEdges T, lam j e = 0) ∧
          ∀ j T, IsAllowed H F T →
            |∑ e ∈ triEdges T, lam j e| ≤
              3*S07V39.glueConst β (B*(M*(d*c):ℕ))*(T∩bad).card := by
  obtain ⟨B,hB,n₀,hGlue⟩ := native_core_physical_gluing α β h hα hβ
  refine ⟨B,hB,n₀,?_⟩
  intro V I _ H F outer bad hnG hnJ hG3 hG4 hJ3 hJ4 hc3 hc4 hbad d c E R A M K C0 Mon
  let f : Fin K → localGroup (restrictedHost H outer) F →ₗ[ℤ] ℝ :=
    fun j => (physMonReal C0 (Dset C0 R bad) Mon.psi j).comp (catalogCoreMap H F outer)
  have hf : ∀ j (x : localGroup (restrictedHost H outer) F),
      |f j x| ≤ (M*(d*c):ℕ)*Dispersal.l1E (x:Sym2 (Survivors outer) → ℤ) := by
    intro j x
    have hh := Mon.real_le j (catalogCoreMap H F outer x)
    rw [catalogCoreMap_l1] at hh
    exact hh
  have hkill : ∀ j (x : localGroup (vertexDeleted H (outer∪bad)) F),
      (x:Sym2 V → ℤ) ∈ lattice (vertexDeleted H bad) F → f j (coreRestriction H F outer bad x) = 0 := by
    intro j x hx
    let y := catalogCoreMap H F outer (coreRestriction H F outer bad x)
    have hy : (y:Sym2 V → ℤ) = x := catalogCoreMap_restriction H F outer bad x
    have hyM : (y:Sym2 V → ℤ) ∈ MZ H.G H.lab F (univ\outer) bad := by
      rw [hy,MZ,indG_core_deleted]
      exact x.2
    have hyL : (y:Sym2 V → ℤ) ∈ LamDel H.G H.lab F bad := by rw [hy]; exact hx
    exact Mon.real_annihilates j y hyM hyL
  have hEach : ∀ j : Fin K, ∃ lam : Sym2 V → ℝ,
      (∀ e, |lam e| ≤ S07V39.glueConst β (B*(M*(d*c):ℕ))) ∧
      (∀ x : localGroup (restrictedHost H outer) F,
        ∑ e, lam e*(edgeZeroExtend outer x.1 e:ℝ) = f j x) ∧
      (∀ T, IsAllowed (vertexDeleted H bad) F T → ∑ e ∈ triEdges T, lam e = 0) ∧
      ∀ T, IsAllowed H F T → |∑ e ∈ triEdges T, lam e| ≤
        3*S07V39.glueConst β (B*(M*(d*c):ℕ))*(T∩bad).card := by
    intro j
    exact hGlue H F outer bad hnG hnJ hG3 hG4 hJ3 hJ4 hc3 hc4 hbad
      (M*(d*c):ℕ) (by positivity) (f j) (hf j) (hkill j)
  choose lam hb hr hz ht using hEach
  exact ⟨lam,hb,hr,hz,ht⟩
end TypedTriangle.CatalogNative
