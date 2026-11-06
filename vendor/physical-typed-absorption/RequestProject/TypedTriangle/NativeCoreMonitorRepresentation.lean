/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.LocalizedCatalogMonitors
public import RequestProject.S07V45.CoreProfile
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.CatalogNative
open S07V42 S07V44
variable {V I : Type*} [Fintype V]

/-- The true-core zero extension used by the native gluing represents EVERY
element of the ambient core profile module, not just a specified subfamily. -/
theorem catalogCoreMap_surjective (H : Host V I) (F : Set (Multiset I)) (outer : Finset V) :
    Function.Surjective (catalogCoreMap H F outer) := by
  intro y
  have hy : (y : Sym2 V → ℤ) ∈ localGroup (vertexDeleted H outer) F := by
    rw [localGroup_eq_localProfile]
    change y.1 ∈ Composition.localProfile (vertexDeleted H outer).G H.lab F
    rw [←indG_complement_eq_vertexDeleted]
    exact y.2
  let y' : localGroup (vertexDeleted H outer) F := ⟨y.1,hy⟩
  refine ⟨(survivingLocalEquiv H F outer).symm y',?_⟩
  apply Subtype.ext
  have hh := congrArg (fun z : localGroup (vertexDeleted H outer) F => (z : Sym2 V → ℤ))
    ((survivingLocalEquiv H F outer).apply_symm_apply y')
  exact hh

/-- V45 discharges intrinsic PROFILE membership for the actual physical,
core-supported leftover. It does not assume or assert intrinsic physicality. -/
theorem physical_indicator_mem_core (H : Host V I) (F : Set (Multiset I))
    {W : Finset V} {t : ℕ} (hCt : S07V45.CorePathContract H.G H.lab F W t)
    (ht : Odd t) (ht3 : 3 ≤ t) (J : Finset (Sym2 V))
    (hphys : IsPhysical H F J) (hsub : J ⊆ SparseEdge.edges (indG H.G W)) :
    ind J ∈ MCore H.G H.lab F W := by
  apply S07V45.mem_MCore_of_lattice hCt ht ht3 hphys
  intro e he
  exact if_neg (fun hJ => he (hsub hJ))

/-- Native gluing weights represent all V44 core monitors after the true-core
transport. No global coupling on arbitrary coordinate vectors is introduced. -/
theorem represent_all_core_monitors (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V)
    {d c E R A M K : ℕ} {C0 : CoreCompression H.G H.lab F (univ\outer) d c E}
    (Mon : PhysicalMonitors C0 R bad A M K) (lam : Fin K → Sym2 V → ℝ)
    (hrep : ∀ j (x : localGroup (restrictedHost H outer) F),
      ∑ e, lam j e*(edgeZeroExtend outer x.1 e:ℝ) =
        physMonReal C0 (Dset C0 R bad) Mon.psi j (catalogCoreMap H F outer x)) :
    ∀ j (x : MCore H.G H.lab F (univ\outer)),
      ∑ e, lam j e*((x.1 e:ℤ):ℝ) = physMonReal C0 (Dset C0 R bad) Mon.psi j x := by
  intro j x
  obtain ⟨y,rfl⟩ := catalogCoreMap_surjective H F outer x
  exact hrep j y

end TypedTriangle.CatalogNative
