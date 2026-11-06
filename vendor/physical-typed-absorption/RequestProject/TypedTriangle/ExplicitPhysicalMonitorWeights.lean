module
public import RequestProject.TypedTriangle.ExplicitUniformCompression
public import RequestProject.TypedTriangle.ExplicitBoundedFunctionalExtension
public import RequestProject.TypedTriangle.G4ActualBankStratumWeightsCore
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical Submodule
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.CoreMonitor.Explicit
open Incidence
def deletedExtensionCost (α β : ℝ) (h : ℕ) : ℝ :=
  let s := ExplicitSample.compressionSampleSize α h
  let D := compD0 (min α 1) s
  S07V41.Explicit.extensionCost ((s+1)^2) D (3*D) (3*RoutingConstants.routeD β)

def deletedExtensionOrder (α β : ℝ) (h : ℕ) : ℕ :=
  max (ExplicitSample.compressionOrder α h)
    (max (RoutingConstants.routeN0 β h) (S07V25.n1Of β))

theorem deletedExtensionCost_nonneg (α β : ℝ) (h : ℕ) :
    0 ≤ deletedExtensionCost α β h :=
  S07V41.Explicit.extensionCost_nonneg _ _ _ _

theorem native_deleted_bounded_extension_explicit (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (outer bad : Finset V), deletedExtensionOrder α β h ≤ Fintype.card (Survivors bad) →
        deletedExtensionOrder α β h ≤ Fintype.card (Survivors (outer∪bad)) →
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
            ∀ x : localGroup (vertexDeleted H bad) F, |f0 x| ≤ deletedExtensionCost α β h*A*Dispersal.l1E (x:Sym2 V → ℤ) := by
  let s := ExplicitSample.compressionSampleSize α h
  let D₀ := compD0 (min α 1) s
  let nC := ExplicitSample.compressionOrder α h
  let R := 3*RoutingConstants.routeD β
  intro V I _ H F outer bad hnG hnJ hG3 hG4 hJ3 hJ4 A hA f hf hfL
  change max nC (max (RoutingConstants.routeN0 β h) (S07V25.n1Of β)) ≤ Fintype.card (Survivors bad) at hnG
  change max nC (max (RoutingConstants.routeN0 β h) (S07V25.n1Of β)) ≤ Fintype.card (Survivors (outer∪bad)) at hnJ
  obtain ⟨cmp⟩ := ExplicitSample.compression_of_H3H4_explicit α h hα (restrictedHost H bad) F ((le_max_left _ _).trans hnG) hG3 hG4
  obtain ⟨q,hker,hq,S,hS,himg⟩ := surviving_compression_coordinate_data H F bad cmp
  obtain ⟨B,hB,hspan,hR⟩ := surviving_routing_atoms hβ H F (outer∪bad) hJ3 hJ4
    ((le_max_left _ _).trans ((le_max_right _ _).trans hnJ))
    ((le_max_right _ _).trans ((le_max_right _ _).trans hnJ))
  have hspanEq : span ℤ B = localGroup (vertexDeleted H (outer∪bad)) F :=
    le_antisymm (span_le.mpr hB) hspan
  exact S07V41.Explicit.uniform_bounded_extension_explicit ((s+1)^2) D₀ (3*D₀) R A hA (Sym2 V)
    (localGroup (vertexDeleted H (outer∪bad)) F) (localGroup (vertexDeleted H bad) F)
    (lattice (vertexDeleted H bad) F)
    (localGroup_mono (vertexDeleted_antitone H subset_union_right) rfl)
    q S B f hker hq hS himg hspanEq hR hf hfL

end TypedTriangle.CoreMonitor.Explicit

namespace TypedTriangle.CoreMonitor.Explicit



theorem native_core_deleted_functional_explicit (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V),
        deletedExtensionOrder α β h ≤ Fintype.card (Survivors bad) → deletedExtensionOrder α β h ≤ Fintype.card (Survivors (outer∪bad)) →
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
              |f0 x| ≤ deletedExtensionCost α β h*A*Dispersal.l1E (x:Sym2 V → ℤ)) ∧
            (∀ x, f (Submodule.inclusion (S07V39.localProfile_delG_le (restrictedHost H outer).G
              (bad.subtype (· ∉ outer))) x) = f0 (deletedCoreMap H F outer bad x)) ∧
            ∀ x (hx : x ∈ SparseEdge.lattice (S07V39.delG H.G bad) H.lab F),
              f0 ⟨x,Composition.lattice_le_localProfile _ _ _ hx⟩ = 0 := by
  intro V I _ H F outer bad hnG hnJ hG3 hG4 hJ3 hJ4 A hA f hf hkill
  let fc := f.comp (coreRestriction H F outer bad)
  have hfc : ∀ x : localGroup (vertexDeleted H (outer∪bad)) F,
      |fc x| ≤ A*Dispersal.l1E (x:Sym2 V → ℤ) := by
    intro x
    exact (hf (coreRestriction H F outer bad x)).trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast coreRestriction_l1_le H F outer bad x) hA)
  obtain ⟨f0,hagree,hann,hbound⟩ := native_deleted_bounded_extension_explicit α β h hα hβ H F outer bad hnG hnJ hG3 hG4 hJ3 hJ4 A hA fc hfc hkill
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

end TypedTriangle.CoreMonitor.Explicit

namespace TypedTriangle.CoreMonitor.Explicit

def physicalGlueCost (α β : ℝ) (h : ℕ) : ℝ := deletedExtensionCost α β h+1
def physicalGlueOrder (α β : ℝ) (h : ℕ) : ℕ :=
  max (deletedExtensionOrder α β h) (S07V25.n1Of β)

theorem native_core_physical_gluing_explicit (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V),
        physicalGlueOrder α β h ≤ Fintype.card (Survivors bad) → physicalGlueOrder α β h ≤ Fintype.card (Survivors (outer∪bad)) →
        CommonNbrCond (restrictedHost H bad) F α → HingeCond (restrictedHost H bad) F α h →
        CommonNbrCond (restrictedHost H (outer∪bad)) F β → HingeCond (restrictedHost H (outer∪bad)) F β h →
        CommonNbrCond (restrictedHost H outer) F β → HingeCond (restrictedHost H outer) F β h →
        ((bad.subtype (· ∉ outer)).card:ℝ) ≤ S07V37.delOf β h*Fintype.card (Survivors outer) →
        ∀ (A : ℝ), 0 ≤ A →
        ∀ f : localGroup (restrictedHost H outer) F →ₗ[ℤ] ℝ,
          (∀ x : localGroup (restrictedHost H outer) F,
            |f x| ≤ A*Dispersal.l1E (x:Sym2 (Survivors outer) → ℤ)) →
          (∀ x : localGroup (vertexDeleted H (outer∪bad)) F,
            (x:Sym2 V → ℤ) ∈ lattice (vertexDeleted H bad) F →
              f (coreRestriction H F outer bad x) = 0) →
          ∃ lam : Sym2 V → ℝ, (∀ e, |lam e| ≤ S07V39.glueConst β (physicalGlueCost α β h*A)) ∧
            (∀ x : localGroup (restrictedHost H outer) F,
              ∑ e, lam e*(edgeZeroExtend outer x.1 e:ℝ) = f x) ∧
            (∀ T, IsAllowed (vertexDeleted H bad) F T → ∑ e ∈ triEdges T, lam e = 0) ∧
            ∀ T, IsAllowed H F T →
              |∑ e ∈ triEdges T, lam e| ≤ 3*S07V39.glueConst β (physicalGlueCost α β h*A)*(T∩bad).card := by
  let B0 := deletedExtensionCost α β h
  have hB0 : 0 ≤ B0 := deletedExtensionCost_nonneg α β h
  let nE := deletedExtensionOrder α β h
  intro V I _ H F outer bad hnG hnJ hG3 hG4 hJ3 hJ4 hK3 hK4 hbad A hA f hf hkill
  change max nE (S07V25.n1Of β) ≤ Fintype.card (Survivors bad) at hnG
  change max nE (S07V25.n1Of β) ≤ Fintype.card (Survivors (outer∪bad)) at hnJ
  obtain ⟨f0,hf0,hagree,hann⟩ := native_core_deleted_functional_explicit α β h hα hβ H F outer bad ((le_max_left _ _).trans hnG)
    ((le_max_left _ _).trans hnJ) hG3 hG4 hJ3 hJ4 A hA f hf hkill
  have hcoreCard : Fintype.card (Survivors (outer∪bad)) ≤ Fintype.card (Survivors outer) := by
    have h₁ := card_survivors_add_card outer
    have h₂ := card_survivors_add_card (outer∪bad)
    have h₃ := card_le_card (subset_union_left : outer ⊆ outer∪bad)
    omega
  have hnK : S07V25.n1Of β ≤ Fintype.card (Survivors outer) :=
    ((le_max_right _ _).trans hnJ).trans hcoreCard
  have hA0 : A ≤ (B0+1)*A := by nlinarith
  have hB0A : B0*A ≤ (B0+1)*A := by nlinarith
  have hfR : ∀ x : localGroup (restrictedHost H outer) F,
      |f x| ≤ ((B0+1)*A)*(∑ e, |(((x:Sym2 (Survivors outer) → ℤ) e):ℝ)|) := by
    intro x
    rw [real_l1E_eq]
    exact (hf x).trans (mul_le_mul_of_nonneg_right hA0 (by rw [←real_l1E_eq]; positivity))
  have hf0R : ∀ x : Composition.localProfile (S07V39.delG H.G bad) H.lab F,
      |f0 x| ≤ ((B0+1)*A)*(∑ e, |(((x:Sym2 V → ℤ) e):ℝ)|) := by
    intro x
    rw [real_l1E_eq]
    exact (hf0 x).trans (mul_le_mul_of_nonneg_right hB0A (by rw [←real_l1E_eq]; positivity))
  have hBoundNonneg : 0 ≤ (B0+1)*A := mul_nonneg (by linarith) hA
  exact core_physical_gluing H F outer bad (A:=((B0+1)*A)) hβ hBoundNonneg
    hK3 hK4 hnK hbad f f0 hfR hf0R hagree hann

end TypedTriangle.CoreMonitor.Explicit

namespace TypedTriangle.CatalogNative.Explicit
open S07V42 S07V44 CoreMonitor


theorem physical_monitors_localize_explicit (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I)) (outer bad : Finset V),
        CoreMonitor.Explicit.physicalGlueOrder α β h ≤ Fintype.card (Survivors bad) → CoreMonitor.Explicit.physicalGlueOrder α β h ≤ Fintype.card (Survivors (outer∪bad)) →
        CommonNbrCond (restrictedHost H bad) F α → HingeCond (restrictedHost H bad) F α h →
        CommonNbrCond (restrictedHost H (outer∪bad)) F β → HingeCond (restrictedHost H (outer∪bad)) F β h →
        CommonNbrCond (restrictedHost H outer) F β → HingeCond (restrictedHost H outer) F β h →
        ((bad.subtype (· ∉ outer)).card:ℝ) ≤ S07V37.delOf β h*Fintype.card (Survivors outer) →
        ∀ {d c E R A M K : ℕ} (C0 : CoreCompression H.G H.lab F (univ\outer) d c E),
        ∀ Mon : PhysicalMonitors C0 R bad A M K,
        ∃ lam : Fin K → Sym2 V → ℝ,
          (∀ j e, |lam j e| ≤ S07V39.glueConst β (CoreMonitor.Explicit.physicalGlueCost α β h*(M*(d*c):ℕ))) ∧
          (∀ j (x : localGroup (restrictedHost H outer) F),
            ∑ e, lam j e*(edgeZeroExtend outer x.1 e:ℝ) =
              physMonReal C0 (Dset C0 R bad) Mon.psi j
                (catalogCoreMap H F outer x)) ∧
          (∀ j T, IsAllowed (vertexDeleted H bad) F T → ∑ e ∈ triEdges T, lam j e = 0) ∧
          ∀ j T, IsAllowed H F T →
            |∑ e ∈ triEdges T, lam j e| ≤
              3*S07V39.glueConst β (CoreMonitor.Explicit.physicalGlueCost α β h*(M*(d*c):ℕ))*(T∩bad).card := by

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
      (∀ e, |lam e| ≤ S07V39.glueConst β (CoreMonitor.Explicit.physicalGlueCost α β h*(M*(d*c):ℕ))) ∧
      (∀ x : localGroup (restrictedHost H outer) F,
        ∑ e, lam e*(edgeZeroExtend outer x.1 e:ℝ) = f j x) ∧
      (∀ T, IsAllowed (vertexDeleted H bad) F T → ∑ e ∈ triEdges T, lam e = 0) ∧
      ∀ T, IsAllowed H F T → |∑ e ∈ triEdges T, lam e| ≤
        3*S07V39.glueConst β (CoreMonitor.Explicit.physicalGlueCost α β h*(M*(d*c):ℕ))*(T∩bad).card := by
    intro j
    exact CoreMonitor.Explicit.native_core_physical_gluing_explicit α β h hα hβ H F outer bad hnG hnJ hG3 hG4 hJ3 hJ4 hc3 hc4 hbad
      (M*(d*c):ℕ) (by positivity) (f j) (hf j) (hkill j)
  choose lam hb hr hz ht using hEach
  exact ⟨lam,hb,hr,hz,ht⟩

end TypedTriangle.CatalogNative.Explicit

namespace TypedTriangle.CatalogNative.Explicit
open S07V42 S07V44 S07V46 LocalizedCover
def physicalWeightMagnitude (α β : ℝ) (h d c M : ℕ) : ℝ :=
  let D : ℝ := (M*(d*c):ℕ)
  max (S07V39.glueConst β (CoreMonitor.Explicit.physicalGlueCost α β h*D)) D+1

theorem physicalWeightMagnitude_pos (α β : ℝ) (h d c M : ℕ) :
    0 < physicalWeightMagnitude α β h d c M := by
  unfold physicalWeightMagnitude
  have hD : (0:ℝ) ≤ (M*(d*c):ℕ) := Nat.cast_nonneg _
  linarith [le_max_right (S07V39.glueConst β
    (CoreMonitor.Explicit.physicalGlueCost α β h*(M*(d*c):ℕ))) (M*(d*c):ℕ)]

theorem uniform_physical_monitor_weights_explicit (α β : ℝ) (h d c E R A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (outer bad : Finset V)
        (C0 : CoreCompression H.G H.lab F (univ\outer) d c E)
        (Mon : PhysicalMonitors C0 R bad A M K)
        (Fm : FullMonitor C0 R A M K),
        CoreMonitor.Explicit.physicalGlueOrder α β h ≤ Fintype.card (Survivors bad) →
        CoreMonitor.Explicit.physicalGlueOrder α β h ≤ Fintype.card (Survivors (outer∪bad)) →
        CommonNbrCond (restrictedHost H bad) F α →
        HingeCond (restrictedHost H bad) F α h →
        CommonNbrCond (restrictedHost H (outer∪bad)) F β →
        HingeCond (restrictedHost H (outer∪bad)) F β h →
        CommonNbrCond (restrictedHost H outer) F β →
        HingeCond (restrictedHost H outer) F β h →
        ((bad.subtype (· ∉ outer)).card:ℝ) ≤
          S07V37.delOf β h * Fintype.card (Survivors outer) →
        ∃ loc full : Fin K → Sym2 V → ℝ,
          (∀ j (x : MCore H.G H.lab F (univ\outer)),
            ∑ e, loc j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 (Dset C0 R bad) Mon.psi j x) ∧
          (∀ j (x : MCore H.G H.lab F (univ\outer)),
            ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 ∅ Fm.psi j x) ∧
          (∀ j T, IsAllowed H F T →
            |triSum (loc j) T| ≤ 3 * physicalWeightMagnitude α β h d c M * (T∩bad).card) ∧
          ∀ j T, IsAllowed H F T →
            |triSum (full j) T| ≤ 3 * physicalWeightMagnitude α β h d c M * T.card := by
  let B := CoreMonitor.Explicit.physicalGlueCost α β h
  let D : ℝ := (M * (d * c) : ℕ)
  let L : ℝ := max (S07V39.glueConst β (B * D)) D + 1
  have hL : 0 < L := by
    dsimp [L]
    have hD : 0 ≤ D := Nat.cast_nonneg _
    linarith [le_max_right (S07V39.glueConst β (B * D)) D]
  intro V I _ H F outer bad C0 Mon Fm hnBad hnBoth hBad3 hBad4 hJoint3 hJoint4
    hCore3 hCore4 hSmall
  obtain ⟨loc, hlocBound, hlocRep, _, hlocTri⟩ :=
    physical_monitors_localize_explicit α β h hα hβ H F outer bad hnBad hnBoth hBad3 hBad4 hJoint3 hJoint4
      hCore3 hCore4 hSmall C0 Mon
  obtain ⟨full, hfullBound, hfullRep⟩ := full_physical_monitor_weights C0 Fm
  refine ⟨loc, full,
    represent_all_core_monitors H F outer bad Mon loc hlocRep,
    hfullRep, ?_, ?_⟩
  · intro j T hT
    have hbound := hlocTri j T hT
    have hLloc : S07V39.glueConst β (B * D) ≤ L := by
      dsimp [L]
      linarith [le_max_left (S07V39.glueConst β (B * D)) D]
    have hnon : (0 : ℝ) ≤ 3 * (T∩bad).card := by positivity
    have hm := mul_le_mul_of_nonneg_right hLloc hnon
    dsimp [D] at hbound hLloc
    calc
      |triSum (loc j) T| ≤
          3 * S07V39.glueConst β (B * (M * (d * c) : ℕ)) * (T∩bad).card := hbound
      _ = S07V39.glueConst β (B * (M * (d * c) : ℕ)) *
          (3 * (T∩bad).card) := by ring
      _ ≤ L * (3 * (T∩bad).card) := hm
      _ = 3 * physicalWeightMagnitude α β h d c M * (T∩bad).card := by
        dsimp only [physicalWeightMagnitude,L,B,D]
        ring
  · intro j T hT
    have hbase := triangle_moment_bound hT D (Nat.cast_nonneg _) (full j)
      (hfullBound j)
    have hDle : D ≤ L := by
      dsimp [L]
      linarith [le_max_right (S07V39.glueConst β (B * D)) D]
    have hcard : T.card = 3 := hT.1
    have hDnon : 0 ≤ D := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hDle
      (show (0 : ℝ) ≤ 3 * (T.card : ℝ) by positivity)
    calc
      |triSum (full j) T| ≤ 3 * D := hbase
      _ ≤ D * (3 * (T.card : ℝ)) := by rw [hcard]; norm_num; nlinarith [hDnon]
      _ ≤ L * (3 * (T.card : ℝ)) := hmul
      _ = 3 * physicalWeightMagnitude α β h d c M * (T.card : ℝ) := by
        dsimp only [physicalWeightMagnitude,L,B,D]
        ring

end TypedTriangle.CatalogNative.Explicit

namespace TypedTriangle.CatalogNative.Explicit
open S07V42 S07V44 S07V46 LocalizedCover


theorem uniform_weights_on_native_stratum_explicit (α β : ℝ) (h d c E R A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hβα : β ≤ α) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (W outer bad : Finset V) (hW : W = univ \ outer)
        (C0 : CoreCompression H.G H.lab F (univ\outer) d c E)
        (Mon : PhysicalMonitors C0 R bad A M K)
        (Fm : FullMonitor C0 R A M K)
        (z : ℕ),
        CoreMonitor.Explicit.physicalGlueOrder (α/2) (β/2) h ≤ Fintype.card (Survivors bad) →
        CoreMonitor.Explicit.physicalGlueOrder (α/2) (β/2) h ≤ Fintype.card (Survivors (outer ∪ bad)) →
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        bad.card ≤ z →
        (z : ℝ) ≤ coreDelta β h * W.card →
        (z : ℝ) ≤ β / 2 * W.card →
        (z : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ β / 2 * W.card →
        ((bad.subtype (· ∉ outer)).card : ℝ) ≤
          S07V37.delOf (β/2) h * Fintype.card (Survivors outer) →
        ∃ loc full : Fin K → Sym2 V → ℝ,
          (∀ j (x : MCore H.G H.lab F (univ\outer)),
            ∑ e, loc j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 (Dset C0 R bad) Mon.psi j x) ∧
          (∀ j (x : MCore H.G H.lab F (univ\outer)),
            ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 ∅ Fm.psi j x) ∧
          (∀ j T, IsAllowed H F T →
            |triSum (loc j) T| ≤ 3 * physicalWeightMagnitude (α/2) (β/2) h d c M * (T∩bad).card) ∧
          ∀ j T, IsAllowed H F T →
            |triSum (full j) T| ≤ 3 * physicalWeightMagnitude (α/2) (β/2) h d c M * T.card := by

  intro V I _ H F W outer bad hW C0 Mon Fm z hnBad hnJoint h3 h4 hCore3
    hCore4 hbad hzCore hz3 hz4 hSmall
  obtain ⟨⟨hBad3,hBad4⟩,⟨hOuter3,hOuter4⟩,⟨hJoint3,hJoint4⟩⟩ :=
    bank_stratum_three_host_geometries H F W outer bad hW hα hβ hβα
      h3 h4 hCore3 hCore4 z hbad hzCore hz3 hz4
  exact uniform_physical_monitor_weights_explicit (α/2) (β/2) h d c E R A M K
    (by positivity) (by positivity) H F outer bad C0 Mon Fm hnBad hnJoint hBad3 hBad4
    hJoint3 hJoint4 hOuter3 hOuter4 hSmall

end TypedTriangle.CatalogNative.Explicit

namespace TypedTriangle.CatalogNative.Explicit
open S07V42 S07V44 S07V46 LocalizedCover
def nativeWeightOrder (α β q : ℝ) (h : ℕ) : ℕ :=
  ⌈4*(CoreMonitor.Explicit.physicalGlueOrder (α/2) (β/2) h:ℝ)/q⌉₊+1

theorem uniform_native_stratum_weights_explicit (α β q : ℝ) (h d c E R A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hq : 0 < q) (hβα : β ≤ α) :
    ∀ {V I : Type} [Fintype V] (H : Host V I) (F : Set (Multiset I))
        (W outer bad : Finset V) (hW : W = univ \ outer)
        (C0 : CoreCompression H.G H.lab F (univ\outer) d c E)
        (Mon : PhysicalMonitors C0 R bad A M K)
        (Fm : FullMonitor C0 R A M K)
        (z : ℕ),
        nativeWeightOrder α β q h ≤ Fintype.card V →
        q * Fintype.card V / 2 ≤ W.card →
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        bad.card ≤ z →
        (z : ℝ) ≤ coreDelta β h * W.card →
        (z : ℝ) ≤ β / 2 * W.card →
        (z : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ β / 2 * W.card →
        (z : ℝ) ≤ S07V37.delOf (β/2) h * W.card →
        ∃ loc full : Fin K → Sym2 V → ℝ,
          (∀ j (x : MCore H.G H.lab F (univ\outer)),
            ∑ e, loc j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 (Dset C0 R bad) Mon.psi j x) ∧
          (∀ j (x : MCore H.G H.lab F (univ\outer)),
            ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 ∅ Fm.psi j x) ∧
          (∀ j T, IsAllowed H F T →
            |triSum (loc j) T| ≤ 3 * physicalWeightMagnitude (α/2) (β/2) h d c M * (T∩bad).card) ∧
          ∀ j T, IsAllowed H F T →
            |triSum (full j) T| ≤ 3 * physicalWeightMagnitude (α/2) (β/2) h d c M * T.card := by
  let n₀ := CoreMonitor.Explicit.physicalGlueOrder (α/2) (β/2) h
  let n₁ := ⌈4 * (n₀ : ℝ) / q⌉₊ + 1
  intro V I _ H F W outer bad hW C0 Mon Fm z hn hWlo h3 h4 hCore3
    hCore4 hbad hzCore hz3 hz4 hzDel
  have hnReal : (n₀ : ℝ) ≤ q * Fintype.card V / 4 := by
    have hceil : 4 * (n₀ : ℝ) / q ≤ Fintype.card V :=
      (Nat.le_ceil _).trans (by exact_mod_cast
        (show ⌈4 * (n₀ : ℝ) / q⌉₊ ≤ Fintype.card V from by
          change ⌈4*(n₀:ℝ)/q⌉₊+1 ≤ Fintype.card V at hn
          omega))
    have hmul := (div_le_iff₀ hq).mp hceil
    nlinarith only [hmul]
  have hzHalf : (z : ℝ) ≤ W.card / 2 := by
    have hδ := S07V42.coreDelta_le_half β h
    have hmul := mul_le_mul_of_nonneg_right hδ
      (show (0 : ℝ) ≤ W.card by positivity)
    nlinarith only [hzCore, hmul]
  obtain ⟨hnBad,hnJoint⟩ := native_stratum_host_sizes W outer bad hW
    z n₀ q hbad hzHalf hWlo hnReal
  have hSmall := native_stratum_deletion_window W outer bad hW
    z β h hbad hzDel
  exact uniform_weights_on_native_stratum_explicit α β h d c E R A M K hα hβ hβα H F W outer bad hW C0 Mon Fm z hnBad hnJoint
    h3 h4 hCore3 hCore4 hbad hzCore hz3 hz4 hSmall

end TypedTriangle.CatalogNative.Explicit

namespace TypedTriangle.CatalogNative.Explicit
open S07V42 S07V44 S07V46 LocalizedCover


theorem choose_uniform_native_stratum_weights_explicit (α β q : ℝ)
    (h d c E R A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hq : 0 < q) (hβα : β ≤ α) :
    ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (W outer : Finset V)
        (hW : W = univ \ outer)
        (C0 : CoreCompression H.G H.lab F (univ \ outer) d c E)
        (Z : ℕ → Finset V)
        (MonS : ∀ ℓ, PhysicalMonitors C0 R (Z ℓ) A M K)
        (Fm : FullMonitor C0 R A M K)
        (z : ℕ),
        nativeWeightOrder α β q h ≤ Fintype.card V →
        q * Fintype.card V / 2 ≤ W.card →
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        (∀ ℓ, (Z ℓ).card ≤ z) →
        (z : ℝ) ≤ coreDelta β h * W.card →
        (z : ℝ) ≤ β / 2 * W.card →
        (z : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ β / 2 * W.card →
        (z : ℝ) ≤ S07V37.delOf (β/2) h * W.card →
        ∃ loc : ℕ → Fin K → Sym2 V → ℝ,
          ∃ full : Fin K → Sym2 V → ℝ,
          (∀ ℓ j (x : MCore H.G H.lab F (univ \ outer)),
            ∑ e, loc ℓ j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 (Dset C0 R (Z ℓ)) (MonS ℓ).psi j x) ∧
          (∀ j (x : MCore H.G H.lab F (univ \ outer)),
            ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 ∅ Fm.psi j x) ∧
          (∀ ℓ j T, IsAllowed H F T →
            |triSum (loc ℓ j) T| ≤ 3 * physicalWeightMagnitude (α/2) (β/2) h d c M * (T ∩ Z ℓ).card) ∧
          ∀ j T, IsAllowed H F T →
            |triSum (full j) T| ≤ 3 * physicalWeightMagnitude (α/2) (β/2) h d c M * T.card := by

  intro V I _ H F W outer hW C0 Z MonS Fm z hn hWlo h3 h4
    hCore3 hCore4 hSmall hzCore hz3 hz4 hzDel
  have hEach : ∀ ℓ, ∃ loc full : Fin K → Sym2 V → ℝ,
      (∀ j (x : MCore H.G H.lab F (univ \ outer)),
        ∑ e, loc j e * ((x.1 e : ℤ) : ℝ) =
          physMonReal C0 (Dset C0 R (Z ℓ)) (MonS ℓ).psi j x) ∧
      (∀ j (x : MCore H.G H.lab F (univ \ outer)),
        ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
          physMonReal C0 ∅ Fm.psi j x) ∧
      (∀ j T, IsAllowed H F T →
        |triSum (loc j) T| ≤ 3 * physicalWeightMagnitude (α/2) (β/2) h d c M * (T ∩ Z ℓ).card) ∧
      ∀ j T, IsAllowed H F T →
        |triSum (full j) T| ≤ 3 * physicalWeightMagnitude (α/2) (β/2) h d c M * T.card := by
    intro ℓ
    exact uniform_native_stratum_weights_explicit α β q h d c E R A M K hα hβ hq hβα H F W outer (Z ℓ) hW C0 (MonS ℓ) Fm z hn hWlo
      h3 h4 hCore3 hCore4 (hSmall ℓ) hzCore hz3 hz4 hzDel
  choose loc full hLocRep hFullRep hLocBound hFullBound using hEach
  exact ⟨loc, full 0, hLocRep, hFullRep 0, hLocBound, hFullBound 0⟩

end TypedTriangle.CatalogNative.Explicit

namespace TypedTriangle.CatalogNative.Explicit
open S07V40 S07V42 S07V44 S07V46 S07V47 LocalizedCover


theorem choose_weights_on_bank_strata_explicit (α β q : ℝ)
    (h d c E R A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hq : 0 < q) (hβα : β ≤ α) :
    ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (W outer : Finset V)
        (hW : W = univ \ outer)
        (C0 : CoreCompression H.G H.lab F (univ \ outer) d c E)
        (S : MacroSetting V (ClassQ H.G H.lab F (univ \ outer) × ℤ) (Cat d R))
        (N L z : ℕ)
        (MonS : ∀ ℓ, PhysicalMonitors C0 R (Zstrat S N (ℓ+1)) A M K)
        (Fm : FullMonitor C0 R A M K)
        (hBank : MacroBank S L N) (hz : S.zmax = z),
        nativeWeightOrder α β q h ≤ Fintype.card V →
        q * Fintype.card V / 2 ≤ W.card →
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        (z : ℝ) ≤ coreDelta β h * W.card →
        (z : ℝ) ≤ β / 2 * W.card →
        (z : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ β / 2 * W.card →
        (z : ℝ) ≤ S07V37.delOf (β/2) h * W.card →
        ∃ loc : ℕ → Fin K → Sym2 V → ℝ,
          ∃ full : Fin K → Sym2 V → ℝ,
          (∀ ℓ j (x : MCore H.G H.lab F (univ \ outer)),
            ∑ e, loc ℓ j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 (Dset C0 R (Zstrat S N (ℓ+1)))
                (MonS ℓ).psi j x) ∧
          (∀ j (x : MCore H.G H.lab F (univ \ outer)),
            ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 ∅ Fm.psi j x) ∧
          (∀ ℓ j T, IsAllowed H F T →
            |triSum (loc ℓ j) T| ≤
              3 * physicalWeightMagnitude (α/2) (β/2) h d c M * (T ∩ Zstrat S N (ℓ+1)).card) ∧
          ∀ j T, IsAllowed H F T →
            |triSum (full j) T| ≤ 3 * physicalWeightMagnitude (α/2) (β/2) h d c M * T.card := by

  intro V I _ H F W outer hW C0 S N L z MonS Fm hBank hz hn hWlo
    h3 h4 hCore3 hCore4 hzCore hz3 hz4 hzDel
  have hSmall : ∀ ℓ, (Zstrat S N (ℓ+1)).card ≤ z := by
    intro ℓ
    simpa only [Zstrat, hz] using
      (hBank.small _ ((preStrat_le (S := S) N (ℓ+1)).trans
        (numRounds_le (S := S) N)))
  exact choose_uniform_native_stratum_weights_explicit α β q h d c E R A M K hα hβ hq hβα H F W outer hW C0 (fun ℓ => Zstrat S N (ℓ+1))
    MonS Fm z hn hWlo h3 h4 hCore3 hCore4 hSmall hzCore hz3 hz4 hzDel

end TypedTriangle.CatalogNative.Explicit

namespace TypedTriangle.CatalogNative.Explicit
open S07V40 S07V42 S07V44 S07V46 S07V47 LocalizedCover


theorem choose_weights_on_actual_bank_core_explicit (α β q : ℝ)
    (h d c E R A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hq : 0 < q) (hβα : β ≤ α) :
    ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (W : Finset V)
        (C0 : CoreCompression H.G H.lab F W d c E)
        (S : MacroSetting V (ClassQ H.G H.lab F W × ℤ) (Cat d R))
        (N L z : ℕ)
        (MonS : ∀ ℓ, PhysicalMonitors C0 R (Zstrat S N (ℓ+1)) A M K)
        (Fm : FullMonitor C0 R A M K)
        (hBank : MacroBank S L N) (hz : S.zmax = z),
        nativeWeightOrder α β q h ≤ Fintype.card V →
        q * Fintype.card V / 2 ≤ W.card →
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        (z : ℝ) ≤ coreDelta β h * W.card →
        (z : ℝ) ≤ β / 2 * W.card →
        (z : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ β / 2 * W.card →
        (z : ℝ) ≤ S07V37.delOf (β/2) h * W.card →
        ∃ loc : ℕ → Fin K → Sym2 V → ℝ,
          ∃ full : Fin K → Sym2 V → ℝ,
          (∀ ℓ j (x : MCore H.G H.lab F W),
            ∑ e, loc ℓ j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 (Dset C0 R (Zstrat S N (ℓ+1)))
                (MonS ℓ).psi j x) ∧
          (∀ j (x : MCore H.G H.lab F W),
            ∑ e, full j e * ((x.1 e : ℤ) : ℝ) =
              physMonReal C0 ∅ Fm.psi j x) ∧
          (∀ ℓ j T, IsAllowed H F T →
            |triSum (loc ℓ j) T| ≤
              3 * physicalWeightMagnitude (α/2) (β/2) h d c M * (T ∩ Zstrat S N (ℓ+1)).card) ∧
          ∀ j T, IsAllowed H F T →
            |triSum (full j) T| ≤ 3 * physicalWeightMagnitude (α/2) (β/2) h d c M * T.card := by

  intro V I _ H F W C0 S N L z MonS Fm hBank hz hn hWlo h3 h4
    hCore3 hCore4 hzCore hz3 hz4 hzDel
  obtain ⟨outer,hW⟩ : ∃ outer : Finset V, W = univ \ outer :=
    ⟨univ \ W, by simp⟩
  cases hW
  exact choose_weights_on_bank_strata_explicit α β q h d c E R A M K hα hβ hq hβα H F (univ \ outer) outer rfl C0 S N L z MonS Fm
    hBank hz hn hWlo h3 h4 hCore3 hCore4 hzCore hz3 hz4 hzDel

end TypedTriangle.CatalogNative.Explicit

#print axioms TypedTriangle.CoreMonitor.Explicit.native_deleted_bounded_extension_explicit
#print axioms TypedTriangle.CoreMonitor.Explicit.native_core_physical_gluing_explicit
#print axioms TypedTriangle.CatalogNative.Explicit.physical_monitors_localize_explicit
#print axioms TypedTriangle.CatalogNative.Explicit.choose_weights_on_actual_bank_core_explicit
