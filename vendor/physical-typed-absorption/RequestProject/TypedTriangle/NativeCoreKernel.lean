/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeRelativeKernel
public import RequestProject.TypedTriangle.RestrictedQuotientTransport
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle
open Incidence
variable {V I : Type*} [Fintype V]

lemma localGroup_eq_localProfile (H : Host V I) (F : Set (Multiset I)) :
    localGroup H F = Composition.localProfile H.G H.lab F := by
  ext x
  rfl

lemma compression_local_coordinate_data (H : Host V I) (F : Set (Multiset I))
    {s H₀ D₀ : ℕ} (cmp : Compression H F s H₀ D₀) :
    ∃ q : localGroup H F →ₗ[ℤ] (Fin ((s+1)^2) → ℤ),
      (∀ x, q x = 0 → (x : Sym2 V → ℤ) ∈ lattice H F) ∧
      (∀ x i, |q x i| ≤ D₀ * Dispersal.l1E (x : Sym2 V → ℤ)) ∧
      ∃ S : Finset (Fin ((s+1)^2) → ℤ),
        (∀ z ∈ S, ∀ i, |z i| ≤ (3*D₀ : ℕ)) ∧
        ((lattice H F).comap (localGroup H F).subtype).map q = span ℤ (S : Set _) := by
  rw [localGroup_eq_localProfile]
  exact compression_coordinate_data H F cmp

/-- Transfer compression coordinates through the actual surviving subtype.
No common-neighbour assumption is made on the host with isolated deleted vertices. -/
theorem surviving_compression_coordinates (H : Host V I) (F : Set (Multiset I)) (Z : Finset V)
    {s H₀ D₀ : ℕ} (cmp : Compression (restrictedHost H Z) F s H₀ D₀) :
    ∃ q : localGroup (vertexDeleted H Z) F →ₗ[ℤ] (Fin ((s+1)^2) → ℤ),
      (∀ x, q x = 0 → (x : Sym2 V → ℤ) ∈ lattice (vertexDeleted H Z) F) ∧
      (∀ x i, |q x i| ≤ D₀ * Dispersal.l1E (x : Sym2 V → ℤ)) := by
  obtain ⟨qc,hker,hq,-⟩ := compression_local_coordinate_data (restrictedHost H Z) F cmp
  let e := survivingLocalEquiv H F Z
  refine ⟨qc.comp e.symm.toLinearMap,?_,?_⟩
  · intro x hx
    have hc := hker (e.symm x) hx
    have he := edgeZeroExtend_mem_lattice H F Z hc
    have hback : edgeZeroExtend Z (e.symm x : Sym2 (Survivors Z) → ℤ) = x :=
      congrArg Subtype.val (e.apply_symm_apply x)
    rwa [hback] at he
  · intro x i
    refine (hq (e.symm x) i).trans ?_
    have hr := Dispersal.l1E_restr_le (Z:=Z) (x : Sym2 V → ℤ)
    exact mul_le_mul_of_nonneg_left hr (by positivity)

/-- Uniform bounded atoms of the actual core, lifted to ambient edge coordinates. -/
theorem surviving_routing_atoms {β : ℝ} {h : ℕ} (hβ : 0 < β)
    (H : Host V I) (F : Set (Multiset I)) (Z : Finset V)
    (h3 : CommonNbrCond (restrictedHost H Z) F β)
    (h4 : HingeCond (restrictedHost H Z) F β h)
    (hn₀ : RoutingConstants.routeN0 β h ≤ Fintype.card (Survivors Z))
    (hn₁ : S07V25.n1Of β ≤ Fintype.card (Survivors Z)) :
    ∃ A : Set (Sym2 V → ℤ), A ⊆ localGroup (vertexDeleted H Z) F ∧
      localGroup (vertexDeleted H Z) F ≤ span ℤ A ∧
      ∀ a ∈ A, Dispersal.l1E a ≤ 3*RoutingConstants.routeD β := by
  obtain ⟨hat,hspan⟩ := S07V37.routing_atoms_H3H4 hβ h3 h4 hn₀ hn₁
  let Ac := S07V37.atoms (restrictedHost H Z).G (restrictedHost H Z).lab F β
  let A := (edgeZeroExtend Z) '' Ac
  refine ⟨A,?_,?_,?_⟩
  · rintro a ⟨x,hx,rfl⟩
    apply edgeZeroExtend_mem_localGroup H F Z
    rw [localGroup_eq_localProfile]
    exact hat hx
  · intro x hx
    have hc := edgeRestrict_mem_localGroup H F Z hx
    rw [localGroup_eq_localProfile] at hc
    have hm : edgeZeroExtend Z (edgeRestrict Z x) ∈ (span ℤ Ac).map (edgeZeroExtend Z) :=
      Submodule.mem_map_of_mem (hspan hc)
    rw [Submodule.map_span] at hm
    have hback := edgeZeroExtend_restrict Z x (localGroup_vertexDeleted_vanish H F Z hx)
    rwa [hback] at hm
  · rintro a ⟨x,hx,rfl⟩
    change l1E (edgeZeroExtend Z x) ≤ _
    rw [l1E_edgeZeroExtend]
    exact hx.2

/-- Bounded physical relative-kernel generators for a genuine induced core,
with its own vertex type. All constants precede both the host and the core. -/
theorem core_relative_kernel_of_H3H4 (α β : ℝ) (h : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ∃ k K n₀ : ℕ, ∀ {V I : Type} [Fintype V] (H : Host V I)
      (F : Set (Multiset I)) (Z : Finset V),
      n₀ ≤ Fintype.card V → n₀ ≤ Fintype.card (Survivors Z) →
      CommonNbrCond H F α → HingeCond H F α h →
      CommonNbrCond (restrictedHost H Z) F β → HingeCond (restrictedHost H Z) F β h →
      ∃ Y : Finset (Sym2 V → ℤ), Y.card ≤ K ∧
        (∀ y ∈ Y, y ∈ localGroup (vertexDeleted H Z) F ∧
          y ∈ lattice H F ∧ Dispersal.l1E y ≤ k) ∧
        ∀ x ∈ localGroup (vertexDeleted H Z) F, x ∈ lattice H F →
          ∃ f : (Sym2 V → ℤ) → ℤ,
            x - ∑ y ∈ Y, f y • y ∈ lattice (vertexDeleted H Z) F := by
  obtain ⟨sg,Hg,Dg,ng,hcg⟩ := compression_of_H3H4 α h hα
  obtain ⟨sj,Hj,Dj,nj,hcj⟩ := compression_of_H3H4 β h hβ
  let dg := (sg+1)^2
  let dj := (sj+1)^2
  let R := 3*RoutingConstants.routeD β
  refine ⟨S07V37.relK dj dg Dj Dg R (3*Dg),S07V37.relN dj dg Dj Dg R (3*Dg),
    max ng (max nj (max (RoutingConstants.routeN0 β h) (S07V25.n1Of β))),?_⟩
  intro V I _ H F Z hn hncore hG3 hG4 hJ3 hJ4
  obtain ⟨cg⟩ := hcg H F ((le_max_left _ _).trans hn) hG3 hG4
  obtain ⟨cj⟩ := hcj (restrictedHost H Z) F
    ((le_max_left _ _).trans ((le_max_right _ _).trans hncore)) hJ3 hJ4
  obtain ⟨qg,hkg,hqg,S,hS,himg⟩ := compression_local_coordinate_data H F cg
  obtain ⟨qj,hkj,hqj⟩ := surviving_compression_coordinates H F Z cj
  obtain ⟨A,hA,hspan,hR⟩ := surviving_routing_atoms hβ H F Z hJ3 hJ4
    ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hncore)))
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hncore)))
  exact S07V37.relative_kernel_generators dj dg Dj Dg R (3*Dg)
    Dispersal.l1E S07V37.l1E_L1Like
    (localGroup (vertexDeleted H Z) F) (localGroup H F)
    (lattice (vertexDeleted H Z) F) (lattice H F)
    (localGroup_mono (vertexDeleted_le H Z) rfl) (lattice_mono (vertexDeleted_le H Z) rfl)
    qj qg hkj hkg hqj hqg S hS himg A hA hspan hR
end TypedTriangle
