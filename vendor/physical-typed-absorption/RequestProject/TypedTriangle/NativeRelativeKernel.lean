/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeCompressionData
public import RequestProject.S07V37.NativeKernel
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

/-- Exact coordinates for the physical quotient, with a finite bounded set of
relations. Neither the local-profile module nor the physical lattice is saturated. -/
theorem compression_coordinate_data (H : Host V I) (F : Set (Multiset I))
    {s H₀ D₀ : ℕ} (cmp : Compression H F s H₀ D₀) :
    ∃ q : Composition.localProfile H.G H.lab F →ₗ[ℤ] (Fin ((s+1)^2) → ℤ),
      (∀ x, q x = 0 → (x : Sym2 V → ℤ) ∈ SparseEdge.lattice H.G H.lab F) ∧
      (∀ x i, |q x i| ≤ D₀ * Dispersal.l1E (x : Sym2 V → ℤ)) ∧
      ∃ S : Finset (Fin ((s+1)^2) → ℤ),
        (∀ z ∈ S, ∀ i, |z i| ≤ (3*D₀ : ℕ)) ∧
        ((SparseEdge.lattice H.G H.lab F).comap
          (Composition.localProfile H.G H.lab F).subtype).map q = span ℤ (S : Set _) := by
  have hdm := card_sym2_le cmp.W cmp.card_W
  let q := (eProj cmp.W hdm).comp (cmp.P.comp (nativeLocalProfile H F))
  have hnorm : ∀ x i, |q x i| ≤ D₀ * Dispersal.l1E (x : Sym2 V → ℤ) := by
    intro x i
    exact (abs_eProj_le cmp.W hdm _ i).trans (cmp.costP (nativeLocalProfile H F x))
  have hker : ∀ x, q x = 0 → (x : Sym2 V → ℤ) ∈ SparseEdge.lattice H.G H.lab F := by
    intro x hx
    have hp : cmp.P (nativeLocalProfile H F x) = 0 := by
      have he := eEmb_eProj cmp.W hdm (cmp.supp (nativeLocalProfile H F x))
      change eEmb cmp.W hdm (q x) = _ at he
      rw [hx, map_zero] at he
      exact he.symm
    have hd := cmp.decomp (nativeLocalProfile H F x)
    rw [hp, sub_zero] at hd
    change (x : Sym2 V → ℤ) = _ at hd
    rw [hd]
    exact triBd_mem_lattice H F _
  let R : Set (Fin ((s+1)^2) → ℤ) :=
    {z | ∃ g ∈ Composition.latGens H.G H.lab F,
      ∃ hg : g ∈ Composition.localProfile H.G H.lab F, q ⟨g,hg⟩ = z}
  have hbox : ∀ z ∈ R, z ∈ QuotientBox.box ((s+1)^2) (3*D₀) := by
    rintro z ⟨g,⟨T,hT,rfl⟩,hg,rfl⟩
    apply QuotientBox.mem_box.mpr
    intro i
    have hn := hnorm ⟨ind (triEdges T),hg⟩ i
    change |q ⟨ind (triEdges T),hg⟩ i| ≤ (D₀:ℤ)*l1E (ind (triEdges T)) at hn
    rw [l1E_ind_triEdges hT.1] at hn
    change |q ⟨ind (triEdges T),hg⟩ i| ≤ (3*D₀ : ℕ)
    push_cast
    linarith
  let S := (QuotientBox.box ((s+1)^2) (3*D₀)).filter (· ∈ R)
  have hSR : (S : Set _) = R := by
    ext z
    simp only [S, mem_coe, mem_filter]
    exact and_iff_right_of_imp (hbox z)
  refine ⟨q,hker,hnorm,S,?_,?_⟩
  · intro z hz
    exact QuotientBox.mem_box.mp (mem_filter.mp hz).1
  · rw [hSR]
    exact Grouping.map_comap_eq_span _ _ _ (Composition.latGens H.G H.lab F) rfl
      (Composition.lattice_le_localProfile H.G H.lab F) q

/-- Bounded generators of every relative physical transport kernel, obtained
from the original H3--H4 for the two actual hosts. All constants precede the hosts;
no coordinate maps, generators or saturation assumptions remain as inputs. -/
theorem relative_kernel_of_H3H4 (α : ℝ) (h : ℕ) (hα : 0 < α) :
    ∃ k K n₀ : ℕ, ∀ {V I : Type} [Fintype V]
      (G : Host V I) (F : Set (Multiset I)) (J : SimpleGraph V),
      J ≤ G.G → n₀ ≤ Fintype.card V →
      CommonNbrCond G F α → HingeCond G F α h →
      CommonNbrCond ⟨J,G.lab⟩ F α → HingeCond ⟨J,G.lab⟩ F α h →
      ∃ Y : Finset (Sym2 V → ℤ), Y.card ≤ K ∧
        (∀ y ∈ Y, y ∈ Composition.localProfile J G.lab F ∧
          y ∈ SparseEdge.lattice G.G G.lab F ∧ Dispersal.l1E y ≤ k) ∧
        ∀ x ∈ Composition.localProfile J G.lab F,
          x ∈ SparseEdge.lattice G.G G.lab F →
          ∃ f : (Sym2 V → ℤ) → ℤ,
            x - ∑ y ∈ Y, f y • y ∈ SparseEdge.lattice J G.lab F := by
  obtain ⟨s,H₀,D₀,nc,hcmp⟩ := compression_of_H3H4 α h hα
  let d := (s+1)^2
  refine ⟨S07V37.nativeK α d d D₀ D₀ (3*D₀),
    S07V37.nativeN α d d D₀ D₀ (3*D₀),
    max nc (max (RoutingConstants.routeN0 α h) (S07V25.n1Of α)),?_⟩
  intro V I _ G F J hJG hn hG3 hG4 hJ3 hJ4
  have hnc : nc ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hn₀ : RoutingConstants.routeN0 α h ≤ Fintype.card V :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₁ : S07V25.n1Of α ≤ Fintype.card V :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  obtain ⟨cmpJ⟩ := hcmp ⟨J,G.lab⟩ F hnc hJ3 hJ4
  obtain ⟨cmpG⟩ := hcmp G F hnc hG3 hG4
  obtain ⟨qJ,hkerJ,hqJ,-⟩ := compression_coordinate_data ⟨J,G.lab⟩ F cmpJ
  obtain ⟨qG,hkerG,hqG,S,hS,himg⟩ := compression_coordinate_data G F cmpG
  exact S07V37.native_relative_kernel hα d d D₀ D₀ (3*D₀) hJG hJ3 hJ4 hn₀ hn₁
    qJ qG hkerJ hkerG hqJ hqG S hS himg
end TypedTriangle
