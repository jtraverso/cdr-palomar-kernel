/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.VertexDeletionReduction
public import RequestProject.TypedTriangle.PhysicalQuotientBounds

@[expose] public section

/-!
# Physical local groups and quotient surjections after deleting vertices

Local proof candidate; not kernel-checked in this campaign.
`vertexDeleted` uses the same ambient type with deleted vertices isolated.
No claim that this host satisfies H3 is made: H3 is used only in the original host.
-/

open Finset
noncomputable section
open Classical

namespace TypedTriangle
open Incidence

variable {V I : Type*} [Fintype V]

/-- Ambient representation of deleting Z: preserve the vertex type and labels. -/
def vertexDeleted (H : Host V I) (Z : Finset V) : Host V I where
  G := {
    Adj := fun u v => H.G.Adj u v ∧ u ∉ Z ∧ v ∉ Z
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
    loopless := ⟨fun _ h => H.G.loopless.irrefl _ h.1⟩ }
  lab := H.lab

lemma vertexDeleted_le (H : Host V I) (Z : Finset V) :
    (vertexDeleted H Z).G ≤ H.G := fun _ _ h => h.1

lemma edges_vertexDeleted_iff (H : Host V I) (Z : Finset V) (e : Sym2 V) :
    e ∈ edges (vertexDeleted H Z) ↔ e ∈ edges H ∧ ∀ z ∈ Z, z ∉ e := by
  induction e using Sym2.ind with
  | _ a b =>
    constructor
    · intro he
      have hab : (vertexDeleted H Z).G.Adj a b := by simpa [edges] using he
      refine ⟨by simpa [edges] using hab.1, ?_⟩
      intro z hz hze
      rcases Sym2.mem_iff.1 hze with rfl | rfl
      · exact hab.2.1 hz
      · exact hab.2.2 hz
    · rintro ⟨he, hav⟩
      have hab : H.G.Adj a b := by simpa [edges] using he
      have ha : a ∉ Z := fun hz => hav a hz (by simp)
      have hb : b ∉ Z := fun hz => hav b hz (by simp)
      have h : (vertexDeleted H Z).G.Adj a b := ⟨hab, ha, hb⟩
      simpa [edges] using h

lemma isAllowed_vertexDeleted_iff (H : Host V I) (F : Set (Multiset I))
    (Z T : Finset V) :
    IsAllowed (vertexDeleted H Z) F T ↔ IsAllowed H F T ∧ Disjoint T Z := by
  constructor
  · intro hT
    refine ⟨isAllowed_mono (vertexDeleted_le H Z) rfl hT, ?_⟩
    rw [Finset.disjoint_left]
    intro v hv hvZ
    obtain ⟨u, w, -, hvu, -, heq⟩ := exists_eq_tri_of_mem hT.1 hv
    have hu : u ∈ T := by rw [heq]; simp
    exact (hT.2.1 v hv u hu hvu).2.1 hvZ
  · rintro ⟨hT, hd⟩
    refine ⟨hT.1, ?_, hT.2.2⟩
    intro u hu v hv huv
    exact ⟨hT.2.1 u hu v hv huv,
      fun hz => Finset.disjoint_left.1 hd hu hz,
      fun hz => Finset.disjoint_left.1 hd hv hz⟩

lemma linkGraph_vertexDeleted_of_out (H : Host V I) (F : Set (Multiset I))
    (Z : Finset V) {v : V} (hv : v ∉ Z) :
    linkGraph (vertexDeleted H Z) F v = linkOn H F v (goodEdges H Z ∅) := by
  ext u w
  change (u ≠ w ∧ IsAllowed (vertexDeleted H Z) F {v, u, w}) ↔
    ((u ≠ w ∧ IsAllowed H F {v, u, w}) ∧ s(u, w) ∈ goodEdges H Z ∅)
  constructor
  · rintro ⟨huw, hT⟩
    obtain ⟨hT, hd⟩ := (isAllowed_vertexDeleted_iff H F Z {v, u, w}).1 hT
    refine ⟨⟨huw, hT⟩, ?_⟩
    have he : s(u, w) ∈ edges H := triEdges_subset_edges hT
      (mem_triEdges.2 ⟨by simp, by simp, huw⟩)
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨he, ?_⟩, by simp⟩
    intro y hy hye
    rcases Sym2.mem_iff.1 hye with rfl | rfl
    · exact Finset.disjoint_left.1 hd (by simp) hy
    · exact Finset.disjoint_left.1 hd (by simp) hy
  · rintro ⟨⟨huw, hT⟩, he⟩
    have hav := (Finset.mem_filter.1 (Finset.mem_filter.1 he).1).2
    refine ⟨huw, (isAllowed_vertexDeleted_iff H F Z {v, u, w}).2 ⟨hT, ?_⟩⟩
    rw [Finset.disjoint_left]
    intro y hy hyZ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact hv hyZ
    · exact hav _ hyZ (by simp)
    · exact hav _ hyZ (by simp)

lemma linkGraph_vertexDeleted_of_in (H : Host V I) (F : Set (Multiset I))
    (Z : Finset V) {v : V} (hv : v ∈ Z) :
    linkGraph (vertexDeleted H Z) F v = ⊥ := by
  ext u w
  change (u ≠ w ∧ IsAllowed (vertexDeleted H Z) F {v, u, w}) ↔ False
  constructor
  · rintro ⟨-, hT⟩
    have hd := ((isAllowed_vertexDeleted_iff H F Z {v, u, w}).1 hT).2
    exact Finset.disjoint_left.1 hd (by simp) hv
  · exact False.elim

/-- Actual integer local-group restriction; no rational saturation is used. -/
theorem mem_localGroup_vertexDeleted_iff {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) (Z : Finset V)
    (hw1 : (Z.card : ℝ) + 2 < α * Fintype.card V)
    (hw2 : ((Z.card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V)
    (x : Sym2 V → ℤ) :
    x ∈ localGroup (vertexDeleted H Z) F ↔
      x ∈ localGroup H F ∧ ∀ e, TouchZ Z e → x e = 0 := by
  constructor
  · intro hx
    refine ⟨localGroup_mono (vertexDeleted_le H Z) rfl hx, ?_⟩
    intro e he
    apply hx.1 e
    intro hedge
    obtain ⟨z, hz, hze⟩ := he
    exact ((edges_vertexDeleted_iff H Z e).1 hedge).2 z hz hze
  · rintro ⟨hx, hz⟩
    apply (mem_localGroup_iff_star (vertexDeleted H Z) F x).2
    refine ⟨?_, ?_⟩
    · intro e he
      by_cases heH : e ∈ edges H
      · by_contra hne
        apply he
        exact (edges_vertexDeleted_iff H Z e).2 ⟨heH, fun z hzZ hze => hne (hz e ⟨z, hzZ, hze⟩)⟩
      · exact hx.1 e heH
    · intro v
      by_cases hv : v ∈ Z
      · have hzero : starProj v x = 0 := by
          funext w
          rw [starProj_apply]
          split_ifs
          · rfl
          · exact hz s(v, w) ⟨v, hv, by simp⟩
        rw [hzero]
        exact Submodule.zero_mem _
      · rw [linkGraph_vertexDeleted_of_out H F Z hv]
        have hdeg : ∀ w, degIn (∅ : Finset (Sym2 V)) w ≤ 0 := fun w => by simp [degIn]
        have hvan : ∀ y ∈ Z, starProj v x y = 0 := by
          intro y hy
          rw [starProj_apply]
          split_ifs
          · rfl
          · exact hz s(v, y) ⟨y, hy, by simp⟩
        exact (link_image_robust hα hH3 hH4 Z hv ∅ 0 hdeg
          (by simpa using hw1) (by simpa using hw2) hvan).1
            (starProj_mem_of_localGroup hx v)

/-- Physical quotient surjection after deleting a small vertex set.
The reduction is constructed from H3--H4, rather than received as a new premise. -/
theorem quotMap_vertexDeleted_surjective {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) (Z : Finset V)
    (hw1 : (Z.card : ℝ) + 2 < α * Fintype.card V)
    (hw2 : ((Z.card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    Function.Surjective (quotMap (F := F) (vertexDeleted_le H Z) rfl) := by
  unfold quotMap
  apply QuotientBox.mapQ_surjective_of_reduce
    (localGroup (vertexDeleted H Z) F) (localGroup H F)
    (lattice (vertexDeleted H Z) F) (lattice H F)
    (localGroup_mono (vertexDeleted_le H Z) rfl)
    (lattice_mono (vertexDeleted_le H Z) rfl)
  intro x hx
  obtain ⟨C, hC⟩ := linear_reduction_away_vertices hα hH3 hH4 Z hw1 hw2
  let x' : localGroup H F := ⟨x, hx⟩
  let y := x - triBd H F (C x')
  have hy : y ∈ localGroup (vertexDeleted H Z) F :=
    (mem_localGroup_vertexDeleted_iff hα hH3 hH4 Z hw1 hw2 y).2
      ⟨(hC x').1, (hC x').2.1⟩
  refine ⟨y, hy, ?_⟩
  have hdiff : x - y = triBd H F (C x') := by simp [y]
  rw [hdiff]
  exact triBd_mem_lattice H F _

/-- Injectivity is exactly persistence of the physical lattice on the remaining support. -/
theorem quotMap_vertexDeleted_injective_iff {H : Host V I} {F : Set (Multiset I)}
    {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond H F α)
    (hH4 : HingeCond H F α h) (Z : Finset V)
    (hw1 : (Z.card : ℝ) + 2 < α * Fintype.card V)
    (hw2 : ((Z.card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    Function.Injective (quotMap (F := F) (vertexDeleted_le H Z) rfl) ↔
      ∀ x ∈ lattice H F, (∀ e, TouchZ Z e → x e = 0) →
        x ∈ lattice (vertexDeleted H Z) F := by
  refine (quotMap_injective_iff (F := F) (vertexDeleted_le H Z) rfl).trans ?_
  constructor
  · intro hinj x hx hzero
    exact hinj x ((mem_localGroup_vertexDeleted_iff hα hH3 hH4 Z hw1 hw2 x).2
      ⟨lattice_le_localGroup H F hx, hzero⟩) hx
  · intro hpersist x hx hxphys
    exact hpersist x hxphys
      ((mem_localGroup_vertexDeleted_iff hα hH3 hH4 Z hw1 hw2 x).1 hx).2

end TypedTriangle
