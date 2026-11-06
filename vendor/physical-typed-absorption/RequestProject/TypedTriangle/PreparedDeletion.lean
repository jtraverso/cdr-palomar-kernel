/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.RootErasureTransport
public import RequestProject.TypedTriangle.ActiveDeletion
public import RequestProject.TypedTriangle.ComponentRowsConverse
public import RequestProject.TypedTriangle.IncidenceColoring
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! Bridge candidate: construct all deletion fields from the original H3--H4
and their explicit numerical windows. No routing provider is a hypothesis.
This module must pass the local audit before its endpoint is called verified. -/

open Finset Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace TypedTriangle.ActiveCover

open TypedTriangle.ComponentRows

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)}

lemma componentRows_link_eq (a : V) :
    link G lab F a = linkGraph (⟨G, lab⟩ : Host V I) F a := rfl

lemma componentRows_linkA_eq (a : V) (A : Finset V) :
    linkA G lab F a A = delG (linkGraph (⟨G, lab⟩ : Host V I) F a) A ∅ := by
  ext u w
  simp [linkA, delG, componentRows_link_eq]

lemma componentRows_starIm_le_incidence (a : V) :
    starIm G lab F a ≤ Incidence.incLattice (linkGraph (⟨G, lab⟩ : Host V I) F a) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨T, hT⟩, rfl⟩
  have hT' : IsAllowed (⟨G, lab⟩ : Host V I) F T ∧ a ∈ T := by
    simpa [ComponentRows.triAt, IsAllowed, SparseEdge.IsAllowed] using hT
  have hvec : triVec a T = starProj a (ind (triEdges T)) := by
    rw [starProj_ind_tri]
    funext u
    simp [triVec, hT'.2]
  change triVec a T ∈ Incidence.incLattice (linkGraph (⟨G, lab⟩ : Host V I) F a)
  rw [hvec]
  exact starProj_tri_mem ((mem_triAt).mpr hT')

lemma active_component_reachable {a : V} {K : Finset V}
    (hK : IsActiveRow G lab F (a, K)) {u w : V} (hu : u ∈ K) (hw : w ∈ K) :
    (link G lab F a).Reachable u w := by
  obtain ⟨u₀, _, hcomp⟩ := hK
  change comp G lab F a u₀ = K at hcomp
  rw [← hcomp] at hu hw
  have hu' : (link G lab F a).Reachable u₀ u := by
    simpa only [comp, Finset.mem_filter, Finset.mem_univ, true_and] using hu
  have hw' : (link G lab F a).Reachable u₀ w := by
    simpa only [comp, Finset.mem_filter, Finset.mem_univ, true_and] using hw
  exact hu'.symm.trans hw'

lemma active_component_closed {a : V} {K : Finset V}
    (hK : IsActiveRow G lab F (a, K)) :
    ∀ u w, (link G lab F a).Adj u w → (u ∈ K ↔ w ∈ K) := by
  obtain ⟨u₀, _, hcomp⟩ := hK
  change comp G lab F a u₀ = K at hcomp
  intro u w huw
  simp only [← hcomp, comp, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.trans huw.reachable, fun h => h.trans huw.reachable.symm⟩

/-- H3 supplies a linear lower bound for every active component, not for isolates. -/
theorem active_component_card_ge {α : ℝ}
    (hH3 : CommonNbrCond (⟨G, lab⟩ : Host V I) F α) {a : V} {K : Finset V}
    (hK : IsActiveRow G lab F (a, K)) :
    α * Fintype.card V ≤ (K.card : ℝ) := by
  obtain ⟨u, ⟨w, huw⟩, hcomp⟩ := hK
  change comp G lab F a u = K at hcomp
  have hTa : IsAllowed (⟨G, lab⟩ : Host V I) F {a, u, w} := huw.2
  obtain ⟨hau, haw, huw'⟩ := distinct_of_card_three hTa.1
  have hlabels : ({lab a, lab u, lab w} : Multiset I) ∈ F := by
    have h := hTa.2.2
    rwa [Finset.insert_val_of_notMem (by simp [hau, haw]),
      Finset.insert_val_of_notMem (by simp [huw'])] at h
  have hc := hH3 a u hau (lab w) hlabels
  have hsub : commonNbrs (⟨G, lab⟩ : Host V I) (lab w) a u ⊆ K := by
    intro t ht
    have hTt := allowed_of_commonNbr hTa ht
    have hut : u ≠ t := (distinct_of_card_three hTt.1).2.2
    have hadj : (link G lab F a).Adj u t := ⟨hut, hTt⟩
    rw [← hcomp]
    exact mem_comp_of_adj hadj
  exact hc.trans (by exact_mod_cast Finset.card_le_card hsub)

/-- The geometric deletion contract follows from H3--H4, including deleted roots.
The numerical windows are the original robust-hinge windows with no forbidden edges. -/
theorem deletionHyp_of_H3H4 {α : ℝ} {h : ℕ} (hα : 0 < α)
    (hH3 : CommonNbrCond (⟨G, lab⟩ : Host V I) F α)
    (hH4 : HingeCond (⟨G, lab⟩ : Host V I) F α h) (A : Finset V)
    (hwin1 : (A.card : ℝ) + 2 < α * Fintype.card V)
    (hwin2 : ((A.card : ℝ) + h) * 2 ^ Nat.choose h 2 ≤ α / 2 * Fintype.card V) :
    DeletionHyp G lab F A := by
  have hnonempty : ∀ a ∈ A, ∀ K, IsActiveRow G lab F (a, K) → ∃ u ∈ K, u ∉ A := by
    intro a _ K hK
    have hcard := active_component_card_ge hH3 hK
    have hlt : A.card < K.card := by exact_mod_cast (show (A.card : ℝ) < K.card by linarith)
    exact Finset.exists_mem_notMem_of_card_lt_card hlt
  have hdeg0 : ∀ v : V, degIn (∅ : Finset (Sym2 V)) v ≤ 0 := by
    intro v
    simp [degIn]
  refine ⟨?_, ?_, ?_, hnonempty⟩
  · intro a _ K hK u hu w hw huA hwA
    rw [componentRows_linkA_eq]
    apply link_reach_robust_any_root hα hH3 hH4 a A ∅ 0 hdeg0
      (by simpa using hwin1) (by simpa using hwin2) huA hwA
    rw [← componentRows_link_eq]
    exact active_component_reachable hK hu hw
  · intro a haA K hK hB
    obtain ⟨u, hu, huA⟩ := hnonempty a haA K hK
    have hcomp : comp G lab F a u = K := by
      obtain ⟨u₀, _, hK0⟩ := hK
      exact (ActiveCover.comp_eq_of_mem (hK0 ▸ hu)).trans hK0
    have hB' : ¬ IsBip G lab F (a, comp G lab F a u) := by simpa [hcomp] using hB
    have hm := componentRows_starIm_le_incidence (G := G) (lab := lab) (F := F) a
      (two_dl_of_not_bip G lab F hB')
    have hz : ∀ y ∈ A, ((2 : ℤ) • Incidence.dlt u) y = 0 := by
      intro y hy
      have hyu : y ≠ u := fun he => huA (he ▸ hy)
      simp [Incidence.dlt, hyu]
    have hm' := (link_image_robust_any_root hα hH3 hH4 a A ∅ 0 hdeg0
      (by simpa using hwin1) (by simpa using hwin2) hz).mp hm
    have hmA : (2 : ℤ) • Incidence.dlt u ∈ Incidence.incLattice (linkA G lab F a A) := by
      rwa [componentRows_linkA_eq]
    apply Incidence.double_delta_forbids_coloring (linkA G lab F a A) K u hu ?_ hmA
    intro x y hxy
    exact active_component_closed hK x y hxy.1
  · intro a _ b _ hab
    obtain ⟨w, _, hT⟩ := hab
    obtain ⟨t, hTt, htA⟩ := exists_fresh_apex hH3 hT A (by linarith)
    refine ⟨t, htA, ?_⟩
    exact ⟨(distinct_of_card_three hTt.1).2.2, hTt⟩

end TypedTriangle.ActiveCover
