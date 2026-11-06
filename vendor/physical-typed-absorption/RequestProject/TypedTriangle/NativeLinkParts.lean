/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.NativeOddRoutes
public import RequestProject.TypedTriangle.ComponentCount
public import RequestProject.TypedTriangle.LinkCover
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Native active-component partition and sizes of the bipartite sides.
Candidate pending rc3 verification. No homogeneous-class bound is used. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.ActiveCover
open ComponentRows ComponentCount Incidence
variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)}

def nativeParts (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V) :
    Finset (Finset V) := univ.filter (fun K => IsActiveRow G lab F (v, K))

lemma mem_nativeParts {v : V} {K : Finset V} :
    K ∈ nativeParts G lab F v ↔ IsActiveRow G lab F (v, K) := by simp [nativeParts]

lemma nativeParts_disjoint (v : V) :
    ∀ K ∈ nativeParts G lab F v, ∀ K' ∈ nativeParts G lab F v,
      K ≠ K' → Disjoint K K' := by
  intro K hK K' hK' hne
  exact activeRowsAt_pairwiseDisjoint G lab F v
    (show (v,K) ∈ activeRowsAt G lab F v by
      rw [ComponentCount.mem_activeRowsAt]; exact ⟨rfl,mem_nativeParts.mp hK⟩)
    (show (v,K') ∈ activeRowsAt G lab F v by
      rw [ComponentCount.mem_activeRowsAt]; exact ⟨rfl,mem_nativeParts.mp hK'⟩)
    (fun he => hne (congrArg Prod.snd he))

lemma nativeParts_cover {v u : V} (hu : LinkActive G lab F v u) :
    u ∈ (nativeParts G lab F v).biUnion id := by
  apply mem_biUnion.mpr
  exact ⟨comp G lab F v u, mem_nativeParts.mpr ⟨u, hu, rfl⟩,
    ComponentCount.mem_comp_self G lab F v u⟩

lemma active_component_active {a x : V} {K : Finset V}
    (hK : IsActiveRow G lab F (a,K)) (hx : x ∈ K) : LinkActive G lab F a x := by
  obtain ⟨u, hu, hc⟩ := hK
  change comp G lab F a u = K at hc
  have huK : u ∈ K := hc ▸ ComponentCount.mem_comp_self G lab F a u
  have hK : IsActiveRow G lab F (a,K) := ⟨u,hu,hc⟩
  obtain ⟨p⟩ := active_component_reachable hK hx huK
  cases p with
  | nil => exact hu
  | cons h _ => exact ⟨_, h⟩

/-- H3 supplies minimum degree at EVERY vertex of an active component. -/
lemma active_component_minDegree {α : ℝ}
    (hH3 : CommonNbrCond (⟨G,lab⟩ : Host V I) F α)
    {a x : V} {K : Finset V} (hK : IsActiveRow G lab F (a,K)) (hx : x ∈ K) :
    α * Fintype.card V ≤ ((univ.filter ((link G lab F a).Adj x)).card : ℝ) := by
  obtain ⟨w, hw⟩ := active_component_active hK hx
  exact link_minDeg hH3 hw

def nativeSide (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (v : V) (K : Finset V) (b : Bool) : Finset V :=
  K.filter (fun x => col G lab F (v,K) x = b)

lemma nativeSide_color {a : V} {K : Finset V} (hB : IsBip G lab F (a,K))
    {x y : V} (hx : x ∈ K) (hy : y ∈ K) (hxy : (link G lab F a).Adj x y) :
    col G lab F (a,K) x ≠ col G lab F (a,K) y := by
  simp only [col, dif_pos hB]
  exact Classical.choose_spec hB x hx y hy hxy

lemma nativeSide_card_opposite {α : ℝ}
    (hH3 : CommonNbrCond (⟨G,lab⟩ : Host V I) F α)
    {a x : V} {K : Finset V} (hK : IsActiveRow G lab F (a,K))
    (hB : IsBip G lab F (a,K)) (hx : x ∈ K) :
    α * Fintype.card V ≤
      ((nativeSide G lab F a K (!(col G lab F (a,K) x))).card : ℝ) := by
  have hsub : univ.filter ((link G lab F a).Adj x) ⊆
      nativeSide G lab F a K (!(col G lab F (a,K) x)) := by
    intro y hy
    have hxy := (mem_filter.mp hy).2
    have hyK := (active_component_closed hK x y hxy).mp hx
    refine mem_filter.mpr ⟨hyK, ?_⟩
    have hn := nativeSide_color hB hx hyK hxy
    cases hxC : col G lab F (a,K) x <;>
      cases hyC : col G lab F (a,K) y <;> simp_all
  exact (active_component_minDegree hH3 hK hx).trans (by exact_mod_cast card_le_card hsub)

/-- BOTH sides are large; the sides are chosen before demands and resource windows. -/
theorem native_bipartite_sides {α : ℝ}
    (hH3 : CommonNbrCond (⟨G,lab⟩ : Host V I) F α)
    {a : V} {K : Finset V} (hK : IsActiveRow G lab F (a,K))
    (hB : IsBip G lab F (a,K)) :
    nativeSide G lab F a K false ⊆ K ∧ nativeSide G lab F a K true ⊆ K ∧
      Disjoint (nativeSide G lab F a K false) (nativeSide G lab F a K true) ∧
      K = nativeSide G lab F a K false ∪ nativeSide G lab F a K true ∧
      (∀ x ∈ K, ∀ y ∈ K, (link G lab F a).Adj x y →
        (x ∈ nativeSide G lab F a K false ↔ y ∉ nativeSide G lab F a K false)) ∧
      α * Fintype.card V ≤ ((nativeSide G lab F a K false).card : ℝ) ∧
      α * Fintype.card V ≤ ((nativeSide G lab F a K true).card : ℝ) := by
  obtain ⟨u, hu⟩ := isActiveRow_nonempty G lab F hK
  obtain ⟨w, huw⟩ := active_component_active hK hu
  have hw : w ∈ K := (active_component_closed hK u w huw).mp hu
  have hnu := nativeSide_card_opposite hH3 hK hB hu
  have hnw := nativeSide_card_opposite hH3 hK hB hw
  have hc := nativeSide_color hB hu hw huw
  refine ⟨filter_subset _ _, filter_subset _ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hy
    have := (mem_filter.mp hx).2
    have := (mem_filter.mp hy).2
    simp_all
  · ext x
    simp only [nativeSide, mem_union, mem_filter]
    cases col G lab F (a,K) x <;> simp
  · intro x hx y hy hxy
    have hn := nativeSide_color hB hx hy hxy
    simp only [nativeSide, mem_filter, hx, hy, true_and]
    cases hxC : col G lab F (a,K) x <;> cases hyC : col G lab F (a,K) y <;> simp_all
  · cases hcu : col G lab F (a,K) u <;>
      cases hcw : col G lab F (a,K) w <;> simp_all
  · cases hcu : col G lab F (a,K) u <;>
      cases hcw : col G lab F (a,K) w <;> simp_all

/-- Every nonzero coordinate of a genuine physical circulation is an active port. -/
theorem lattice_port_active {x : Sym2 V → ℤ}
    (hx : x ∈ TypedTriangle.lattice (⟨G,lab⟩ : Host V I) F)
    {v u : V} (hvu : v ≠ u) (hxu : x s(v,u) ≠ 0) : LinkActive G lab F v u := by
  have hlocal : IsLocalProfile G lab F x :=
    lattice_le_localGroup (⟨G,lab⟩ : Host V I) F hx
  exact linkActive_of_ne_zero hlocal hvu hxu

/-- H2 ensures coverage of all ports of every subgraph of the host.
No additional port-coverage hypothesis is needed in the original theorem. -/
theorem physical_host_ports (X : SimpleGraph V) (hX : X ≤ G)
    (hphys : TypedTriangle.ind (edges (⟨G,lab⟩ : Host V I)) ∈
      TypedTriangle.lattice (⟨G,lab⟩ : Host V I) F) :
    ∀ v u, X.Adj v u → LinkActive G lab F v u := by
  intro v u hvu
  apply lattice_port_active hphys (X.ne_of_adj hvu)
  have he : s(v,u) ∈ edges (⟨G,lab⟩ : Host V I) := by
    simpa [edges] using hX hvu
  simp [TypedTriangle.ind, he]

end TypedTriangle.ActiveCover
