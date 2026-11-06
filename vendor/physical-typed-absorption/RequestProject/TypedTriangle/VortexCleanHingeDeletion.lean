/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V49.HingeLoss
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace S07V49
open TypedTriangle.SparseEdge S07V24
variable {V I : Type*} [Fintype V] {G : SimpleGraph V}
  {lab : V → I} {F : Set (Multiset I)}

private theorem decomposition_on_edge_subset {G' : SimpleGraph V}
    {E : Finset (Sym2 V)} {D : Finset (Finset V)}
    (hD : IsDecomposition G lab F E D) (hE : E ⊆ edges G') :
    IsDecomposition G' lab F E D := by
  refine ⟨fun T hT => isAllowed_of_triEdges_subset (hD.1 T hT) ?_, hD.2⟩
  exact (hD.2.2 ▸ subset_biUnion_of_mem triEdges hT).trans hE

private theorem hinge_on_edge_deleted_host {B : SimpleGraph V}
    {u v a b : V} {J : Finset (Sym2 V)}
    (hT : HingeTest (G \ B) lab F u v a b)
    (hJ : IsHinge G lab F u v a b J)
    (hAvoid : ∀ e ∈ J, e ∉ B.edgeSet) :
    IsHinge (G \ B) lab F u v a b J := by
  have hJE : J ⊆ edges (G \ B) := by
    intro e he
    rw [mem_edges, SimpleGraph.edgeSet_sdiff]
    exact ⟨mem_edges.mp (hJ.1 he), hAvoid e he⟩
  obtain ⟨huv, hua, hva, hub, hvb, _⟩ := roots_distinct hT
  have hWa : wedge u v a ⊆ edges (G \ B) :=
    (wedge_subset_triEdges huv hua hva).trans (triEdges_subset_edges hT.2.1)
  have hWb : wedge u v b ⊆ edges (G \ B) :=
    (wedge_subset_triEdges huv hub hvb).trans (triEdges_subset_edges hT.2.2)
  obtain ⟨Da, hDa⟩ := hJ.2.2.1
  obtain ⟨Db, hDb⟩ := hJ.2.2.2
  exact ⟨hJE, hJ.2.1,
    ⟨Da, decomposition_on_edge_subset hDa (union_subset hJE hWa)⟩,
    ⟨Db, decomposition_on_edge_subset hDb (union_subset hJE hWb)⟩⟩

/-- Clean hinges lose only the sparse-degree error, even when the deleted
graph contains the apex--apex edge. Their order does not increase. -/
theorem clean_hinges_after_edge_deletion {u v a b : V}
    (B : SimpleGraph V) [DecidableRel B.Adj] (d i : ℕ)
    (hT : HingeTest (G \ B) lab F u v a b) (hi : 6 ≤ i)
    (hB : ∀ x, B.degree x ≤ d) :
    (((hinges G lab F u v a b i).filter (fun J => s(a,b) ∉ J)).card : ℝ) -
      (5 * (d : ℝ)) * (2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i - 5)) ≤
    ((hinges (G \ B) lab F u v a b i).filter (fun J => s(a,b) ∉ J)).card := by
  let B₀ := B \ SimpleGraph.edge a b
  letI : DecidableRel B₀.Adj := Classical.decRel _
  have hB₀ : ∀ x, B₀.degree x ≤ d := by
    intro x
    exact (B₀.degree_le_of_le sdiff_le).trans (hB x)
  obtain ⟨huv, hua, hva, hub, hvb, hab⟩ := roots_distinct hT
  have hRoot : ¬ B₀.Adj a b := by
    intro he
    exact he.2 ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩, hab⟩)
  let A := hinges G lab F u v a b i
  let Good := A.filter (fun J => freeV u v a b J ⊆ univ ∧
    (∀ e ∈ J, e ∉ B₀.edgeSet) ∧ Disjoint (support J) ∅)
  let Clean := A.filter (fun J => s(a,b) ∉ J)
  let Survive := Clean.filter (fun J => ∀ e ∈ J, e ∉ B₀.edgeSet)
  let loss : ℝ := 5 * d * (2 ^ (i.choose 2) * (Fintype.card V : ℝ) ^ (i-5))
  have hLoss : (A.card : ℝ) - loss ≤ Good.card := by
    have h := good_hinges_ge (G := G) (lab := lab) (F := F)
      ⟨huv,hua,hva,hub,hvb,hab⟩ i hi univ ∅ (by simp) B₀ d hB₀ hRoot
    simpa [A, Good, loss] using h
  have hGood : Good ⊆ A := filter_subset _ _
  have hCover : Clean ⊆ Survive ∪ (A \ Good) := by
    intro J hJ
    by_cases hAvoid : ∀ e ∈ J, e ∉ B₀.edgeSet
    · exact mem_union_left _ (mem_filter.mpr ⟨hJ,hAvoid⟩)
    · refine mem_union_right _ (mem_sdiff.mpr ⟨(mem_filter.mp hJ).1, ?_⟩)
      intro hG
      exact hAvoid (mem_filter.mp hG).2.2.1
  have hCards : Clean.card ≤ Survive.card + (A \ Good).card :=
    (card_le_card hCover).trans (card_union_le _ _)
  have hDiff := card_sdiff_add_card_eq_card hGood
  have hCardsR : (Clean.card : ℝ) ≤ Survive.card + (A \ Good).card := by
    exact_mod_cast hCards
  have hDiffR : ((A \ Good).card : ℝ) + Good.card = A.card := by
    exact_mod_cast hDiff
  have hSurvive : Survive ⊆
      (hinges (G \ B) lab F u v a b i).filter (fun J => s(a,b) ∉ J) := by
    intro J hJ
    obtain ⟨hClean,hAvoid₀⟩ := mem_filter.mp hJ
    obtain ⟨hA,hNot⟩ := mem_filter.mp hClean
    obtain ⟨hHinge,hOrder⟩ := (mem_filter.mp hA).2
    have hAvoid : ∀ e ∈ J, e ∉ B.edgeSet := by
      intro e he heB
      have heNot : e ∉ (SimpleGraph.edge a b).edgeSet := by
        intro heEdge
        exact hNot ((Set.mem_singleton_iff.mp
          (SimpleGraph.edgeSet_edge_subset heEdge)) ▸ he)
      exact hAvoid₀ e he ((SimpleGraph.edgeSet_sdiff B (SimpleGraph.edge a b)).symm ▸
        ⟨heB,heNot⟩)
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,
      hinge_on_edge_deleted_host hT hHinge hAvoid,hOrder⟩,hNot⟩
  have hLast : (Survive.card : ℝ) ≤
      ((hinges (G \ B) lab F u v a b i).filter (fun J => s(a,b) ∉ J)).card := by
    exact_mod_cast card_le_card hSurvive
  change (Clean.card : ℝ) - loss ≤ _
  linarith

#print axioms clean_hinges_after_edge_deletion
end S07V49
