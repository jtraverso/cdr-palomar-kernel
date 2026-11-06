/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V49.EdgeRoutes
public import RequestProject.S07V27.CoreComponent
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical S07V24 S07V25 S07V45 S07V49
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.Vortex

/-- A preplanned robust window remains a robust window of the actual paid
parent. Both missing spokes and missing path edges are charged explicitly. -/
theorem routeProp_after_sparse_payment {V I : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel C.Adj] (lab : V → I)
    (F : Set (Multiset I)) (W : Finset V) (t dC : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hRoute : S07V27.RouteProp G lab F t ε W)
    (hC : ∀ v, C.degree v ≤ dC)
    (hCap : (dC : ℝ) ≤ ε/4*Fintype.card V) :
    S07V27.RouteProp (G \ C) lab F t (ε/4) W := by
  intro Z B _ b hZ hB hb v x y hxy
  let D := C ⊔ B
  letI : DecidableRel D.Adj := Classical.decRel _
  have hDegree : ∀ z, D.degree z ≤ dC+b := by
    intro z
    have hNeighbors : D.neighborFinset z = C.neighborFinset z ∪ B.neighborFinset z := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset,mem_union]
      rfl
    rw [← SimpleGraph.card_neighborFinset_eq_degree,hNeighbors]
    exact (card_union_le _ _).trans (by
      rw [SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.card_neighborFinset_eq_degree]
      exact Nat.add_le_add (hC z) (hB z))
  have hεn : 0 ≤ ε*(Fintype.card V : ℝ) := mul_nonneg hε.le (by positivity)
  have hDCap : ((dC+b : ℕ) : ℝ) ≤ ε*Fintype.card V := by
    push_cast
    linarith
  let NC := C.neighborFinset v
  have hNC : NC.card ≤ dC := by
    simpa only [NC,SimpleGraph.card_neighborFinset_eq_degree] using hC v
  have hZC : ((Z ∪ NC).card : ℝ) ≤ ε*Fintype.card V := by
    have hUnion : ((Z ∪ NC).card : ℝ) ≤ Z.card + NC.card := by exact_mod_cast card_union_le Z NC
    have hNCR : (NC.card : ℝ) ≤ dC := by exact_mod_cast hNC
    linarith
  have hxy' : OrigAdm (G \ C) lab F v x y := hxy
  obtain ⟨hOriginal,hx,hy⟩ := resid_adm_orig hxy'
  obtain ⟨p,hp,hW,hAvoidVertices,hAvoidEdges⟩ :=
    hRoute (Z ∪ NC) D (dC+b) hZC hDegree hDCap v x y hOriginal
  have hLength : p.length = t := by
    exact SimpleGraph.mem_finsetWalkLength_iff.mp (mem_filter.mp hp).1
  have hPath : p.IsPath := (mem_filter.mp hp).2
  have hSpokes : ∀ z ∈ p.support, ¬ C.Adj v z := by
    intro z hz
    rcases support_of_pathsLen hp hz with rfl | rfl | hzInternal
    · exact hx
    · exact hy
    · obtain ⟨i,rfl⟩ := (mem_intlSet _ _ _).mp hzInternal
      intro hc
      exact hAvoidVertices i (mem_union_right _ (by
        simpa only [NC,SimpleGraph.mem_neighborFinset] using hc))
  have hPathEdges : ∀ k < t, ¬ C.Adj (p.getVert k) (p.getVert (k+1)) := by
    intro k hk hc
    exact hAvoidEdges k hk (Or.inl hc)
  obtain ⟨p',hLen',hSupport',hVertices'⟩ :=
    residual_walk p hSpokes (fun k hk => hPathEdges k (hLength ▸ hk))
  have hInternal : intlSet (t-1) p' = intlSet (t-1) p := by
    unfold intlSet intl
    simp only [hVertices']
  refine ⟨p',?_,hInternal ▸ hW,?_,?_⟩
  · simp only [pathsLen,mem_filter,SimpleGraph.mem_finsetWalkLength_iff]
    refine ⟨hLen'.trans hLength,?_⟩
    rw [SimpleGraph.Walk.isPath_def,hSupport']
    exact hPath.support_nodup
  · intro i hi
    have hEq : intl (t-1) p' i = intl (t-1) p i := hVertices' _
    rw [hEq] at hi
    exact hAvoidVertices i (mem_union_left _ hi)
  · intro k hk hBad
    rw [hVertices' k,hVertices' (k+1)] at hBad
    exact hAvoidEdges k hk (Or.inr hBad)

#print axioms routeProp_after_sparse_payment
end TypedTriangle.Vortex
