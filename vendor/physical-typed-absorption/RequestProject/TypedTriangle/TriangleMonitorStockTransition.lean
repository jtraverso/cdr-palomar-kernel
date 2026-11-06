/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.MonitoredStockTransition
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.StockEntry
open BasalIncidence LocalizedCover
variable {V I : Type*} [Fintype V]

/-- Join the SAME monitored packing to its actual stock cover-down. The final
remainder and all its moments are identified exactly; no replacement packing
is chosen to obtain the quota. This is entry in the stock with ambient
physicality, not yet intrinsic child-lattice entry. -/
theorem monitored_stock_transition_retaining_initial_packing (H : Host V I) (F : Set (Multiset I))
    (D DR P : Finset (Finset V)) (R : Finset (Sym2 V)) {κ : ℝ}
    (hD : IsDecomposition H F (cover D) D) (hR : IsDecomposition H F R DR)
    (hXR : Disjoint (cover D) R) (hPhys : IsPhysical H F (edges H))
    (hP : IsPacking H F P) (hPS : Disjoint (P.biUnion triEdges) (cover D∪R))
    (hSupply : ∀ u v, H.G.Adj u v → κ*Fintype.card V ≤ (good H F D u v).card)
    (d q : ℕ)
    (hdeg : ∀ v, (((edges H\(cover D∪R))\P.biUnion triEdges).filter (fun e => v ∈ e)).card ≤ d)
    (hwin : ((((edges H\(cover D∪R))\P.biUnion triEdges).card+q*(2*d+4*q):ℕ):ℝ) <
      q*κ*Fintype.card V) :
    ∃ Q : Finset (Finset V), P ⊆ Q ∧ IsPacking H F Q ∧ Disjoint (Q.biUnion triEdges) R ∧
      (edges H\(R∪Q.biUnion triEdges)) ⊆ cover D ∧
      IsPhysical H F (edges H\(R∪Q.biUnion triEdges)) ∧
      ∀ (lam : Sym2 V → ℝ) (bad : Finset V) (L E0 : ℝ), 0 ≤ L →
        (∀ T, IsAllowed H F T → |triSum lam T| ≤ 3*L*(T∩bad).card) →
        |edgeSum lam ((edges H\(cover D∪R))\P.biUnion triEdges)| ≤ E0 →
        |edgeSum lam (edges H\(R∪Q.biUnion triEdges))-edgeSum lam (cover D)| ≤
          E0+(3*L*bad.card)*(2*d+2*q:ℕ)/2 := by
  let X := cover D
  let U := (edges H\(X∪R))\P.biUnion triEdges
  have hS := S07V26.isDecomposition_union hXR hD hR
  have hXH : X ⊆ edges H := by
    intro e he
    change e ∈ cover D at he
    rw [←hD.2.2] at he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact triEdges_subset_edges (hD.1 T hT) heT
  have hPH : P.biUnion triEdges ⊆ edges H\(X∪R) := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
    exact mem_sdiff.mpr ⟨triEdges_subset_edges (hP.1 T hT) heT,
      fun heS => disjoint_left.mp hPS (mem_biUnion.mpr ⟨T,hT,heT⟩) heS⟩
  have hUphys : IsPhysical H F U :=
    isPhysical_sdiff (isPhysical_sdiff_of_decomposition hPhys hS (by
      rw [←hS.2.2]
      intro e he
      obtain ⟨T,hT,heT⟩ := mem_biUnion.mp he
      exact triEdges_subset_edges (hS.1 T hT) heT))
      (isPhysical_of_isDecomposition hP.isDecomposition) hPH
  have hUX : Disjoint U X := by
    apply disjoint_left.mpr
    intro e he hx
    exact (mem_sdiff.mp (mem_sdiff.mp he).1).2 (mem_union_left _ hx)
  obtain ⟨A,hA,hCov,hSub,_,hleft,hMom⟩ := stock_cover_down_monitored hD hSupply U
    (sdiff_subset.trans sdiff_subset) hUX hUphys hdeg hwin
  have hPA : Disjoint (P.biUnion triEdges) (A.biUnion triEdges) := by
    apply disjoint_left.mpr
    intro e heP heA
    rcases mem_union.mp (hSub heA) with heU | heX
    · exact (mem_sdiff.mp heU).2 heP
    · exact disjoint_left.mp hPS heP (mem_union_left _ heX)
  have hQdec := S07V26.isDecomposition_union hPA hP.isDecomposition hA.isDecomposition
  have hQedges : (P∪A).biUnion triEdges = P.biUnion triEdges∪A.biUnion triEdges := by
    ext e
    simp only [mem_biUnion,mem_union]
    aesop
  have hFinal : edges H\(R∪(P∪A).biUnion triEdges) = X\A.biUnion triEdges := by
    rw [hQedges]
    ext e
    have hu : e ∈ U ↔ e ∈ edges H ∧ e ∉ X ∧ e ∉ R ∧ e ∉ P.biUnion triEdges := by
      simp only [U,mem_sdiff,mem_union,not_or]
      tauto
    have hcov : e ∈ U → e ∈ A.biUnion triEdges := fun he => hCov he
    have hxp : e ∈ X → e ∉ P.biUnion triEdges :=
      fun heX heP => disjoint_left.mp hPS heP (mem_union_left _ heX)
    have hxr : e ∈ X → e ∉ R := fun heX heR => disjoint_left.mp hXR heX heR
    have hxe : e ∈ X → e ∈ edges H := fun he => hXH he
    simp only [mem_sdiff,mem_union,not_or]
    tauto
  refine ⟨P∪A,subset_union_left,⟨hQdec.1,hQdec.2.1⟩,?_,?_,?_,?_⟩
  · rw [hQedges,disjoint_union_left]
    refine ⟨hPS.mono_right subset_union_right,?_⟩
    apply disjoint_left.mpr
    intro e heA heR
    rcases mem_union.mp (hSub heA) with heU | heX
    · exact (mem_sdiff.mp (mem_sdiff.mp heU).1).2 (mem_union_right _ heR)
    · exact disjoint_left.mp hXR heX heR
  · rw [hFinal]
    exact sdiff_subset
  · rw [hFinal]
    exact hleft
  · intro lam bad L E0 hL htri hUmon
    rw [hFinal]
    exact hMom lam bad L E0 hL htri hUmon
#print axioms monitored_stock_transition_retaining_initial_packing
end TypedTriangle.StockEntry
