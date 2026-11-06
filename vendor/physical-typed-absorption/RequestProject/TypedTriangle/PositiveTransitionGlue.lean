/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.MonitoredStockTransition
public import RequestProject.TypedTriangle.CorePositiveRefiner
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.StockEntry
variable {V I : Type*} [Fintype V]

/-- Glue the actual packing to the positive withdrawal mode. The resulting
leftover is EXACTLY Y, not merely a physical subset of the stock. The protected
bank B stays untouched. No transport of a decomposition between hosts is used. -/
theorem positive_stock_transition_glue (H : Host V I) (F : Set (Multiset I))
    (B R : Finset (Sym2 V)) (Q : Finset (Finset V))
    (hRQ : R ⊆ edges H) (hBR : Disjoint B R) (hQ : IsPacking H F Q)
    (hQBR : Disjoint (Q.biUnion triEdges) (B∪R))
    (Ps Y : Finset (Sym2 V))
    (hMode : R∪(edges H\((B∪R)∪Q.biUnion triEdges)) = Ps∪Y)
    (hPY : Disjoint Ps Y) (hPs : Basal H F Ps) :
    ∃ Q' : Finset (Finset V), IsPacking H F Q' ∧
      Disjoint (Q'.biUnion triEdges) B ∧ edges H\(B∪Q'.biUnion triEdges) = Y := by
  let J := edges H\((B∪R)∪Q.biUnion triEdges)
  have hPsSub : Ps ⊆ R∪J := by rw [hMode]; exact subset_union_left
  have hQPs : Disjoint (Q.biUnion triEdges) Ps := by
    apply disjoint_left.mpr
    intro e heQ hePs
    rcases mem_union.mp (hPsSub hePs) with heR | heJ
    · exact disjoint_left.mp hQBR heQ (mem_union_right _ heR)
    · exact (mem_sdiff.mp heJ).2 (mem_union_right _ heQ)
  have hPsB : Disjoint Ps B := by
    apply disjoint_left.mpr
    intro e hePs heB
    rcases mem_union.mp (hPsSub hePs) with heR | heJ
    · exact disjoint_left.mp hBR heB heR
    · exact (mem_sdiff.mp heJ).2 (mem_union_left _ (mem_union_left _ heB))
  obtain ⟨DP,hDP⟩ := hPs
  have hDec := S07V26.isDecomposition_union hQPs hQ.isDecomposition hDP
  have hEdges : (Q∪DP).biUnion triEdges = Q.biUnion triEdges∪Ps := hDec.2.2
  refine ⟨Q∪DP,⟨hDec.1,hDec.2.1⟩,?_,?_⟩
  · rw [hEdges,disjoint_union_left]
    exact ⟨hQBR.mono_right subset_union_left,hPsB⟩
  · rw [hEdges]
    ext e
    have hm := (Finset.ext_iff.mp hMode) e
    simp only [mem_union,mem_sdiff,not_or] at hm ⊢
    have hr : e ∈ R → e ∈ edges H := fun he => hRQ he
    have hb : e ∈ B → e ∉ R := fun heB heR => disjoint_left.mp hBR heB heR
    have hqr : e ∈ Q.biUnion triEdges → e ∉ R :=
      fun heQ heR => disjoint_left.mp hQBR heQ (mem_union_right _ heR)
    have hqb : e ∈ Q.biUnion triEdges → e ∉ B :=
      fun heQ heB => disjoint_left.mp hQBR heQ (mem_union_left _ heB)
    have hpy : e ∈ Ps → e ∉ Y := fun heP heY => disjoint_left.mp hPY heP heY
    tauto

end TypedTriangle.StockEntry
