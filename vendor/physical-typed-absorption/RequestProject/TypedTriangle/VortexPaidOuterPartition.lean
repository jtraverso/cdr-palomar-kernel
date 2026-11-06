/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexReservedTerminalPartition
public import RequestProject.TypedTriangle.CoreEdgeGraph
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option autoImplicit false

namespace TypedTriangle.Vortex
open CatalogNative BasalIncidence

/-- Glue the actual packing and selector mode while retaining both the
reserved terminal stock and the reference for the recursive child. -/
theorem paid_outer_partition {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I))
    (Q : Finset (Finset V)) (R T Bank E Rtail Ps Y Yb Bc : Finset (Sym2 V))
    (hQ : IsPacking H F Q) (hQR : Disjoint (Q.biUnion triEdges) Rtail)
    (hTail : Rtail = ((R ∪ T) ∪ Bank) ∪ E)
    (hRT : Disjoint R T) (hRB : Disjoint R Bank) (hRE : Disjoint R E)
    (hTB : Disjoint T Bank) (hTE : Disjoint T E) (hBE : Disjoint Bank E)
    (hMove : R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) = Ps ∪ Y)
    (hPY : Disjoint Ps Y) (hPs : Basal H F Ps)
    (hBank : Bank = Bc ∪ Yb) (hBc : Basal H F Bc)
    (hBcYb : Disjoint Bc Yb) (hYYb : Disjoint Y Yb) :
    Basal H F (edges H \ (T ∪ (E ∪ (Y ∪ Yb)))) ∧
      Disjoint T (E ∪ (Y ∪ Yb)) ∧
      edges H \ (T ∪ (E ∪ (Y ∪ Yb))) =
        (Q.biUnion triEdges ∪ Ps) ∪ Bc := by
  let L := edges H \ (Rtail ∪ Q.biUnion triEdges)
  have hPsRL : Ps ⊆ R ∪ L := by
    rw [hMove]
    exact Finset.subset_union_left
  have hYRL : Y ⊆ R ∪ L := by
    rw [hMove]
    exact Finset.subset_union_right
  have hRTail : R ⊆ Rtail := by
    rw [hTail]
    exact (Finset.subset_union_left.trans Finset.subset_union_left).trans
      Finset.subset_union_left
  have hTTail : T ⊆ Rtail := by
    rw [hTail]
    exact (Finset.subset_union_right.trans Finset.subset_union_left).trans
      Finset.subset_union_left
  have hBTail : Bank ⊆ Rtail := by
    rw [hTail]
    exact Finset.subset_union_right.trans Finset.subset_union_left
  have hETail : E ⊆ Rtail := by rw [hTail]; exact Finset.subset_union_right
  have hBcB : Bc ⊆ Bank := by rw [hBank]; exact Finset.subset_union_left
  have hYbB : Yb ⊆ Bank := by rw [hBank]; exact Finset.subset_union_right
  have hLTail : Disjoint L Rtail := by
    exact Finset.disjoint_left.mpr fun e he ht =>
      (Finset.mem_sdiff.mp he).2 (Finset.mem_union_left _ ht)
  have hLQ : Disjoint L (Q.biUnion triEdges) := by
    exact Finset.disjoint_left.mpr fun e he hq =>
      (Finset.mem_sdiff.mp he).2 (Finset.mem_union_right _ hq)
  have hQPs : Disjoint (Q.biUnion triEdges) Ps :=
    (Finset.disjoint_union_right.mpr ⟨hQR.mono_right hRTail,hLQ.symm⟩).mono_right hPsRL
  have hPsBc : Disjoint Ps Bc := by
    apply (Finset.disjoint_union_left.mpr
      ⟨hRB.mono_right hBcB,hLTail.mono_right (hBcB.trans hBTail)⟩).mono_left hPsRL
  have hQPBc : Disjoint (Q.biUnion triEdges ∪ Ps) Bc :=
    Finset.disjoint_union_left.mpr ⟨hQR.mono_right (hBcB.trans hBTail),hPsBc⟩
  have hQBasal : Basal H F (Q.biUnion triEdges) := ⟨Q,hQ.1,hQ.2,rfl⟩
  have hAllBasal := Basal.union (Basal.union hQBasal hPs hQPs) hBc hQPBc
  have hQY : Disjoint (Q.biUnion triEdges) Y :=
    (Finset.disjoint_union_right.mpr ⟨hQR.mono_right hRTail,hLQ.symm⟩).mono_right hYRL
  have hPsT : Disjoint Ps T := (Finset.disjoint_union_left.mpr
    ⟨hRT,hLTail.mono_right hTTail⟩).mono_left hPsRL
  have hPsE : Disjoint Ps E := (Finset.disjoint_union_left.mpr
    ⟨hRE,hLTail.mono_right hETail⟩).mono_left hPsRL
  have hPsYb : Disjoint Ps Yb := (Finset.disjoint_union_left.mpr
    ⟨hRB.mono_right hYbB,hLTail.mono_right (hYbB.trans hBTail)⟩).mono_left hPsRL
  have hBcY : Disjoint Bc Y := (Finset.disjoint_union_right.mpr
    ⟨hRB.symm.mono_left hBcB,hLTail.symm.mono_left (hBcB.trans hBTail)⟩).mono_right hYRL
  have hQAvoid : Disjoint (Q.biUnion triEdges) (T ∪ (E ∪ (Y ∪ Yb))) :=
    Finset.disjoint_union_right.mpr ⟨hQR.mono_right hTTail,
      Finset.disjoint_union_right.mpr ⟨hQR.mono_right hETail,
        Finset.disjoint_union_right.mpr ⟨hQY,hQR.mono_right (hYbB.trans hBTail)⟩⟩⟩
  have hPsAvoid : Disjoint Ps (T ∪ (E ∪ (Y ∪ Yb))) :=
    Finset.disjoint_union_right.mpr ⟨hPsT,Finset.disjoint_union_right.mpr
      ⟨hPsE,Finset.disjoint_union_right.mpr ⟨hPY,hPsYb⟩⟩⟩
  have hBcAvoid : Disjoint Bc (T ∪ (E ∪ (Y ∪ Yb))) :=
    Finset.disjoint_union_right.mpr ⟨hTB.symm.mono_left hBcB,
      Finset.disjoint_union_right.mpr ⟨hBE.mono_left hBcB,
        Finset.disjoint_union_right.mpr ⟨hBcY,hBcYb⟩⟩⟩
  have hAllAvoid : Disjoint ((Q.biUnion triEdges ∪ Ps) ∪ Bc)
      (T ∪ (E ∪ (Y ∪ Yb))) := Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨hQAvoid,hPsAvoid⟩,hBcAvoid⟩
  have hEq : edges H \ (T ∪ (E ∪ (Y ∪ Yb))) =
      (Q.biUnion triEdges ∪ Ps) ∪ Bc := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨heH,hnot⟩ := Finset.mem_sdiff.mp he
      by_cases heQ : e ∈ Q.biUnion triEdges
      · exact mem_union_left _ (mem_union_left _ heQ)
      by_cases heBc : e ∈ Bc
      · exact mem_union_right _ heBc
      have hRL : e ∈ R ∪ L := by
        by_cases heTail : e ∈ Rtail
        · rw [hTail] at heTail
          rcases mem_union.mp heTail with he | heE
          · rcases mem_union.mp he with he | heB
            · rcases mem_union.mp he with heR | heT
              · exact mem_union_left _ heR
              · exact False.elim (hnot (mem_union_left _ heT))
            · have heBank : e ∈ Bc ∪ Yb := by rwa [← hBank]
              rcases mem_union.mp heBank with heBc' | heYb
              · exact False.elim (heBc heBc')
              · exact False.elim (hnot (mem_union_right _
                  (mem_union_right _ (mem_union_right _ heYb))))
          · exact False.elim (hnot (mem_union_right _ (mem_union_left _ heE)))
        · exact mem_union_right _ (Finset.mem_sdiff.mpr
            ⟨heH,fun hc => (mem_union.mp hc).elim heTail heQ⟩)
      have hePY : e ∈ Ps ∪ Y := by rwa [← hMove]
      rcases mem_union.mp hePY with hePs | heY
      · exact mem_union_left _ (mem_union_right _ hePs)
      · exact False.elim (hnot (mem_union_right _
          (mem_union_right _ (mem_union_left _ heY))))
    · intro e he
      exact Finset.mem_sdiff.mpr ⟨CorePaid.basal_subset_edges hAllBasal he,
        fun hc => Finset.disjoint_left.mp hAllAvoid he hc⟩
  have hTY : Disjoint T Y := by
    apply (Finset.disjoint_union_right.mpr
      ⟨hRT.symm,hLTail.symm.mono_left hTTail⟩).mono_right hYRL
  refine ⟨?_,Finset.disjoint_union_right.mpr
    ⟨hTE,Finset.disjoint_union_right.mpr ⟨hTY,hTB.mono_right hYbB⟩⟩,hEq⟩
  rw [hEq]
  exact hAllBasal

#print axioms paid_outer_partition

end TypedTriangle.Vortex
