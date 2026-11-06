module
public import RequestProject.TypedTriangle.VortexPaidOuterPartition
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Vortex
open CatalogNative BasalIncidence

/-- The exterior decomposition is the literal union of the packing and
both already chosen paid modes. No basal witness is selected again. -/
theorem paid_outer_partition_retaining_decompositions {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I))
    (Q P₀ Dps Dbc U : Finset (Finset V))
    (R T Bank E Rtail Ps Y Yb Bc : Finset (Sym2 V))
    (hQ : IsPacking H F Q) (hPQ : P₀ ⊆ Q)
    (hQU : Q ⊆ U) (hDpsU : Dps ⊆ U) (hDbcU : Dbc ⊆ U)
    (hQR : Disjoint (Q.biUnion triEdges) Rtail)
    (hTail : Rtail = ((R ∪ T) ∪ Bank) ∪ E)
    (hRT : Disjoint R T) (hRB : Disjoint R Bank) (hRE : Disjoint R E)
    (hTB : Disjoint T Bank) (hTE : Disjoint T E) (hBE : Disjoint Bank E)
    (hMove : R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) = Ps ∪ Y)
    (hPY : Disjoint Ps Y) (hPs : IsDecomposition H F Ps Dps)
    (hBank : Bank = Bc ∪ Yb) (hBc : IsDecomposition H F Bc Dbc)
    (hBcYb : Disjoint Bc Yb) (hYYb : Disjoint Y Yb) :
    Basal H F (edges H \ (T ∪ (E ∪ (Y ∪ Yb)))) ∧
      Disjoint T (E ∪ (Y ∪ Yb)) ∧
      edges H \ (T ∪ (E ∪ (Y ∪ Yb))) = (Q.biUnion triEdges ∪ Ps) ∪ Bc ∧
      IsDecomposition H F (edges H \ (T ∪ (E ∪ (Y ∪ Yb)))) ((Q∪Dps)∪Dbc) ∧
      P₀ ⊆ (Q∪Dps)∪Dbc ∧ (Q∪Dps)∪Dbc ⊆ U := by
  obtain ⟨hBasal,hDis,hEq⟩ := paid_outer_partition H F Q R T Bank E Rtail Ps Y Yb Bc
    hQ hQR hTail hRT hRB hRE hTB hTE hBE hMove hPY ⟨Dps,hPs⟩
    hBank ⟨Dbc,hBc⟩ hBcYb hYYb
  let L := edges H \ (Rtail ∪ Q.biUnion triEdges)
  have hPsRL : Ps ⊆ R ∪ L := by
    rw [hMove]
    exact subset_union_left
  have hRTail : R ⊆ Rtail := by
    rw [hTail]
    exact (subset_union_left.trans subset_union_left).trans subset_union_left
  have hBTail : Bank ⊆ Rtail := by
    rw [hTail]
    exact subset_union_right.trans subset_union_left
  have hBcB : Bc ⊆ Bank := by rw [hBank]; exact subset_union_left
  have hLTail : Disjoint L Rtail :=
    disjoint_left.mpr fun _ he ht => (mem_sdiff.mp he).2 (mem_union_left _ ht)
  have hLQ : Disjoint L (Q.biUnion triEdges) :=
    disjoint_left.mpr fun _ he hq => (mem_sdiff.mp he).2 (mem_union_right _ hq)
  have hQPs : Disjoint (Q.biUnion triEdges) Ps :=
    (disjoint_union_right.mpr ⟨hQR.mono_right hRTail,hLQ.symm⟩).mono_right hPsRL
  have hPsBc : Disjoint Ps Bc :=
    (disjoint_union_left.mpr
      ⟨hRB.mono_right hBcB,hLTail.mono_right (hBcB.trans hBTail)⟩).mono_left hPsRL
  have hQPBc : Disjoint (Q.biUnion triEdges ∪ Ps) Bc :=
    disjoint_union_left.mpr ⟨hQR.mono_right (hBcB.trans hBTail),hPsBc⟩
  have hLiteral : IsDecomposition H F ((Q.biUnion triEdges ∪ Ps) ∪ Bc) ((Q∪Dps)∪Dbc) :=
    (hQ.isDecomposition.union hPs hQPs).union hBc hQPBc
  refine ⟨hBasal,hDis,hEq,?_,hPQ.trans (subset_union_left.trans subset_union_left),?_⟩
  · rw [hEq]
    exact hLiteral
  · exact union_subset (union_subset hQU hDpsU) hDbcU

#print axioms paid_outer_partition_retaining_decompositions
end TypedTriangle.Vortex
