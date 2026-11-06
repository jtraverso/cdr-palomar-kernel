/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G34BasalRemainderNibble
public import RequestProject.TypedTriangle.G4SelectorSameResidue
public import RequestProject.TypedTriangle.ActualResidualCharge
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex
open CatalogNative StockEntry BasalIncidence S07V42 TypedTriangle.LocalizedCover

/-- On an already prescribed window, the basal split and monitored nibble
produce one packing, and the existing selector acts on *that same* physical
remainder. The exact seed of the deleted complement is explicit. -/
theorem positive_packing_on_fixed_prepared_window {I : Type}
    (F : Set (Multiset I)) (C α κ ηPack τ Λ τSel : ℝ) (h t : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hκ : 0 < κ)
    (hη : 0 < ηPack) (hτ : 0 < τ) (hΛ : 0 < Λ)
    (ht : Odd t) (ht3 : 3 ≤ t) :
    ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V]
      (H : Host V I) (ψ : Finset V → ℝ)
      (W : Finset V) (D DT : Finset (Finset V))
      (R T Bank E : Finset (Sym2 V)),
      n₀ ≤ Fintype.card V →
      let B := (((cover D ∪ R) ∪ T) ∪ Bank) ∪ E
      let Jhost := subHost H (edges H \ B)
      S07V45.CorePathContract H.G H.lab F W t →
      IsDiffuseSeed Jhost F C ψ → IsPhysical Jhost F (edges Jhost) →
      CommonNbrCond Jhost F α → HingeCond Jhost F α h →
      IsPhysical H F (edges H) →
      IsDecomposition H F (cover D) D →
      Basal H F R → IsDecomposition H F T DT →
      Basal H F Bank → Basal H F E →
      Disjoint (cover D) T →
      Disjoint R (cover D ∪ T) →
      Disjoint Bank ((cover D ∪ R) ∪ T) →
      Disjoint E (((cover D ∪ R) ∪ T) ∪ Bank) →
      (∀ u v, H.G.Adj u v →
        κ * Fintype.card V ≤ (good H F D u v).card) →
      (∀ L : Finset (Sym2 V), L ⊆ cover D → IsPhysical H F L →
        ∃ Ps Y : Finset (Sym2 V), R ∪ L = Ps ∪ Y ∧
          Disjoint Ps Y ∧ Basal H F Ps ∧
          (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
          (∀ v, (SelSimul.edeg Y v : ℝ) ≤ τSel * Fintype.card V) ∧
          IsPhysical H F Y) →
      ∀ (κi ι : Type) [Fintype κi] [Fintype ι]
        (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
        (full : ι → Sym2 V → ℝ),
        ((Fintype.card κi + Fintype.card ι : ℕ) : ℝ) ≤
          Fintype.card V →
        (∀ k A, IsAllowed H F A →
          |triSum (loc k) A| ≤ 3 * Λ * (A ∩ bad k).card) →
        (∀ j A, IsAllowed H F A →
          |triSum (full j) A| ≤ 3 * Λ * A.card) →
        ∃ (DR Q : Finset (Finset V))
          (Rtail Ps Y : Finset (Sym2 V))
          (x : MCore H.G H.lab F W) (d q : ℕ),
          IsDecomposition H F Rtail DR ∧
          Disjoint (cover D) Rtail ∧ cover D ∪ Rtail = B ∧
          IsPacking H F Q ∧ Disjoint (Q.biUnion triEdges) Rtail ∧
          (edges H \ (Rtail ∪ Q.biUnion triEdges)) ⊆ cover D ∧
          IsPhysical H F (edges H \ (Rtail ∪ Q.biUnion triEdges)) ∧
          R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) = Ps ∪ Y ∧
          Disjoint Ps Y ∧ Basal H F Ps ∧ IsPhysical H F Y ∧
          (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
          (∀ v, (SelSimul.edeg Y v : ℝ) ≤ τSel * Fintype.card V) ∧
          (x : Sym2 V → ℤ) = SparseEdge.ind Y ∧
          clsQ H.G H.lab F W (x : Sym2 V → ℤ) ∈
            KZ H.G H.lab F W ∅ ∧
          ((2*d+2*q : ℕ) : ℝ) ≤ ηPack * Fintype.card V ∧
          (∀ k, |edgeSum (loc k)
              (edges H \ (Rtail ∪ Q.biUnion triEdges)) -
              edgeSum (loc k) (cover D)| ≤
            τ * Fintype.card V * (bad k).card +
              (3 * Λ * (bad k).card) * (2*d+2*q : ℕ) / 2) ∧
          ∀ j, |edgeSum (full j)
              (edges H \ (Rtail ∪ Q.biUnion triEdges)) -
              edgeSum (full j) (cover D)| ≤
            τ * (Fintype.card V : ℝ)^2 +
              (3 * Λ * Fintype.card V) * (2*d+2*q : ℕ) / 2 := by
  obtain ⟨n₀,hNibble⟩ :=
    nibble_after_basal_remainder_split F C α κ ηPack τ Λ h 1
      hC hα hκ hη hτ hΛ
  refine ⟨n₀,?_⟩
  intro V _ H ψ W D DT R T Bank E hn
  dsimp only
  intro hPath hSeed hPhysJ h3 h4 hPhys hD hR hT hBank hE
    hDT hRDT hBankDis hEDis hSupply hMode
    κi ι _ _ bad loc full hCount hLoc hFull
  have hCount' : ((Fintype.card κi + Fintype.card ι : ℕ) : ℝ) ≤
      (Fintype.card V : ℝ)^1 := by simpa using hCount
  obtain ⟨DR,Q,Rtail,hDR,hDtail,hEq,hQ,hQR,hRes,hPhysRes,
    d,q,hLoad,hLocOut,hFullOut⟩ :=
    hNibble H ψ D DT R T Bank E hn hSeed hPhysJ h3 h4 hPhys
      hD hR hT hBank hE hDT hRDT hBankDis hEDis hSupply
      κi ι bad loc full hCount' hLoc hFull
  obtain ⟨Ps,Y,hMove,hPY,hPs,hYin,hYdeg,hYphys⟩ :=
    hMode (edges H \ (Rtail ∪ Q.biUnion triEdges)) hRes hPhysRes
  have hRE : R ⊆ edges H := CorePaid.basal_subset_edges hR
  have hYE : Y ⊆ edges H := by
    intro e heY
    have heRL : e ∈ R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) := by
      rw [hMove]
      exact mem_union_right _ heY
    rcases mem_union.mp heRL with heR | heL
    · exact hRE heR
    · exact (mem_sdiff.mp heL).1
  have hYsub : Y ⊆ SparseEdge.edges (indG H.G W) :=
    g4_positive_payload_in_child H W Y hYE hYin
  obtain ⟨x,hx,hCharge⟩ :=
    actual_physical_residue_charge H F hPath ht ht3 Y hYphys hYsub
  exact ⟨DR,Q,Rtail,Ps,Y,x,d,q,hDR,hDtail,hEq,hQ,hQR,hRes,
    hPhysRes,hMove,hPY,hPs,hYphys,hYin,hYdeg,hx,hCharge,hLoad,
    hLocOut,hFullOut⟩

#print axioms positive_packing_on_fixed_prepared_window

end TypedTriangle.Vortex
