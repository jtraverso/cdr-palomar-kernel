/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexFixedWindowPositivePacking
public import RequestProject.TypedTriangle.G4NativeOneLayerBank
public import RequestProject.TypedTriangle.G4PositiveMomentBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.Vortex
open CatalogNative StockEntry BasalIncidence S07V42 TypedTriangle.LocalizedCover

/-- The complete G34 native result on a prescribed window. The exact seed
and H3/H4 of the complement after the basal stock, bank and reference are
explicit hypotheses; this theorem does not choose or resample that window. -/
theorem g34_native_result_on_fixed_prepared_window {I : Type}
    (F : Set (Multiset I)) (C α κ ηPack τ Λ qCore ρ τSel : ℝ)
    (h t : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hκ : 0 < κ)
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
      Disjoint (cover D) T → Disjoint R (cover D ∪ T) →
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
      (∀ v, (SparseEdge.degIn (cover D) v : ℝ) ≤
        qCore / 64 * Fintype.card V) →
      (∀ v, (SparseEdge.degIn (cover D) v : ℝ) ≤
        ρ * Fintype.card V) →
      (∀ v, (SelSimul.edeg R v : ℝ) ≤ τSel * Fintype.card V) →
      G34NativeResult H F W D R qCore ρ ηPack τ Λ τSel := by
  obtain ⟨n₀,hFixed⟩ :=
    positive_packing_on_fixed_prepared_window F C α κ ηPack τ Λ τSel h t
      hC hα hκ hη hτ hΛ ht ht3
  refine ⟨n₀,?_⟩
  intro V _ H ψ W D DT R T Bank E hn
  dsimp only
  intro hPath hSeed hPhysJ h3 h4 hPhys hD hR hT hBank hE
    hDT hRDT hBankDis hEDis hSupply hMode hDq hDcap hRd
  intro κi ι _ _ bad loc full hCount hLoc hFull
  have hCount' : ((Fintype.card κi + Fintype.card ι : ℕ) : ℝ) ≤
      Fintype.card V := by simpa using hCount
  obtain ⟨DR,Q,Rtail,Ps,Y,x,d,q,hDR,hDtail,hEq,hQ,hQR,hRes,
    hPhysRes,hMove,hPY,hPs,hYphys,hYin,hYdeg,hx,hCharge,hLoad,
    hLocOut,hFullOut⟩ :=
    hFixed H ψ W D DT R T Bank E hn hPath hSeed hPhysJ h3 h4 hPhys
      hD hR hT hBank hE hDT hRDT hBankDis hEDis hSupply hMode
      κi ι bad loc full hCount' hLoc hFull
  have hRL : Disjoint R (edges H \ (Rtail ∪ Q.biUnion triEdges)) := by
    apply disjoint_left.mpr
    intro e heR heL
    apply disjoint_left.mp hRDT heR
    exact mem_union.mpr (Or.inl (hRes heL))
  have hStockDeg : ∀ v,
      (((cover D).filter (fun e => v ∈ e)).card : ℝ) ≤
        ρ * Fintype.card V := by
    intro v
    simpa only [SparseEdge.degIn] using hDcap v
  have hRDeg : ∀ v,
      ((R.filter (fun e => v ∈ e)).card : ℝ) ≤
        τSel * Fintype.card V := by
    intro v
    simpa only [SelSimul.edeg] using hRd v
  have hJDeg : ∀ v,
      (((edges H \ (Rtail ∪ Q.biUnion triEdges)).filter
        (fun e => v ∈ e)).card : ℝ) ≤ ρ * Fintype.card V := by
    intro v
    have hc := Finset.card_le_card
      (Finset.filter_subset_filter (p := fun e => v ∈ e) hRes)
    have hc' : (((edges H \ (Rtail ∪ Q.biUnion triEdges)).filter
        (fun e => v ∈ e)).card : ℝ) ≤
        (((cover D).filter (fun e => v ∈ e)).card : ℝ) := by
      exact_mod_cast hc
    exact hc'.trans (hStockDeg v)
  have hLocY : ∀ k, |edgeSum (loc k) Y| ≤
      τ * Fintype.card V * (bad k).card +
      (3 * Λ * (bad k).card) *
        (((2*d+2*q : ℕ) : ℝ) + ρ * Fintype.card V +
          2 * (τSel * Fintype.card V) + ρ * Fintype.card V) / 2 := by
    intro k
    exact g4_actual_positive_moment_budget H F D hD R
      (edges H \ (Rtail ∪ Q.biUnion triEdges)) Ps Y hRL hPY hMove
      hR hPs (ρ * Fintype.card V) (τSel * Fintype.card V)
      (ρ * Fintype.card V) ((2*d+2*q : ℕ) : ℝ)
      (τ * Fintype.card V * (bad k).card) Λ hΛ.le
      hStockDeg hRDeg hJDeg (bad k) (loc k) (hLoc k) (hLocOut k)
  have hFullY : ∀ j, |edgeSum (full j) Y| ≤
      τ * (Fintype.card V : ℝ)^2 +
      (3 * Λ * Fintype.card V) *
        (((2*d+2*q : ℕ) : ℝ) + ρ * Fintype.card V +
          2 * (τSel * Fintype.card V) + ρ * Fintype.card V) / 2 := by
    intro j
    have htri : ∀ A, IsAllowed H F A →
        |triSum (full j) A| ≤
          3 * Λ * (A ∩ (univ : Finset V)).card := by
      intro A hA
      simpa using hFull j A hA
    simpa only [card_univ] using
      (g4_actual_positive_moment_budget H F D hD R
        (edges H \ (Rtail ∪ Q.biUnion triEdges)) Ps Y hRL hPY hMove
        hR hPs (ρ * Fintype.card V) (τSel * Fintype.card V)
        (ρ * Fintype.card V) ((2*d+2*q : ℕ) : ℝ)
        (τ * (Fintype.card V : ℝ)^2) Λ hΛ.le
        hStockDeg hRDeg hJDeg univ (full j) htri
        (by simpa only [card_univ] using hFullOut j))
  exact ⟨DR,Q,Rtail,Ps,Y,hD,hDR,hDtail,hQ,hQR,hRes,hPhysRes,
    hR,hRL,hDq,hDcap,hRd,hMove,hPY,hPs,hYin,hYdeg,hYphys,
    ⟨x,hx,hCharge⟩,d,q,hLoad,hLocOut,hFullOut,hLocY,hFullY⟩

#print axioms g34_native_result_on_fixed_prepared_window

end TypedTriangle.Vortex
