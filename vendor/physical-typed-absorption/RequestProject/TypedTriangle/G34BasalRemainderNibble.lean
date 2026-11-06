/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3BasalRemainderSplit
public import RequestProject.TypedTriangle.G4UnprotectedNibbleEntry
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A native one-layer interface: split the paid basal resources into a stock
and a basal reserve, then apply the monitored nibble to their exact complement.
This does not construct the resources or the bank outcome. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open BasalIncidence StockEntry ProtectedNibble LocalizedCover

theorem nibble_after_basal_remainder_split {I : Type}
    (F : Set (Multiset I)) (C α κ η τ L : ℝ) (h qMon : ℕ)
    (hC : 1 ≤ C) (hα : 0 < α) (hκ : 0 < κ)
    (hη : 0 < η) (hτ : 0 < τ) (hL : 0 < L) :
    ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (ψ : Finset V → ℝ)
        (D DT : Finset (Finset V))
        (R T Bank E : Finset (Sym2 V)),
        n₀ ≤ Fintype.card V →
        let B := (((cover D ∪ R) ∪ T) ∪ Bank) ∪ E
        let J := subHost H (edges H \ B)
        IsDiffuseSeed J F C ψ → IsPhysical J F (edges J) →
        CommonNbrCond J F α → HingeCond J F α h →
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
        ∀ (κi ι : Type) [Fintype κi] [Fintype ι]
          (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
          (full : ι → Sym2 V → ℝ),
          ((Fintype.card κi + Fintype.card ι : ℕ) : ℝ) ≤
            (Fintype.card V : ℝ) ^ qMon →
          (∀ k A, IsAllowed H F A →
            |triSum (loc k) A| ≤ 3 * L * (A ∩ bad k).card) →
          (∀ j A, IsAllowed H F A →
            |triSum (full j) A| ≤ 3 * L * A.card) →
          ∃ (DR Q : Finset (Finset V)) (Rtail : Finset (Sym2 V)),
            IsDecomposition H F Rtail DR ∧
            Disjoint (cover D) Rtail ∧
            cover D ∪ Rtail = B ∧
            IsPacking H F Q ∧
            Disjoint (Q.biUnion triEdges) Rtail ∧
            (edges H \ (Rtail ∪ Q.biUnion triEdges)) ⊆ cover D ∧
            IsPhysical H F (edges H \ (Rtail ∪ Q.biUnion triEdges)) ∧
            ∃ d q : ℕ, ((2*d + 2*q : ℕ) : ℝ) ≤ η * Fintype.card V ∧
              (∀ k, |edgeSum (loc k)
                  (edges H \ (Rtail ∪ Q.biUnion triEdges)) -
                  edgeSum (loc k) (cover D)| ≤
                τ * Fintype.card V * (bad k).card +
                  (3 * L * (bad k).card) * (2*d + 2*q : ℕ) / 2) ∧
              ∀ j, |edgeSum (full j)
                  (edges H \ (Rtail ∪ Q.biUnion triEdges)) -
                  edgeSum (full j) (cover D)| ≤
                τ * (Fintype.card V : ℝ)^2 +
                  (3 * L * Fintype.card V) * (2*d + 2*q : ℕ) / 2 := by
  obtain ⟨n₀,hFour⟩ :=
    g4_nibble_after_stock_deletion F C α κ η τ L h qMon
      hC hα hκ hη hτ hL
  refine ⟨n₀,?_⟩
  intro V _ H ψ D DT R T Bank E hn
  dsimp only
  intro hSeed hPhysJ h3 h4 hPhysH hD hR hT hBank hE
    hDT hRDT hBankDis hEDis hSupply κi ι _ _ bad loc full
    hCount hLoc hFull
  obtain ⟨DR,hDR,hDtail,hEq⟩ :=
    basal_remainder_split D DT R T Bank E hR hT hBank hE
      hDT hRDT hBankDis hEDis
  obtain ⟨Q,hQ,hQR,hRem,hRemPhys,d,q,hLoad,hLocOut,hFullOut⟩ :=
    hFour H ψ D DR (((R ∪ T) ∪ Bank) ∪ E) hn
      (by simpa only [hEq] using hSeed)
      (by simpa only [hEq] using hPhysJ)
      (by simpa only [hEq] using h3)
      (by simpa only [hEq] using h4)
      hPhysH hD hDR hDtail hSupply
      κi ι bad loc full hCount hLoc hFull
  exact ⟨DR,Q,((R ∪ T) ∪ Bank) ∪ E,hDR,hDtail,hEq,
    hQ,hQR,hRem,hRemPhys,d,q,hLoad,hLocOut,hFullOut⟩

#print axioms nibble_after_basal_remainder_split

end TypedTriangle.CatalogNative
