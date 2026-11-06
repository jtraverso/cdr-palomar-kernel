/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G3ExactComplementOneLayer
public import RequestProject.TypedTriangle.G4UnprotectedNibbleEntry
public import RequestProject.TypedTriangle.G4SelectorSameResidue
public import RequestProject.TypedTriangle.ActualResidualCharge
public import RequestProject.TypedTriangle.G4PositiveMomentBudget
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! One native G3/G4 transition: choose the core and protected resources,
delete their exact basal union, then run the monitored nibble and cover-down
on that same complement. No iteration or terminal bank activation is claimed. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.CatalogNative

open BasalIncidence StockEntry LocalizedCover S07V40 S07V42

theorem native_monitored_packing_one_layer {I : Type} (F : Set (Multiset I))
    (α C ηChild : ℝ) (h qMon : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hChild : 0 < ηChild)
    (hh : 6 ≤ h) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧
      ∃ (d c E d' c' E' Ecell A M K P : ℕ) (κ εBank : ℝ),
      0 < κ ∧ 0 < εBank ∧
      P = 2*S07V46.gammaL A M
        (Fintype.card (Cat d (catR (α*q^h/4) d c E d' c' E'))) ∧
      ∀ ηPack τ L ρTarget : ℝ,
      0 < ηPack → 0 < τ → 0 < L → 0 < ρTarget →
      ∃ ηT : ℝ, 0 < ηT ∧
      ∃ τSel : ℝ, 0 < τSel ∧ τSel ≤ ρTarget ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → CommonNbrCond H F α →
        HingeCond H F α h →
        ∃ W : Finset V, q*Fintype.card V/2 ≤ W.card ∧
          (W.card:ℝ) < 2*q*Fintype.card V ∧
          SparseEdge.CommonNbrCond
            (H.G.comap (Subtype.val : {x // x ∈ W} → V))
            (H.lab ∘ Subtype.val) F (α*q^h/4) ∧
          SparseEdge.HingeCond
            (H.G.comap (Subtype.val : {x // x ∈ W} → V))
            (H.lab ∘ Subtype.val) F (α*q^h/4) h ∧
          ∀ (T : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT : ℕ),
            IsDecomposition H F T DT →
            (∀ v, SparseEdge.degIn T v ≤ dT) →
            (dT:ℝ) ≤ ηT*Fintype.card V →
            ∃ (D : Finset (Finset V)) (R : Finset (Sym2 V)),
              (∃ (qSel z N : ℕ)
                (C0 : CoreCompression H.G H.lab F W d c E),
                let Rc := catR (α*q^h/4) d c E d' c' E'
                ∃ (Mon : ∀ Z : Finset V,
                    S07V44.CatalogGen C0 Rc Z →
                      S07V44.PhysicalMonitors C0 Rc Z A M K)
                  (Fm : S07V46.FullMonitor C0 Rc A M K),
                let S := S07V47.protSetting C0 Rc P qSel Ecell z
                  ((cover D∪R)∪T)
                0 < qSel ∧
                εBank/4 * W.card ≤ qSel ∧
                N = ⌊κ*(W.card:ℝ)^2⌋₊ ∧
                (z:ℝ) ≤ coreDelta (α*q^h/4) h * W.card ∧
                (z:ℝ) ≤ (α*q^h/4) * W.card / 2 ∧
                (z:ℝ) * 2 ^ Nat.choose (h+1) 2 ≤
                  (α*q^h/4) / 2 * W.card ∧
                (z:ℝ) ≤ S07V37.delOf (α*q^h/4) h * W.card ∧
                (z:ℝ) ≤ S07V37.delOf ((α*q^h/4)/2) h * W.card ∧
                (∀ Z : Finset V, Z.card ≤ z →
                  Nonempty (DelCompression H.G H.lab F Z d' c' E')) ∧
                MacroBank S (Fintype.card (Cat d Rc)) N ∧
                ∀ j, S07V44.CatalogGen C0 Rc (Zstrat S N j)) ∧
            ∀ (κi ι : Type) [Fintype κi] [Fintype ι]
              (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
              (full : ι → Sym2 V → ℝ),
              ((Fintype.card κi+Fintype.card ι:ℕ):ℝ) ≤
                (Fintype.card V:ℝ)^qMon →
              (∀ k A, IsAllowed H F A → |triSum (loc k) A| ≤
                3*L*(A∩bad k).card) →
              (∀ j A, IsAllowed H F A → |triSum (full j) A| ≤ 3*L*A.card) →
              ∃ (DR Q : Finset (Finset V))
                (Rtail Ps Y : Finset (Sym2 V)),
                IsDecomposition H F (cover D) D ∧
                IsDecomposition H F Rtail DR ∧
                Disjoint (cover D) Rtail ∧
                IsPacking H F Q ∧
                Disjoint (Q.biUnion triEdges) Rtail ∧
                (edges H\(Rtail∪Q.biUnion triEdges)) ⊆ cover D ∧
                IsPhysical H F (edges H\(Rtail∪Q.biUnion triEdges)) ∧
                Basal H F R ∧
                Disjoint R (edges H\(Rtail∪Q.biUnion triEdges)) ∧
                (∀ v, (SparseEdge.degIn (cover D) v:ℝ) ≤
                  (q/64)*Fintype.card V) ∧
                (∀ v, (SparseEdge.degIn (cover D) v:ℝ) ≤
                  ρTarget*Fintype.card V) ∧
                (∀ v, (SelSimul.edeg R v:ℝ) ≤ τSel*Fintype.card V) ∧
                R∪(edges H\(Rtail∪Q.biUnion triEdges)) = Ps∪Y ∧
                Disjoint Ps Y ∧ Basal H F Ps ∧
                (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
                (∀ v, (SelSimul.edeg Y v:ℝ) ≤ τSel*Fintype.card V) ∧
                IsPhysical H F Y ∧
                (∃ x : MCore H.G H.lab F W,
                  (x : Sym2 V → ℤ) = ind Y ∧
                  clsQ H.G H.lab F W (x : Sym2 V → ℤ) ∈
                    KZ H.G H.lab F W ∅) ∧
                ∃ d' q' : ℕ, ((2*d'+2*q':ℕ):ℝ) ≤ ηPack*Fintype.card V ∧
                  (∀ k, |edgeSum (loc k) (edges H\(Rtail∪Q.biUnion triEdges))-
                      edgeSum (loc k) (cover D)| ≤
                    τ*Fintype.card V*(bad k).card+
                      (3*L*(bad k).card)*(2*d'+2*q':ℕ)/2) ∧
                  (∀ j, |edgeSum (full j) (edges H\(Rtail∪Q.biUnion triEdges))-
                      edgeSum (full j) (cover D)| ≤
                    τ*(Fintype.card V:ℝ)^2+
                      (3*L*Fintype.card V)*(2*d'+2*q':ℕ)/2) ∧
                  (∀ k, |edgeSum (loc k) Y| ≤
                    τ*Fintype.card V*(bad k).card+
                      (3*L*(bad k).card)*
                        (((2*d'+2*q':ℕ):ℝ)+ρTarget*Fintype.card V+
                          2*(τSel*Fintype.card V)+ρTarget*Fintype.card V)/2) ∧
                  ∀ j, |edgeSum (full j) Y| ≤
                    τ*(Fintype.card V:ℝ)^2+
                      (3*L*Fintype.card V)*
                        (((2*d'+2*q':ℕ):ℝ)+ρTarget*Fintype.card V+
                          2*(τSel*Fintype.card V)+ρTarget*Fintype.card V)/2 := by
  let α' := min (α/2) (S07V49.hingeConstB α 1 h)
  have hα' : 0 < α' := lt_min (by positivity)
    (S07V49.hingeConstB_pos hα (by norm_num) (by omega))
  obtain ⟨q,hq,hq1,d,c,E,d',c',E',Ecell,A,M,K,P,κ,εBank,hκ,hεBank,hP,hExact⟩ :=
    native_exact_complement_one_layer F α C ηChild h hα hC hChild hh
  refine ⟨q,hq,hq1,d,c,E,d',c',E',Ecell,A,M,K,P,κ,εBank,hκ,hεBank,hP,?_⟩
  intro ηPack τ L ρTarget hPack hτ hL hρTarget
  obtain ⟨ηT,hηT,κX,hκX,τSel,hτSel,hτTarget,t,ht,ht3,nG,hG⟩ :=
    hExact ρTarget hρTarget
  obtain ⟨nFour,hFour⟩ :=
    g4_nibble_after_stock_deletion F (2*C) α' κX ηPack τ L
      (2*h-3) qMon (by linarith) hα' hκX hPack hτ hL
  refine ⟨ηT,hηT,τSel,hτSel,hτTarget,max nG nFour,?_⟩
  intro V _ H φ hn hSeed hPhys h3 h4
  obtain ⟨W,hWlo,hWhi,hCt,h3Core,h4Core,hNative⟩ :=
    hG H φ ((le_max_left _ _).trans hn) hSeed hPhys h3 h4
  refine ⟨W,hWlo,hWhi,h3Core,h4Core,?_⟩
  intro T DT dT hT hTd hTs
  obtain ⟨D,R,U,E₀,D₀,ψ,hD,hDT,hRdis,hRbasal,hDq,hDcap,hRd,hSupply,hMode,hBank,hSub,hAvoid,hBasal,
    ⟨Rtail,DR,hDR,hDtail,hEq⟩,hE,hEDec,hHole,hSeedJ,hPhysJ,h3J,h4J⟩ :=
    hNative T DT dT hT hTd hTs
  refine ⟨D,R,(by
    rcases hBank with ⟨qSel,z,N,C0,Mon,Fm,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩
    exact ⟨qSel,z,N,C0,Mon,Fm,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩),?_⟩
  intro κi ι _ _ bad loc full hCount hLoc hFull
  have h3J' : CommonNbrCond
      (subHost H (edges H\(cover D∪Rtail))) F α' := by
    exact commonNbrCond_mono (by simpa only [hEq] using h3J)
      (min_le_left _ _)
  have h4J' : HingeCond
      (subHost H (edges H\(cover D∪Rtail))) F α' (2*h-3) := by
    exact hingeCond_mono (by simpa only [hEq] using h4J)
      (min_le_right _ _)
  obtain ⟨Q,hQ,hQR,hRes,hPhysRes,d',q',hLoad,hLocOut,hFullOut⟩ :=
    hFour H ψ D DR Rtail ((le_max_right _ _).trans hn)
      (by simpa only [hEq] using hSeedJ)
      (by simpa only [hEq] using hPhysJ)
      h3J' h4J' hPhys hD hDR hDtail hSupply
      κi ι bad loc full hCount hLoc hFull
  obtain ⟨Ps,Y,hMove,hPY,hPs,hYin,hYdeg,hYphys⟩ :=
    hMode (edges H\(Rtail∪Q.biUnion triEdges)) hRes hPhysRes
  have hRL : Disjoint R (edges H\(Rtail∪Q.biUnion triEdges)) := by
    apply disjoint_left.mpr
    intro e heR heL
    apply disjoint_left.mp hRdis heR
    exact mem_union.mpr (Or.inl (hRes heL))
  have hUE : U ⊆ edges H :=
    (subset_union_left : U ⊆ U∪SampledResource.lift W E₀).trans
      (CorePaid.basal_subset_edges hBasal)
  have hRE : R ⊆ edges H := by
    intro e heR
    apply hUE
    exact hSub (mem_union.mpr (Or.inl
      (mem_union.mpr (Or.inr heR))))
  have hYE : Y ⊆ edges H := by
    intro e heY
    have heRL : e ∈ R∪(edges H\(Rtail∪Q.biUnion triEdges)) := by
      rw [hMove]
      exact mem_union.mpr (Or.inr heY)
    rcases mem_union.mp heRL with heR | heL
    · exact hRE heR
    · exact (mem_sdiff.mp heL).1
  have hYsub : Y ⊆ SparseEdge.edges (indG H.G W) :=
    g4_positive_payload_in_child H W Y hYE hYin
  obtain ⟨x,hx,hK⟩ :=
    actual_physical_residue_charge H F hCt ht ht3 Y hYphys hYsub
  have hStockDeg : ∀ v,
      (((cover D).filter (fun e => v ∈ e)).card:ℝ) ≤
        ρTarget*Fintype.card V := by
    intro v
    simpa only [SparseEdge.degIn] using hDcap v
  have hRDeg : ∀ v, ((R.filter (fun e => v ∈ e)).card:ℝ) ≤
      τSel*Fintype.card V := by
    intro v
    simpa only [SelSimul.edeg] using hRd v
  have hJDeg : ∀ v,
        (((edges H\(Rtail∪Q.biUnion triEdges)).filter
        (fun e => v ∈ e)).card:ℝ) ≤ ρTarget*Fintype.card V := by
    intro v
    have hc := Finset.card_le_card
      (Finset.filter_subset_filter (p:=fun e => v ∈ e) hRes)
    have hc' : (((edges H\(Rtail∪Q.biUnion triEdges)).filter
        (fun e => v ∈ e)).card:ℝ) ≤
        (((cover D).filter (fun e => v ∈ e)).card:ℝ) := by
      exact_mod_cast hc
    exact hc'.trans (hStockDeg v)
  have hLocY : ∀ k, |edgeSum (loc k) Y| ≤
      τ*Fintype.card V*(bad k).card+
        (3*L*(bad k).card)*
          (((2*d'+2*q':ℕ):ℝ)+ρTarget*Fintype.card V+
            2*(τSel*Fintype.card V)+ρTarget*Fintype.card V)/2 := by
    intro k
    exact g4_actual_positive_moment_budget H F D hD R
      (edges H\(Rtail∪Q.biUnion triEdges)) Ps Y hRL hPY hMove
      hRbasal hPs (ρTarget*Fintype.card V)
      (τSel*Fintype.card V) (ρTarget*Fintype.card V)
      ((2*d'+2*q':ℕ):ℝ) (τ*Fintype.card V*(bad k).card) L hL.le
      hStockDeg hRDeg hJDeg (bad k) (loc k) (hLoc k) (hLocOut k)
  have hFullY : ∀ j, |edgeSum (full j) Y| ≤
      τ*(Fintype.card V:ℝ)^2+
        (3*L*Fintype.card V)*
          (((2*d'+2*q':ℕ):ℝ)+ρTarget*Fintype.card V+
            2*(τSel*Fintype.card V)+ρTarget*Fintype.card V)/2 := by
    intro j
    have htri : ∀ A, IsAllowed H F A →
        |triSum (full j) A| ≤ 3*L*(A∩(univ : Finset V)).card := by
      intro A hA
      simpa using hFull j A hA
    simpa only [card_univ] using
      (g4_actual_positive_moment_budget H F D hD R
        (edges H\(Rtail∪Q.biUnion triEdges)) Ps Y hRL hPY hMove
        hRbasal hPs (ρTarget*Fintype.card V)
        (τSel*Fintype.card V) (ρTarget*Fintype.card V)
        ((2*d'+2*q':ℕ):ℝ) (τ*(Fintype.card V:ℝ)^2) L hL.le
        hStockDeg hRDeg hJDeg univ (full j) htri
        (by simpa only [card_univ] using hFullOut j))
  exact ⟨DR,Q,Rtail,Ps,Y,hD,hDR,hDtail,hQ,hQR,hRes,hPhysRes,
    hRbasal,hRL,hDq,hDcap,hRd,hMove,hPY,hPs,hYin,hYdeg,hYphys,⟨x,hx,hK⟩,
    d',q',hLoad,hLocOut,hFullOut,hLocY,hFullY⟩

#print axioms native_monitored_packing_one_layer

end TypedTriangle.CatalogNative
