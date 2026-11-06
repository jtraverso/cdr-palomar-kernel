/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G34PackingProviderExtraction
public import RequestProject.TypedTriangle.G4ActualBankStratumWeightsCore
public import RequestProject.TypedTriangle.G4NativePackingToBank
public import RequestProject.TypedTriangle.G4NativeScaleCapPackage
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! One actual G34 packing and the physical bank created before that packing.
This is a one-layer statement on the same positive residue Y. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.CatalogNative

open BasalIncidence S07V40 S07V42 S07V43 S07V44 S07V46 S07V47
open TypedTriangle.LocalizedCover

def G34NativeResult {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I))
    (W : Finset V) (D : Finset (Finset V)) (R : Finset (Sym2 V))
    (q ρ ηPack τ Λ τSel : ℝ) : Prop :=
    ∀ (κi ι : Type) [Fintype κi] [Fintype ι]
        (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
        (full : ι → Sym2 V → ℝ),
        ((Fintype.card κi+Fintype.card ι:ℕ):ℝ) ≤
          (Fintype.card V:ℝ)^1 →
        (∀ k A, IsAllowed H F A → |triSum (loc k) A| ≤
          3*Λ*(A∩bad k).card) →
        (∀ j A, IsAllowed H F A → |triSum (full j) A| ≤ 3*Λ*A.card) →
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
            ρ*Fintype.card V) ∧
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
                (3*Λ*(bad k).card)*(2*d'+2*q':ℕ)/2) ∧
            (∀ j, |edgeSum (full j) (edges H\(Rtail∪Q.biUnion triEdges))-
                edgeSum (full j) (cover D)| ≤
              τ*(Fintype.card V:ℝ)^2+
                (3*Λ*Fintype.card V)*(2*d'+2*q':ℕ)/2) ∧
            (∀ k, |edgeSum (loc k) Y| ≤
              τ*Fintype.card V*(bad k).card+
                (3*Λ*(bad k).card)*
                  (((2*d'+2*q':ℕ):ℝ)+ρ*Fintype.card V+
                    2*(τSel*Fintype.card V)+ρ*Fintype.card V)/2) ∧
            ∀ j, |edgeSum (full j) Y| ≤
              τ*(Fintype.card V:ℝ)^2+
                (3*Λ*Fintype.card V)*
                  (((2*d'+2*q':ℕ):ℝ)+ρ*Fintype.card V+
                    2*(τSel*Fintype.card V)+ρ*Fintype.card V)/2

theorem activate_bank_after_g34_result (α β qCore : ℝ)
    (h d c E Rc A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hqCore : 0 < qCore)
    (hβα : β ≤ α) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∃ nWeights : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (W : Finset V)
        (D : Finset (Finset V)) (R : Finset (Sym2 V))
        (C0 : CoreCompression H.G H.lab F W d c E)
        (P q Ecell z N L : ℕ)
        (Mon : ∀ Z : Finset V, CatalogGen C0 Rc Z →
          PhysicalMonitors C0 Rc Z A M K)
        (Fm : FullMonitor C0 Rc A M K)
        (hP : P = 2 * gammaL A M L)
        (F0 : Finset (Sym2 V))
        (hF0 : cover D ∪ R ⊆ F0)
        (hBank : MacroBank (protSetting C0 Rc P q Ecell z F0) L N)
        (hgen : ∀ j, CatalogGen C0 Rc
          (Zstrat (protSetting C0 Rc P q Ecell z F0) N j))
        (γ η ηPack τ ρ τSel : ℝ),
        nWeights ≤ Fintype.card V →
        qCore * Fintype.card V / 2 ≤ W.card →
        CommonNbrCond H F α → HingeCond H F α h →
        SparseEdge.CommonNbrCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β →
        SparseEdge.HingeCond
          (H.G.comap (Subtype.val : {x // x ∈ W} → V))
          (H.lab ∘ Subtype.val) F β h →
        (z : ℝ) ≤ coreDelta β h * W.card →
        (z : ℝ) ≤ β / 2 * W.card →
        (z : ℝ) * 2 ^ Nat.choose (h+1) 2 ≤ β / 2 * W.card →
        (z : ℝ) ≤ S07V37.delOf (β/2) h * W.card →
        (L+2)*K ≤ Fintype.card V →
        0 ≤ η → 0 < γ →
        γ * Fintype.card V ≤ q →
        η * ((2 * Ecell *
          (childSetting C0 Rc P q Ecell z).Bstar : ℕ) : ℝ) / γ ≤ 1 →
        (K : ℝ) *
          (τ + (3 * Λ / 2) * (ηPack + 2 * ρ + 2 * τSel)) ≤ η →
        ((protSetting C0 Rc P q Ecell z F0).K
          (Zr (protSetting C0 Rc P q Ecell z F0) N) ≠ ⊥ →
          1 + η * (Fintype.card V : ℝ) ^ 2 ≤ 2 * N) →
        G34NativeResult H F W D R qCore ρ ηPack τ Λ τSel →
        ∃ (Y : Finset (Sym2 V)) (x : MCore H.G H.lab F W) (J : ℕ),
          Y ⊆ F0 ∧ Y ⊆ edges H ∧
          J ≤ L ∧ (x : Sym2 V → ℤ) = ind Y ∧
          ProtOutcome C0 Rc P q Ecell z F0 N J x ∧
          ((protSetting C0 Rc P q Ecell z F0).K
            (Zr (protSetting C0 Rc P q Ecell z F0) N) ≠ ⊥ → J = L) := by
  obtain ⟨Λ,hΛ,nWeights,hWeights⟩ :=
    choose_weights_on_actual_bank_core α β qCore h d c E Rc A M K
      hα hβ hqCore hβα
  refine ⟨Λ,hΛ,nWeights,?_⟩
  intro V I _ H F W D R C0 P q Ecell z N L Mon Fm hP F0 hF0 hBank hgen
    γ η ηPack τ ρ τSel hn hWlo h3 h4 hCore3 hCore4
    hzCore hz3 hz4 hzDel hsize hη hγ hqn hcapacity hKB hN hNative
  let S := protSetting C0 Rc P q Ecell z F0
  let MonS : ∀ ℓ, PhysicalMonitors C0 Rc
      (Zstrat S N (ℓ+1)) A M K :=
    fun ℓ => Mon _ (hgen (ℓ+1))
  obtain ⟨loc,full,hLocRep,hFullRep,hLocTri,hFullTri⟩ :=
    hWeights H F W C0 S N L z MonS Fm hBank rfl hn hWlo h3 h4
      hCore3 hCore4 hzCore hz3 hz4 hzDel
  have hPack := g34_packing_provider_of_native_result H F W D R
    qCore ρ ηPack τ Λ τSel hNative
  exact activate_bank_after_one_monitored_packing C0 Rc A M K P q Ecell z N L
    Mon Fm hP F0 hBank hgen (Fintype.card V) Λ η γ ηPack τ ρ τSel
    hΛ.le hη hγ hsize hqn hcapacity hKB loc full
    (fun ℓ hg j x => by simpa only [S, MonS] using hLocRep ℓ j x)
    hFullRep hLocTri hFullTri
    (fun badF locF fullF hCount hLoc hFull => by
      obtain ⟨Y,x,load,hYDR,hYE,hxY,hx,hload,hLocY,hFullY⟩ :=
        hPack _ _ badF locF fullF hCount hLoc hFull
      exact ⟨Y,x,load,hYDR.trans hF0,hYE,hxY,hx,hload,hLocY,hFullY⟩)
    hN

#print axioms TypedTriangle.CatalogNative.activate_bank_after_g34_result

end TypedTriangle.CatalogNative

