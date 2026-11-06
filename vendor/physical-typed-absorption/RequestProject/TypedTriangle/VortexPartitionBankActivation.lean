/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.VortexFixedWindowG34PartitionResult
public import RequestProject.TypedTriangle.G4NativeOneLayerBank
public import RequestProject.TypedTriangle.CoreEdgeGraph
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

open Finset Classical
noncomputable section
set_option maxHeartbeats 3200000
set_option autoImplicit false

namespace TypedTriangle.CatalogNative
open BasalIncidence S07V40 S07V42 S07V43 S07V44 S07V46 S07V47
open TypedTriangle.LocalizedCover

/-- Activate the actual bank on one monitored packing and retain that same
packing, selector split and reserved-union identity for the final gluing. -/
theorem activate_partition_bank_after_g34_result (α β qCore : ℝ)
    (h d c E Rc A M K : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hqCore : 0 < qCore)
    (hβα : β ≤ α) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∃ nWeights : ℕ,
      ∀ {V I : Type} [Fintype V] (H : Host V I)
        (F : Set (Multiset I)) (W : Finset V)
        (D : Finset (Finset V)) (R B : Finset (Sym2 V))
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
        G34NativePartitionResult H F W D R B qCore ρ ηPack τ Λ τSel →
        ∃ (DR Q : Finset (Finset V)) (Rtail Ps Y : Finset (Sym2 V))
          (x : MCore H.G H.lab F W) (J : ℕ),
          IsDecomposition H F Rtail DR ∧
          Disjoint (cover D) Rtail ∧ cover D ∪ Rtail = B ∧
          IsPacking H F Q ∧ Disjoint (Q.biUnion triEdges) Rtail ∧
          (edges H \ (Rtail ∪ Q.biUnion triEdges)) ⊆ cover D ∧
          IsPhysical H F (edges H \ (Rtail ∪ Q.biUnion triEdges)) ∧
          Basal H F R ∧ Disjoint R (edges H \ (Rtail ∪ Q.biUnion triEdges)) ∧
          R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) = Ps ∪ Y ∧
          Disjoint Ps Y ∧ Basal H F Ps ∧ IsPhysical H F Y ∧
          (∀ e ∈ Y, ∀ v ∈ e, v ∈ W) ∧
          (∀ v, (SelSimul.edeg Y v : ℝ) ≤ τSel * Fintype.card V) ∧
          Y ⊆ F0 ∧ Y ⊆ edges H ∧
          J ≤ L ∧ (x : Sym2 V → ℤ) = ind Y ∧
          ProtOutcome C0 Rc P q Ecell z F0 N J x ∧
          ((protSetting C0 Rc P q Ecell z F0).K
            (Zr (protSetting C0 Rc P q Ecell z F0) N) ≠ ⊥ → J = L) := by
  obtain ⟨Λ,hΛ,nWeights,hWeights⟩ :=
    choose_weights_on_actual_bank_core α β qCore h d c E Rc A M K
      hα hβ hqCore hβα
  refine ⟨Λ,hΛ,nWeights,?_⟩
  intro V I _ H F W D R B C0 P q Ecell z N L Mon Fm hP F0 hF0 hBank hgen
    γ η ηPack τ ρ τSel hn hWlo h3 h4 hCore3 hCore4
    hzCore hz3 hz4 hzDel hsize hη hγ hqn hcapacity hKB hN hNative
  let S := protSetting C0 Rc P q Ecell z F0
  let MonS : ∀ ℓ, PhysicalMonitors C0 Rc (Zstrat S N (ℓ+1)) A M K :=
    fun ℓ => Mon _ (hgen (ℓ+1))
  obtain ⟨loc,full,hLocRep,hFullRep,hLocTri,hFullTri⟩ :=
    hWeights H F W C0 S N L z MonS Fm hBank rfl hn hWlo h3 h4
      hCore3 hCore4 hzCore hz3 hz4 hzDel
  let badF : Fin (L+1) × Fin K → Finset V :=
    fun k => Zstrat S N (k.1.val+1)
  let locF : Fin (L+1) × Fin K → Sym2 V → ℝ :=
    fun k => loc k.1.val k.2
  have hCount :
      ((Fintype.card (Fin (L+1) × Fin K) + Fintype.card (Fin K) : ℕ) : ℝ) ≤
        Fintype.card V := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact_mod_cast (show (L+1)*K+K ≤ Fintype.card V from by nlinarith only [hsize])
  have hTri : ∀ k T, IsAllowed H F T →
      |triSum (locF k) T| ≤ 3 * Λ * (T ∩ badF k).card := by
    intro k T hT
    exact hLocTri k.1.val k.2 T hT
  obtain ⟨DR,Q,Rtail,Ps,Y,hD,hDR,hDtail,hEq,hQ,hQR,hRes,hPhysRes,
    hR,hRL,hDq,hDcap,hRd,hMove,hPY,hPs,hYin,hYdeg,hYphys,
    hCharge,d',q',hLoad,hLocOut,hFullOut,hLocY,hFullY⟩ :=
    hNative (Fin (L+1) × Fin K) (Fin K) badF locF full
      (by simpa using hCount) hTri hFullTri
  obtain ⟨x,hxY,hx⟩ := hCharge
  let load : ℝ := ((2*d'+2*q' : ℕ) : ℝ)
  have hLoc : ∀ ℓ ≤ L, ∀ j,
      |edgeSum (loc ℓ j) Y| ≤
        τ * Fintype.card V * (Zstrat S N (ℓ+1)).card +
        (3 * Λ * (Zstrat S N (ℓ+1)).card) *
          (load + ρ*Fintype.card V + 2*(τSel*Fintype.card V) +
            ρ*Fintype.card V) / 2 := by
    intro ℓ hℓ j
    exact hLocY ⟨⟨ℓ, Nat.lt_succ_iff.mpr hℓ⟩,j⟩
  obtain ⟨J,hJ,hOutcome,hFinish,_⟩ :=
    activate_bank_from_native_packing_moments C0 Rc A M K P q Ecell z N L
      Mon Fm hP F0 Y hBank hgen (Fintype.card V) Λ η γ ηPack τ ρ τSel load
      hΛ.le hη hγ hqn hcapacity hLoad hKB x hxY hx loc full
      (fun ℓ hg j => by simpa only [S,MonS] using hLocRep ℓ j x)
      (fun j => hFullRep j x) hLoc hFullY hN
  have hYDR : Y ⊆ cover D ∪ R := by
    intro e he
    have hm : e ∈ R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) := by
      rw [hMove]
      exact mem_union_right _ he
    rcases mem_union.mp hm with heR | heL
    · exact mem_union_right _ heR
    · exact mem_union_left _ (hRes heL)
  have hYE : Y ⊆ edges H := hYDR.trans (Finset.union_subset
    (CorePaid.basal_subset_edges ⟨D,hD⟩) (CorePaid.basal_subset_edges hR))
  exact ⟨DR,Q,Rtail,Ps,Y,x,J,hDR,hDtail,hEq,hQ,hQR,hRes,hPhysRes,
    hR,hRL,hMove,hPY,hPs,hYphys,hYin,hYdeg,hYDR.trans hF0,hYE,hJ,hxY,
    hOutcome,hFinish⟩

#print axioms activate_partition_bank_after_g34_result

end TypedTriangle.CatalogNative
