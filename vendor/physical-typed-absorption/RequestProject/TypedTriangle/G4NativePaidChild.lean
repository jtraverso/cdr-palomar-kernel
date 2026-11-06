/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G4NativeBankEntry
public import RequestProject.TypedTriangle.NativeActivatedChild
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Export the entire actual bank, its basal complement and the paid child
from the same native one-layer packing residue. -/

open Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

namespace TypedTriangle.CatalogNative

open BasalIncidence S07V40 S07V42 S07V43 S07V44 S07V47
open TypedTriangle.LocalizedCover

theorem native_paid_child_one_layer {I : Type} (F : Set (Multiset I))
    (α C ηChild : ℝ) (h : ℕ)
    (hα : 0 < α) (hC : 1 ≤ C) (hChild : 0 < ηChild)
    (hh : 6 ≤ h) :
    ∃ q : ℝ, 0 < q ∧
      ∃ (d c E d' c' E' Ecell A M K P : ℕ) (κ εBank : ℝ),
      0 < κ ∧ 0 < εBank ∧
      ∃ ηT : ℝ, 0 < ηT ∧ ∃ n₀ : ℕ,
      ∀ {V : Type} [Fintype V] (H : Host V I) (φ : Finset V → ℝ),
        n₀ ≤ Fintype.card V → IsDiffuseSeed H F C φ →
        IsPhysical H F (edges H) → CommonNbrCond H F α →
        HingeCond H F α h →
        ∃ W : Finset V,
          ∀ (T : Finset (Sym2 V)) (DT : Finset (Finset V)) (dT : ℕ),
            IsDecomposition H F T DT →
            (∀ v, SparseEdge.degIn T v ≤ dT) →
            (dT : ℝ) ≤ ηT * Fintype.card V →
            ∃ (D : Finset (Finset V)) (R : Finset (Sym2 V))
              (qSel z N : ℕ)
              (C0 : CoreCompression H.G H.lab F W d c E),
              ∃ (Y : Finset (Sym2 V)) (x : MCore H.G H.lab F W) (J : ℕ),
                let Rc := catR (α*q^h/4) d c E d' c' E'
                let L := Fintype.card (Cat d Rc)
                let F0 := ((cover D ∪ R) ∪ T)
                let S := protSetting C0 Rc P qSel Ecell z F0
                MacroBank S L N ∧ Y ⊆ F0 ∧ J ≤ L ∧
                (x : Sym2 V → ℤ) = ind Y ∧
                ProtOutcome C0 Rc P qSel Ecell z F0 N J x ∧
                ∃ Yb Bc : Finset (Sym2 V),
                  Y ∪ Yb ⊆ edges H ∧
                  physBasal H.G H.lab F Bc ∧ Disjoint Bc F0 ∧
                  Br S N = Bc ∪ Yb ∧ Disjoint Bc Yb ∧
                  Disjoint Y Yb ∧
                  ind (Y ∪ Yb) ∈ LamCore H.G H.lab F W ∧
                  Yb ⊆ childEdges H.G W := by
  obtain ⟨q,hq,d,c,E,d',c',E',Ecell,A,M,K,P,κ,εBank,
    hκ,hεBank,ηT,hηT,n₀,hEntry⟩ :=
    native_bank_entry_one_layer F α C ηChild h hα hC hChild hh
  refine ⟨q,hq,d,c,E,d',c',E',Ecell,A,M,K,P,κ,εBank,
    hκ,hεBank,ηT,hηT,n₀,?_⟩
  intro V _ H φ hn hSeed hPhys h3 h4
  obtain ⟨W,hForChild⟩ := hEntry H φ hn hSeed hPhys h3 h4
  refine ⟨W,?_⟩
  intro T DT dT hT hTd hTs
  obtain ⟨D,R,qSel,z,N,C0,Y,x,J,hBank,hYF,hYE,hJ,hxY,hOut⟩ :=
    hForChild T DT dT hT hTd hTs
  let Rc := catR (α*q^h/4) d c E d' c' E'
  let L := Fintype.card (Cat d Rc)
  let F0 := ((cover D ∪ R) ∪ T)
  let S := protSetting C0 Rc P qSel Ecell z F0
  obtain ⟨Yb,Bc,hBcPhys,hBcF,hWhole,hBcYb,hYYb,hLam,hYbChild⟩ :=
    activated_child_and_whole_complement C0 F0 hBank hJ
      Y hYF x hxY hOut
  have hYbE : Yb ⊆ edges H := by
    intro e he
    have heAdj := SparseEdge.mem_edges.mp (hYbChild he)
    induction e using Sym2.ind with
    | _ u v =>
      exact SparseEdge.mem_edges.mpr ((indG_le H.G W) heAdj)
  have hYtotE : Y ∪ Yb ⊆ edges H := union_subset hYE hYbE
  exact ⟨D,R,qSel,z,N,C0,Y,x,J,hBank,hYF,hJ,hxY,hOut,
    Yb,Bc,hYtotE,hBcPhys,hBcF,hWhole,hBcYb,hYYb,hLam,hYbChild⟩

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.native_paid_child_one_layer
