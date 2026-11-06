/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.G34NativePackingOneLayer
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! Extract exactly the physical positive residue, its core certificate and
its simultaneous moments from the native G34 one-layer conclusion. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.CatalogNative

open BasalIncidence S07V40 S07V42 TypedTriangle.LocalizedCover

theorem g34_packing_provider_of_native_result {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I))
    (W : Finset V) (D : Finset (Finset V)) (R : Finset (Sym2 V))
    (q ρ ηPack τ Λ τSel : ℝ)
    (hNative : ∀ (κi ι : Type) [Fintype κi] [Fintype ι]
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
                    2*(τSel*Fintype.card V)+ρ*Fintype.card V)/2) :
    ∀ (κi ι : Type) [Fintype κi] [Fintype ι]
        (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
        (full : ι → Sym2 V → ℝ),
      ((Fintype.card κi+Fintype.card ι:ℕ):ℝ) ≤ Fintype.card V →
      (∀ k A, IsAllowed H F A → |triSum (loc k) A| ≤
        3*Λ*(A∩bad k).card) →
      (∀ j A, IsAllowed H F A → |triSum (full j) A| ≤ 3*Λ*A.card) →
      ∃ (Y : Finset (Sym2 V)) (x : MCore H.G H.lab F W) (load : ℝ),
        Y ⊆ cover D ∪ R ∧
        Y ⊆ edges H ∧
        (x : Sym2 V → ℤ) = ind Y ∧
        clsQ H.G H.lab F W (x : Sym2 V → ℤ) ∈ KZ H.G H.lab F W ∅ ∧
        load ≤ ηPack * Fintype.card V ∧
        (∀ k, |edgeSum (loc k) Y| ≤
          τ * Fintype.card V * (bad k).card +
          (3 * Λ * (bad k).card) *
            (load + ρ*Fintype.card V + 2*(τSel*Fintype.card V) +
              ρ*Fintype.card V) / 2) ∧
        ∀ j, |edgeSum (full j) Y| ≤
          τ * (Fintype.card V : ℝ)^2 +
          (3 * Λ * Fintype.card V) *
            (load + ρ*Fintype.card V + 2*(τSel*Fintype.card V) +
              ρ*Fintype.card V) / 2 := by
  intro κi ι _ _ bad loc full hCount hLoc hFull
  have hCount' :
      ((Fintype.card κi + Fintype.card ι : ℕ) : ℝ) ≤
        (Fintype.card V : ℝ)^1 := by simpa using hCount
  obtain ⟨DR,Q,Rtail,Ps,Y,_,_,_,_,_,hRes,_,hRbasal,_,_,_,_,hMove,_,_,_,_,_,
    ⟨x,hxY,hx⟩,d',q',hload,_,_,hLocY,hFullY⟩ :=
    hNative κi ι bad loc full hCount' hLoc hFull
  have hYF : Y ⊆ cover D ∪ R := by
    intro e heY
    have he : e ∈ R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) := by
      rw [hMove]
      exact mem_union_right _ heY
    rcases mem_union.mp he with heR | heL
    · exact mem_union_right _ heR
    · exact mem_union_left _ (hRes heL)
  have hYE : Y ⊆ edges H := by
    intro e heY
    have he : e ∈ R ∪ (edges H \ (Rtail ∪ Q.biUnion triEdges)) := by
      rw [hMove]
      exact mem_union_right _ heY
    rcases mem_union.mp he with heR | heL
    · exact CorePaid.basal_subset_edges hRbasal heR
    · exact (mem_sdiff.mp heL).1
  exact ⟨Y,x,((2*d'+2*q':ℕ):ℝ),hYF,hYE,hxY,hx,hload,hLocY,hFullY⟩

end TypedTriangle.CatalogNative

#print axioms TypedTriangle.CatalogNative.g34_packing_provider_of_native_result
