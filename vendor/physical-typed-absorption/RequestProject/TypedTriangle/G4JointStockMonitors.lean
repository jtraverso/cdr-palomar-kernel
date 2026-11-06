/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.MonitoredStockTransition
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-! A single actual stock transition retains both families of monitor estimates.
The two families are tested on the same nibble residue and the same final packing. -/

open Finset Classical
noncomputable section
namespace TypedTriangle.StockEntry
open BasalIncidence LocalizedCover
variable {V I : Type*} [Fintype V]

theorem joint_monitored_stock_transition (H : Host V I) (F : Set (Multiset I))
    (D DR P : Finset (Finset V)) (R : Finset (Sym2 V)) {κ : ℝ}
    (hD : IsDecomposition H F (cover D) D) (hR : IsDecomposition H F R DR)
    (hXR : Disjoint (cover D) R) (hPhys : IsPhysical H F (edges H))
    (hP : IsPacking H F P) (hPS : Disjoint (P.biUnion triEdges) (cover D∪R))
    (hSupply : ∀ u v, H.G.Adj u v → κ*Fintype.card V ≤ (good H F D u v).card)
    (d q : ℕ)
    (hdeg : ∀ v, (((edges H\(cover D∪R))\P.biUnion triEdges).filter
      (fun e => v ∈ e)).card ≤ d)
    (hwin : ((((edges H\(cover D∪R))\P.biUnion triEdges).card+
      q*(2*d+4*q):ℕ):ℝ) < q*κ*Fintype.card V)
    {κi ι : Type} [Fintype κi] [Fintype ι]
    (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
    (full : ι → Sym2 V → ℝ) (L Eₗ E𝓰 : ℝ) (hL : 0 ≤ L)
    (hloc : ∀ k T, IsAllowed H F T →
      |triSum (loc k) T| ≤ 3*L*(T∩bad k).card)
    (hfull : ∀ j T, IsAllowed H F T → |triSum (full j) T| ≤ 3*L*T.card)
    (hUl : ∀ k, |edgeSum (loc k) ((edges H\(cover D∪R))\P.biUnion triEdges)| ≤
      Eₗ*Fintype.card V*(bad k).card)
    (hUg : ∀ j, |edgeSum (full j) ((edges H\(cover D∪R))\P.biUnion triEdges)| ≤
      E𝓰*(Fintype.card V:ℝ)^2) :
    ∃ Q : Finset (Finset V), IsPacking H F Q ∧ Disjoint (Q.biUnion triEdges) R ∧
      (edges H\(R∪Q.biUnion triEdges)) ⊆ cover D ∧
      IsPhysical H F (edges H\(R∪Q.biUnion triEdges)) ∧
      (∀ k, |edgeSum (loc k) (edges H\(R∪Q.biUnion triEdges))-
          edgeSum (loc k) (cover D)| ≤
        Eₗ*Fintype.card V*(bad k).card+
          (3*L*(bad k).card)*(2*d+2*q:ℕ)/2) ∧
      ∀ j, |edgeSum (full j) (edges H\(R∪Q.biUnion triEdges))-
          edgeSum (full j) (cover D)| ≤
        E𝓰*(Fintype.card V:ℝ)^2+
          (3*L*Fintype.card V)*(2*d+2*q:ℕ)/2 := by
  obtain ⟨Q,hQ,hQR,hrem,hphys,hMom⟩ :=
    monitored_stock_transition H F D DR P R hD hR hXR hPhys hP hPS
      hSupply d q hdeg hwin
  refine ⟨Q,hQ,hQR,hrem,hphys,?_,?_⟩
  · intro k
    exact hMom (loc k) (bad k) L (Eₗ*Fintype.card V*(bad k).card)
      hL (hloc k) (hUl k)
  · intro j
    have htri : ∀ T, IsAllowed H F T →
        |triSum (full j) T| ≤ 3*L*(T∩(univ : Finset V)).card := by
      intro T hT
      simpa using hfull j T hT
    simpa only [inter_univ,card_univ] using
      hMom (full j) (univ : Finset V) L
        (E𝓰*(Fintype.card V:ℝ)^2) hL htri (hUg j)

end TypedTriangle.StockEntry
