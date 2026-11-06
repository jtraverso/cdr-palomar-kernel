/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.TriangleMonitorFixedWindowPositivePacking
public import RequestProject.TypedTriangle.G4PositiveMomentBudget
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

/-- The native monitored result with the actual reserved union retained.
The extra equality identifies the same Rtail for every packing witness. -/
def G34NativePartitionResultRetainingPacking {V I : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I))
    (W : Finset V) (D : Finset (Finset V)) (R B : Finset (Sym2 V))
    (q ρ ηPack τ Λ τSel : ℝ) (Data : Finset (Finset V) → Prop) : Prop :=
    ∀ (κi ι : Type) [Fintype κi] [Fintype ι]
        (bad : κi → Finset V) (loc : κi → Sym2 V → ℝ)
        (full : ι → Sym2 V → ℝ),
        ((Fintype.card κi+Fintype.card ι:ℕ):ℝ) ≤
          (Fintype.card V:ℝ)^1 →
        (∀ k A, IsAllowed H F A → |triSum (loc k) A| ≤
          3*Λ*(A∩bad k).card) →
        (∀ j A, IsAllowed H F A → |triSum (full j) A| ≤ 3*Λ*A.card) →
        ∃ (P₀ DR Q : Finset (Finset V))
          (Rtail Ps Y : Finset (Sym2 V)),
          P₀ ⊆ Q ∧ Data P₀ ∧
          IsDecomposition H F (cover D) D ∧
          IsDecomposition H F Rtail DR ∧
          Disjoint (cover D) Rtail ∧
          cover D ∪ Rtail = B ∧
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

/-- The actual initial packing and its same-window triangle tests. -/
def InitialTriangleMonitorData {V I ν : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (J : Host V I)
    (φ : Finset V → ℝ) (w : ν → Finset V → ℝ) (η τ : ℝ)
    (P₀ : Finset (Finset V)) : Prop :=
  IsPacking H F P₀ ∧ (∀ A ∈ P₀, IsAllowed J F A) ∧
  (∀ v, (((edges J\P₀.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
  ∀ k, |(∑ A ∈ P₀, w k A)-(∑ A ∈ allowed J F, φ A*w k A)| ≤ τ*(Fintype.card V:ℝ)^2

/-- Monitor conclusions measured against the original diffuse seed. -/
def OriginalTriangleMonitorData {V I ν : Type} [Fintype V]
    (H : Host V I) (F : Set (Multiset I)) (φ : Finset V → ℝ)
    (w : ν → Finset V → ℝ) (η τ : ℝ) (P₀ : Finset (Finset V)) : Prop :=
  IsPacking H F P₀ ∧
  (∀ v, (((edges H\P₀.biUnion triEdges).filter (fun e => v ∈ e)).card:ℝ) ≤ η*Fintype.card V) ∧
  ∀ k, |(∑ A ∈ P₀, w k A)-(∑ A ∈ allowed H F, φ A*w k A)| ≤ τ*(Fintype.card V:ℝ)^2

theorem G34NativePartitionResultRetainingPacking.map_data {V I : Type} [Fintype V]
    {H : Host V I} {F : Set (Multiset I)} {W : Finset V}
    {D : Finset (Finset V)} {R B : Finset (Sym2 V)}
    {q ρ ηPack τ Λ τSel : ℝ} {Data Data' : Finset (Finset V) → Prop}
    (h : G34NativePartitionResultRetainingPacking H F W D R B q ρ ηPack τ Λ τSel Data)
    (hMap : ∀ P, Data P → Data' P) :
    G34NativePartitionResultRetainingPacking H F W D R B q ρ ηPack τ Λ τSel Data' := by
  intro κi ι _ _ bad loc full hCount hLoc hFull
  obtain ⟨P₀,DR,Q,Rtail,Ps,Y,hPQ,hData,hRest⟩ := h κi ι bad loc full hCount hLoc hFull
  exact ⟨P₀,DR,Q,Rtail,Ps,Y,hPQ,hMap P₀ hData,hRest⟩

lemma polynomial_monitor_sum_bound (n : ℝ) (q : ℕ) (hn : 2 ≤ n) :
    n+n^q ≤ n^(q+2) := by
  have hn1 : 1 ≤ n := by linarith
  have hnp : 1 ≤ n^q := one_le_pow₀ hn1
  have hpn0 : 0 ≤ n^q := pow_nonneg (by linarith) _
  have ha : n ≤ n^(q+1) := by
    simpa only [one_mul,pow_succ] using mul_le_mul_of_nonneg_right hnp (by linarith : 0≤n)
  have hb : n^q ≤ n^(q+1) := by
    simpa only [mul_one,pow_succ] using mul_le_mul_of_nonneg_left hn1 hpn0
  calc n+n^q ≤ 2*n^(q+1) := by linarith only [ha,hb]
    _ ≤ n^(q+1)*n := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hn (pow_nonneg (by linarith) (q+1))
    _ = n^(q+2) := by simp only [pow_add,pow_one,pow_two,mul_assoc]

end TypedTriangle.CatalogNative

namespace TypedTriangle.Vortex
open CatalogNative StockEntry BasalIncidence S07V42 TypedTriangle.LocalizedCover

theorem g34_native_partition_result_on_fixed_prepared_window_with_triangle_monitors {I : Type}
    (F : Set (Multiset I)) (C α κ ηPack τ Λ qCore ρ τSel : ℝ)
    (h t qStat : ℕ) (hC : 1 ≤ C) (hα : 0 < α) (hκ : 0 < κ)
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
      ∀ (ν : Type) [Fintype ν] (w : ν → Finset V → ℝ),
      (Fintype.card ν:ℝ) ≤ (Fintype.card V:ℝ)^qStat →
      (∀ k A, IsAllowed H F A → |w k A| ≤ 1) →
      G34NativePartitionResultRetainingPacking H F W D R B qCore ρ ηPack τ Λ τSel
        (InitialTriangleMonitorData H F Jhost ψ w ηPack τ) := by
  obtain ⟨n₀,hFixed⟩ :=
    positive_packing_on_fixed_prepared_window_with_triangle_monitors F C α κ ηPack τ Λ τSel h t (qStat+2)
      hC hα hκ hη hτ hΛ ht ht3
  refine ⟨max n₀ 2,?_⟩
  intro V _ H ψ W D DT R T Bank E hn
  dsimp only
  intro hPath hSeed hPhysJ h3 h4 hPhys hD hR hT hBank hE
    hDT hRDT hBankDis hEDis hSupply hMode hDq hDcap hRd ν _ w hν hw
  intro κi ι _ _ bad loc full hCount hLoc hFull
  have hCount' : ((Fintype.card κi + Fintype.card ι : ℕ) : ℝ) ≤
      Fintype.card V := by simpa using hCount
  push_cast at hCount'
  have hn2 : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast (le_max_right _ _).trans hn
  have hCombined : ((Fintype.card κi+Fintype.card ι+Fintype.card ν:ℕ):ℝ) ≤
      (Fintype.card V:ℝ)^(qStat+2) := by
    have hh := polynomial_monitor_sum_bound (Fintype.card V:ℝ) qStat hn2
    push_cast
    nlinarith only [hCount',hν,hh]
  obtain ⟨P₀,DR,Q,Rtail,Ps,Y,x,d,q,hPQ,hP₀,hAllow,hSparse,hQuota,hDR,hDtail,hEq,hQ,hQR,hRes,
    hPhysRes,hMove,hPY,hPs,hYphys,hYin,hYdeg,hx,hCharge,hLoad,
    hLocOut,hFullOut⟩ :=
    hFixed H ψ W D DT R T Bank E ((le_max_left _ _).trans hn) hPath hSeed hPhysJ h3 h4 hPhys
      hD hR hT hBank hE hDT hRDT hBankDis hEDis hSupply hMode
      κi ι ν bad loc full w hCombined hLoc hFull hw
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
  exact ⟨P₀,DR,Q,Rtail,Ps,Y,hPQ,⟨hP₀,hAllow,hSparse,hQuota⟩,hD,hDR,hDtail,hEq,hQ,hQR,hRes,hPhysRes,
    hR,hRL,hDq,hDcap,hRd,hMove,hPY,hPs,hYin,hYdeg,hYphys,
    ⟨x,hx,hCharge⟩,d,q,hLoad,hLocOut,hFullOut,hLocY,hFullY⟩

#print axioms g34_native_partition_result_on_fixed_prepared_window_with_triangle_monitors

end TypedTriangle.Vortex
