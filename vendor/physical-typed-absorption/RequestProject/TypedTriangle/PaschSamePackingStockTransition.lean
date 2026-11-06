module
public import RequestProject.TypedTriangle.PaschAmbientStockPayment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
variable {V I Ambient : Type*} [Fintype V] [Fintype Ambient]

/-- Glue for an already constructed packing and an already constructed
literal withdrawal mode. No packing producer is called here. -/
theorem same_packing_ambient_stock_transition (ι : V ↪ Ambient)
    (H : Host V I) (F : Set (Multiset I)) (D P0 : Finset (Finset V))
    (hP0 : IsPacking H F P0) (R Rtail J : Finset (Sym2 V))
    (hJ : J=edges H\(Rtail∪P0.biUnion triEdges))
    (hP0tail : Disjoint (P0.biUnion triEdges) Rtail)
    (hStockJ : BasalIncidence.cover D⊆J) (hPhysJ : IsPhysical H F J)
    (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η)
    (hSupply : ∀ u v, s(u,v)∈J\BasalIncidence.cover D → H.G.Adj u v →
      κ*Fintype.card V≤(BasalIncidence.good H F D u v).card)
    (d : ℕ) (hDeg : ∀ v, ((J\BasalIncidence.cover D).filter (fun e => v∈e)).card≤d)
    (hOrder : StockEntry.Explicit.coverDownOrder κ η≤Fintype.card V)
    (hCard : (J\BasalIncidence.cover D).card≤Fintype.card V*d)
    (hSparse : (d : ℝ)≤StockEntry.Explicit.coverDownBudget κ η*Fintype.card V)
    (U : Finset (Finset V)) (W : Finset V) (τ : ℝ)
    (hMode : ∀ L : Finset (Sym2 V), L⊆BasalIncidence.cover D → IsPhysical H F L →
      ∃ (Ps Y : Finset (Sym2 V)) (Dps : Finset (Finset V)),
        R∪L=Ps∪Y ∧ Disjoint Ps Y ∧ IsDecomposition H F Ps Dps ∧ Dps⊆U ∧
        (∀ e∈Y, ∀ v∈e, v∈W) ∧ (∀ v, (SelSimul.edeg Y v : ℝ)≤τ*Fintype.card V) ∧
        IsPhysical H F Y)
    (Rfixed : Finset (Finset Ambient)) (Lfixed : ℕ)
    (hFixed : PairCodegreeBound Rfixed Lfixed)
    (hP0fixed : mapConfiguration ι P0⊆Rfixed) (hUfixed : mapConfiguration ι U⊆Rfixed) :
    ∃ (C : Finset (Finset V)) (Ps Y : Finset (Sym2 V)) (Dps : Finset (Finset V)),
      IsPacking H F C ∧ IsPacking H F (P0∪C) ∧
      Disjoint ((P0∪C).biUnion triEdges) Rtail ∧
      (edges H\(Rtail∪(P0∪C).biUnion triEdges))⊆BasalIncidence.cover D ∧
      IsPhysical H F (edges H\(Rtail∪(P0∪C).biUnion triEdges)) ∧
      R∪(edges H\(Rtail∪(P0∪C).biUnion triEdges))=Ps∪Y ∧
      Disjoint Ps Y ∧ IsDecomposition H F Ps Dps ∧ Dps⊆U ∧
      (∀ e∈Y, ∀ v∈e, v∈W) ∧ (∀ v, (SelSimul.edeg Y v : ℝ)≤τ*Fintype.card V) ∧
      IsPhysical H F Y ∧ C.biUnion triEdges⊆J ∧
      (∀ v, (((C.biUnion triEdges).filter (fun e => v∈e)).card : ℝ)≤η*Fintype.card V) ∧
      (count (Rfixed∪mapConfiguration ι ((P0∪C)∪Dps)) : ℝ)≤count Rfixed+
        2*((J\BasalIncidence.cover D).card : ℝ)*
          ((Fintype.card Ambient : ℝ)/Fintype.card V)*((Lfixed+1 : ℕ) : ℝ)^3/κ := by
  have hJH : J⊆edges H := by rw [hJ]; exact sdiff_subset
  have hProtected : Disjoint (P0.biUnion triEdges) J := by
    rw [hJ]
    apply disjoint_left.mpr
    intro e he hRest
    exact (mem_sdiff.mp hRest).2 (mem_union_right _ he)
  obtain ⟨C,hC,hQ,hCJ,hLeft,hLeftPhys,hCdeg,hCost⟩ :=
    StockEntry.enter_stock_native_with_ambient_fixed_universe_pasch ι hκ hη hP0
      Rfixed hP0fixed Lfixed hFixed J hJH hStockJ hProtected hPhysJ hSupply
      hDeg hOrder hCard hSparse
  obtain ⟨Ps,Y,Dps,hMove,hDis,hDps,hDpsU,hInside,hYdeg,hYphys⟩ :=
    hMode (J\C.biUnion triEdges) hLeft hLeftPhys
  have hRemainder : edges H\(Rtail∪(P0∪C).biUnion triEdges)=J\C.biUnion triEdges := by
    rw [hJ,union_biUnion]
    ext e
    simp only [mem_sdiff,mem_union]
    tauto
  have hQtail : Disjoint ((P0∪C).biUnion triEdges) Rtail := by
    rw [union_biUnion]
    apply disjoint_union_left.mpr
    refine ⟨hP0tail,disjoint_left.mpr ?_⟩
    intro e he ht
    have hh := hCJ he
    rw [hJ] at hh
    exact (mem_sdiff.mp hh).2 (mem_union_left _ ht)
  have hDpsFixed : mapConfiguration ι Dps⊆Rfixed := by
    intro Q hQ
    obtain ⟨T,hT,rfl⟩ := mem_mapConfiguration.mp hQ
    exact hUfixed (mem_mapConfiguration.mpr ⟨T,hDpsU hT,rfl⟩)
  have hFixedEq : Rfixed∪mapConfiguration ι ((P0∪C)∪Dps)=Rfixed∪mapConfiguration ι C := by
    unfold mapConfiguration
    rw [map_union,map_union]
    ext Q
    have hp : Q∈mapConfiguration ι P0 → Q∈Rfixed := fun h => hP0fixed h
    have hd : Q∈mapConfiguration ι Dps → Q∈Rfixed := fun h => hDpsFixed h
    simp only [mem_union]
    change (Q∈Rfixed ∨ (Q∈mapConfiguration ι P0 ∨ Q∈mapConfiguration ι C) ∨
      Q∈mapConfiguration ι Dps) ↔ _
    tauto
  refine ⟨C,Ps,Y,Dps,hC,hQ,hQtail,?_,?_,?_,hDis,hDps,hDpsU,hInside,hYdeg,hYphys,hCJ,hCdeg,?_⟩
  · rw [hRemainder]
    exact hLeft
  · rw [hRemainder]
    exact hLeftPhys
  · rw [hRemainder]
    exact hMove
  · rw [hFixedEq]
    exact hCost
end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.same_packing_ambient_stock_transition
