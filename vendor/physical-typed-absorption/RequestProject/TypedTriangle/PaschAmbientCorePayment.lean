module
public import RequestProject.TypedTriangle.PaschAmbientH3Envelope
public import RequestProject.TypedTriangle.PaschAmbientCellModes
public import RequestProject.TypedTriangle.PaschSelectorUniverse
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace TypedTriangle.Pasch
open SelSimul SelBridge CorePayment
variable {V I Ambient : Type*} [Fintype V] [Fintype Ambient]

/-- The decomposition represented by the indexed selector packing itself. -/
theorem rooted_packing_decomposition {H : Host V I} {F : Set (Multiset I)}
    (D : Finset (V×Sym2 V))
    (hD : (D : Set (V×Sym2 V)).PairwiseDisjoint (fun p => triE p.1 p.2))
    (ht : ∀ p∈D, ∃ x y, p.2=s(x,y) ∧ IsAllowed H F {p.1,x,y}) :
    IsDecomposition H F (packEdges D)
      (D.image (fun p => selectorTriangle p.1 p.2)) := by
  have hEq : ∀ p∈D, triEdges (selectorTriangle p.1 p.2)=triE p.1 p.2 := by
    intro p hp
    obtain ⟨x,y,he,hT⟩ := ht p hp
    rw [he]
    simpa only [selectorTriangle,Sym2.toFinset_mk_eq] using (Envelope.triE_eq_triEdges hT).symm
  refine ⟨?_,?_,?_⟩
  · intro T hT
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hT
    obtain ⟨x,y,he,hT⟩ := ht p hp
    simpa only [selectorTriangle,he,Sym2.toFinset_mk_eq] using hT
  · intro T hT U hU hne
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hT
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hU
    change Disjoint (triEdges (selectorTriangle p.1 p.2)) (triEdges (selectorTriangle q.1 q.2))
    rw [hEq p hp,hEq q hq]
    exact hD hp hq (fun he => hne (congrArg (fun p => selectorTriangle p.1 p.2) he))
  · ext e
    simp only [mem_biUnion,mem_image,packEdges]
    constructor
    · rintro ⟨T,⟨p,hp,rfl⟩,he⟩
      exact ⟨p,hp,(hEq p hp) ▸ he⟩
    · rintro ⟨p,hp,he⟩
      exact ⟨selectorTriangle p.1 p.2,⟨p,hp,rfl⟩,(hEq p hp).symm ▸ he⟩

/-- The actual H3 payment on the surviving core, with both literal
subdecompositions retained. Only the H3 pool of the core is charged. -/
theorem basal_payment_inside_core_with_ambient_pasch (ι : V ↪ Ambient)
    {H : Host V I} {F : Set (Multiset I)} {α : ℝ} (hα : 0 < α)
    (Z : Finset V) (hH3 : CommonNbrCond (restrictedHost H Z) F α)
    (E : Finset (Sym2 (Survivors Z))) (R X B : Finset (Sym2 V))
    (DR : Finset (Finset V))
    (hDR : IsDecomposition H F (R\CorePayment.liftEdges Z E) DR)
    {r b q : ℕ} (hq : 0 < q) (hn : 0 < Fintype.card (Survivors Z))
    (hK : CorePayment.liftEdges Z E ⊆ R)
    (hE : ∀ v, edeg E v ≤ r)
    (hprot : ∀ v, edeg (R∪X∪B) v ≤ b)
    (htri : ∀ e∈E, HasTri (restrictedHost H Z) F e)
    (hwin : (E.card : ℝ)/(q : ℝ)+2*((b+3*r+2*q : ℕ) : ℝ) ≤
      (α/2)*Fintype.card (Survivors Z))
    (Rfixed : Finset (Finset Ambient)) (L : ℕ) (hL : PairCodegreeBound Rfixed L) :
    ∃ (W : Finset (Sym2 V)) (DC : Finset (Finset V)),
      Disjoint W (R∪X∪B) ∧
      (∀ e∈W, ∀ v∈e, v∉Z) ∧
      IsDecomposition H F (CorePayment.liftEdges Z E∪W) DC ∧
      IsDecomposition H F (R∪W) (DR∪DC) ∧
      (∀ v, edeg W v ≤ 2*(r+q)) ∧
      (count (Rfixed∪mapConfiguration ι DC) : ℝ) ≤ count Rfixed+
        2*(E.card : ℝ)*((Fintype.card Ambient : ℝ)/Fintype.card (Survivors Z))*
          ((L+1 : ℕ) : ℝ)^3/α := by
  letI : DecidableEq (Survivors Z) := Classical.decEq _
  let eCore := survivingVertexEmbedding Z
  let eAmbient' : Survivors Z ↪ Ambient := eCore.trans ι
  obtain ⟨W0,D0,hW0,hD0,hDeg,hStat⟩ := envelope_of_H3_with_ambient_pasch
    eAmbient' hα hH3 E (pullEdges Z (R∪X∪B)) hq hn
    (fun v => by simpa only [edeg_eq_classical] using hE v)
    (fun v => by simpa only [edeg_eq_classical] using
      (degree_pull_le Z _ v).trans (hprot v.1)) htri hwin Rfixed L hL
  let W := CorePayment.liftEdges Z W0
  let DC := mapConfiguration eCore D0
  have hAvoid : Disjoint W (R∪X∪B) := disjoint_left.mpr (by
    intro f hf hp
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
    exact disjoint_left.mp hW0 hg (mem_union_right _ (mem_preimage.mpr hp)))
  have hDC := AmbientBank.decomposition_lift (restrictedHost H Z) H F eCore
    (fun _ _ h => h) (fun _ => rfl) hD0
  have hLiftEq : AmbientBank.liftEdges eCore (E∪W0)=CorePayment.liftEdges Z E∪W := by
    simp only [AmbientBank.liftEdges,CorePayment.liftEdges,W,map_eq_image,image_union]
    rfl
  rw [hLiftEq] at hDC
  have hDis : Disjoint (R\CorePayment.liftEdges Z E) (CorePayment.liftEdges Z E∪W) := by
    apply disjoint_left.mpr
    intro f hf hg
    rcases mem_union.mp hg with hg | hg
    · exact (mem_sdiff.mp hf).2 hg
    · exact disjoint_left.mp hAvoid hg (mem_union_left _ (mem_union_left _ (mem_sdiff.mp hf).1))
  have hUnion := hDR.union hDC hDis
  have hSet : (R\CorePayment.liftEdges Z E)∪(CorePayment.liftEdges Z E∪W)=R∪W := by
    ext f
    have hh : f∈CorePayment.liftEdges Z E → f∈R := fun hf => hK hf
    simp only [mem_union,mem_sdiff]
    tauto
  rw [hSet] at hUnion
  have hMap : mapConfiguration ι DC=mapConfiguration eAmbient' D0 := by
    unfold DC eAmbient' mapConfiguration
    rw [Finset.map_map]
    congr 1
    apply Function.Embedding.ext
    intro T
    change (T.map eCore).map ι=T.map (eCore.trans ι)
    exact Finset.map_map _ _ _
  refine ⟨W,DC,hAvoid,CorePayment.liftEdges_avoids Z W0,hDC,hUnion,?_,?_⟩
  · exact degree_lift_le Z W0 (fun v => by simpa only [edeg_eq_classical] using hDeg v)
  · rw [hMap]
    exact hStat
end TypedTriangle.Pasch
#print axioms TypedTriangle.Pasch.rooted_packing_decomposition
#print axioms TypedTriangle.Pasch.basal_payment_inside_core_with_ambient_pasch
