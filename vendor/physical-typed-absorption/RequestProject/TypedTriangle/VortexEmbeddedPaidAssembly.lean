/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.CoreBasalPayment
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section
open Finset Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace TypedTriangle.Vortex

/-- Edge transport through an injective vertex map, including nested val maps. -/
def embeddedEdges {V W : Type} (ι : V ↪ W) (E : Finset (Sym2 V)) : Finset (Sym2 W) :=
  E.image (Sym2.map ι)

private theorem allowed_embedding {V W I : Type} [Fintype V] [Fintype W]
    (J : Host V I) (H : Host W I) (F : Set (Multiset I)) (ι : V ↪ W)
    (hAdj : ∀ u v, J.G.Adj u v → H.G.Adj (ι u) (ι v))
    (hLab : ∀ u, J.lab u = H.lab (ι u)) (T : Finset V) (hT : IsAllowed J F T) :
    IsAllowed H F (T.map ι) := by
  refine ⟨by simpa only [card_map] using hT.1, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
    exact hAdj u v (hT.2.1 u hu v hv (fun he => hxy (congrArg ι he)))
  · change (T.map ι).val.map H.lab ∈ F
    rw [Finset.map_val, Multiset.map_map]
    have hL : H.lab ∘ ι = J.lab := funext (fun u => (hLab u).symm)
    change T.val.map (H.lab ∘ ι) ∈ F
    rw [hL]
    exact hT.2.2

theorem triEdges_embedding {V W : Type} (ι : V ↪ W) (T : Finset V) :
    triEdges (T.map ι) = embeddedEdges ι (triEdges T) := by
  ext e
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hx,hy,hxy⟩ := mem_triEdges.mp he
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
      exact mem_image.mpr ⟨s(u,v), mem_triEdges.mpr
        ⟨hu,hv,fun h => hxy (congrArg ι h)⟩, rfl⟩
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    induction f using Sym2.ind with
    | _ u v =>
      obtain ⟨hu,hv,huv⟩ := mem_triEdges.mp hf
      exact mem_triEdges.mpr ⟨mem_map.mpr ⟨u,hu,rfl⟩,mem_map.mpr ⟨v,hv,rfl⟩,
        fun h => huv (ι.injective (by simpa only using h))⟩

theorem basal_embedding {V W I : Type} [Fintype V] [Fintype W]
    (J : Host V I) (H : Host W I) (F : Set (Multiset I)) (ι : V ↪ W)
    (hAdj : ∀ u v, J.G.Adj u v → H.G.Adj (ι u) (ι v))
    (hLab : ∀ u, J.lab u = H.lab (ι u)) {E : Finset (Sym2 V)}
    (hE : Basal J F E) : Basal H F (embeddedEdges ι E) := by
  obtain ⟨D,hD⟩ := hE
  refine ⟨D.image (fun T => T.map ι), ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨U,hU,rfl⟩ := mem_image.mp hT
    exact allowed_embedding J H F ι hAdj hLab U (hD.1 U hU)
  · intro T hT U hU hne
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hT
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hU
    change Disjoint (triEdges (A.map ι)) (triEdges (B.map ι))
    rw [triEdges_embedding,triEdges_embedding]
    apply disjoint_left.mpr
    intro e heA heB
    obtain ⟨a,ha,hae⟩ := mem_image.mp heA
    obtain ⟨b,hb,hbe⟩ := mem_image.mp heB
    have hab : a = b := (Sym2.map.injective ι.injective) (hae.trans hbe.symm)
    exact disjoint_left.mp (hD.2.1 hA hB (fun h => hne (congrArg (fun T => T.map ι) h)))
      ha (hab ▸ hb)
  · ext e
    simp only [embeddedEdges,mem_biUnion,mem_image]
    constructor
    · rintro ⟨T,⟨U,hU,rfl⟩,he⟩
      rw [triEdges_embedding] at he
      obtain ⟨f,hf,hfe⟩ := mem_image.mp he
      refine ⟨f,?_,hfe⟩
      rw [← hD.2.2]
      exact mem_biUnion.mpr ⟨U,hU,hf⟩
    · rintro ⟨f,hf,hfe⟩
      rw [← hD.2.2] at hf
      obtain ⟨T,hT,hfT⟩ := mem_biUnion.mp hf
      refine ⟨T.map ι,⟨T,hT,rfl⟩,?_⟩
      rw [triEdges_embedding]
      exact mem_image.mpr ⟨f,hfT,hfe⟩

/-- One exact splice across different vertex types. Physicality of the final
remainder is obtained in the parent host by subtracting the basal packing. -/
theorem assemble_embedded_paid_layer {V W I : Type} [Fintype V] [Fintype W]
    (J : Host V I) (H : Host W I) (F : Set (Multiset I)) (ι : V ↪ W)
    (hAdj : ∀ u v, J.G.Adj u v → H.G.Adj (ι u) (ι v))
    (hLab : ∀ u, J.lab u = H.lab (ι u)) (hH2 : IsPhysical H F (edges H))
    (P : Finset (Sym2 W)) (Ptail Ltail : Finset (Sym2 V)) (U : Finset V)
    (hP : Basal H F P) (hStep : edges H = P ∪ embeddedEdges ι (edges J))
    (hStepDisjoint : Disjoint P (embeddedEdges ι (edges J)))
    (hPtail : Basal J F Ptail) (hTail : edges J = Ptail ∪ Ltail)
    (hTailDisjoint : Disjoint Ptail Ltail)
    (hSupport : ∀ e ∈ Ltail, ∀ v ∈ e, v ∈ U) :
    Basal H F (P ∪ embeddedEdges ι Ptail) ∧
      Disjoint (P ∪ embeddedEdges ι Ptail) (embeddedEdges ι Ltail) ∧
      edges H = (P ∪ embeddedEdges ι Ptail) ∪ embeddedEdges ι Ltail ∧
      IsPhysical H F (embeddedEdges ι Ltail) ∧
      ∀ e ∈ embeddedEdges ι Ltail, ∀ v ∈ e, v ∈ U.map ι := by
  have hPTsub : embeddedEdges ι Ptail ⊆ embeddedEdges ι (edges J) := by
    apply image_subset_image
    rw [hTail]
    exact subset_union_left
  have hLTsub : embeddedEdges ι Ltail ⊆ embeddedEdges ι (edges J) := by
    apply image_subset_image
    rw [hTail]
    exact subset_union_right
  have hTailLiftDisjoint : Disjoint (embeddedEdges ι Ptail) (embeddedEdges ι Ltail) := by
    apply disjoint_left.mpr
    intro e heP heL
    obtain ⟨p,hp,hpe⟩ := mem_image.mp heP
    obtain ⟨l,hl,hle⟩ := mem_image.mp heL
    have heq : p = l := (Sym2.map.injective ι.injective) (hpe.trans hle.symm)
    exact disjoint_left.mp hTailDisjoint hp (heq ▸ hl)
  have hBasal := hP.union (basal_embedding J H F ι hAdj hLab hPtail)
    (hStepDisjoint.mono_right hPTsub)
  have hDisjoint : Disjoint (P ∪ embeddedEdges ι Ptail) (embeddedEdges ι Ltail) :=
    disjoint_union_left.mpr ⟨hStepDisjoint.mono_right hLTsub,hTailLiftDisjoint⟩
  have hPartition : edges H = (P ∪ embeddedEdges ι Ptail) ∪ embeddedEdges ι Ltail := by
    rw [hStep,hTail]
    simp only [embeddedEdges,Finset.image_union]
    exact (union_assoc _ _ _).symm
  have hPsub : P ∪ embeddedEdges ι Ptail ⊆ edges H := by
    rw [hPartition]
    exact subset_union_left
  have hPhysicalP : IsPhysical H F (P ∪ embeddedEdges ι Ptail) := by
    obtain ⟨D,hD⟩ := hBasal
    exact isPhysical_of_isDecomposition hD
  have hRemainder : edges H \ (P ∪ embeddedEdges ι Ptail) = embeddedEdges ι Ltail := by
    rw [hPartition]
    ext e
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨he,hn⟩
      exact he.resolve_left hn
    · intro he
      exact ⟨Or.inr he,fun hp => disjoint_left.mp hDisjoint (mem_union.mpr hp) he⟩
  have hPhysical := isPhysical_sdiff hH2 hPhysicalP hPsub
  rw [hRemainder] at hPhysical
  refine ⟨hBasal,hDisjoint,hPartition,hPhysical,?_⟩
  intro e he v hv
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
  exact mem_map.mpr ⟨w,hSupport f hf w hw,rfl⟩

#print axioms basal_embedding
#print axioms assemble_embedded_paid_layer
end TypedTriangle.Vortex
