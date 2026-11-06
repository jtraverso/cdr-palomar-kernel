/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SampledForbiddenTransport
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-! A decomposition of the induced host on a sampled core remains a genuine
triangle decomposition after its edges and blocks are lifted to the ambient
host. No ambient physicality assumption is used. -/

open Finset Classical
noncomputable section

namespace TypedTriangle.SampledResource

variable {V I : Type} [Fintype V]

def vertexEmb (W : Finset V) : {x // x ∈ W} ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

def liftVertices (W : Finset V) (T : Finset {x // x ∈ W}) : Finset V :=
  T.map (vertexEmb W)

lemma allowed_lift (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    (T : Finset {x // x ∈ W})
    (hT : IsAllowed (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ :
      Host {x // x ∈ W} I) F T) :
    IsAllowed H F (liftVertices W T) := by
  obtain ⟨hcard,hadj,htype⟩ := hT
  refine ⟨?_,?_,?_⟩
  · simpa only [liftVertices,Finset.card_map] using hcard
  · intro x hx y hy hxy
    obtain ⟨x',hx',rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y',hy',rfl⟩ := Finset.mem_map.mp hy
    exact hadj x' hx' y' hy' (fun he => hxy (congrArg Subtype.val he))
  · change (T.map (vertexEmb W)).val.map H.lab ∈ F
    rw [Finset.map_val,Multiset.map_map]
    change T.val.map (H.lab ∘ Subtype.val) ∈ F
    exact htype

lemma triEdges_lift (W : Finset V) (T : Finset {x // x ∈ W}) :
    triEdges (liftVertices W T) = lift W (triEdges T) := by
  ext e
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hx,hy,hxy⟩ := mem_triEdges.mp he
      obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hy
      exact Finset.mem_image.mpr ⟨s(u,v),
        mem_triEdges.mpr ⟨hu,hv,fun h => hxy (congrArg Subtype.val h)⟩,rfl⟩
  · intro he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    induction f using Sym2.ind with
    | _ u v =>
      obtain ⟨hu,hv,huv⟩ := mem_triEdges.mp hf
      exact mem_triEdges.mpr ⟨Finset.mem_map.mpr ⟨u,hu,rfl⟩,
        Finset.mem_map.mpr ⟨v,hv,rfl⟩,
        fun h => huv (Subtype.val_injective (by simpa only using h))⟩

theorem basal_lift (H : Host V I) (F : Set (Multiset I)) (W : Finset V)
    {E : Finset (Sym2 {x // x ∈ W})}
    (hE : Basal (⟨H.G.comap Subtype.val,H.lab ∘ Subtype.val⟩ :
      Host {x // x ∈ W} I) F E) :
    Basal H F (lift W E) := by
  letI : DecidableEq {x // x ∈ W} := Classical.decEq _
  obtain ⟨D,hD⟩ := hE
  refine ⟨D.image (liftVertices W),?_,?_,?_⟩
  · intro T hT
    obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hT
    exact allowed_lift H F W U (hD.1 U hU)
  · intro T hT U hU hne
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hU
    change Disjoint (triEdges (liftVertices W A)) (triEdges (liftVertices W B))
    rw [triEdges_lift,triEdges_lift]
    apply Finset.disjoint_left.mpr
    intro e heA heB
    obtain ⟨a,ha,hae⟩ := Finset.mem_image.mp heA
    obtain ⟨b,hb,hbe⟩ := Finset.mem_image.mp heB
    have hab : a = b := edgeLift_injective W (hae.trans hbe.symm)
    exact Finset.disjoint_left.mp
      (hD.2.1 hA hB (fun h => hne (congrArg (liftVertices W) h))) ha (hab ▸ hb)
  · ext e
    simp only [lift,Finset.mem_biUnion,Finset.mem_image]
    constructor
    · rintro ⟨T,⟨U,hU,rfl⟩,he⟩
      rw [triEdges_lift] at he
      obtain ⟨f,hf,hfe⟩ := Finset.mem_image.mp he
      refine ⟨f,?_,hfe⟩
      rw [← hD.2.2]
      exact Finset.mem_biUnion.mpr ⟨U,hU,hf⟩
    · rintro ⟨f,hf,hfe⟩
      rw [← hD.2.2] at hf
      obtain ⟨T,hT,hfT⟩ := Finset.mem_biUnion.mp hf
      refine ⟨liftVertices W T,⟨T,hT,rfl⟩,?_⟩
      rw [triEdges_lift]
      exact Finset.mem_image.mpr ⟨f,hfT,hfe⟩

#print axioms basal_lift

end TypedTriangle.SampledResource
