/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.BasalEnvelope
public import RequestProject.TypedTriangle.VertexZeroExtension
@[expose] public section

/-! Pay the basal empty mode INSIDE a prescribed core. The deleted root set Z
may be large: its cardinality never enters the resource window. The input is
genuine geometry and permitted thirds on the core, not a basal-payment provider.
Constructing the common core and placing all preceding selectors there are
separate obligations. -/

open Finset Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TypedTriangle.CorePayment
open SelSimul
variable {V I : Type*} [Fintype V]

lemma edeg_eq_classical {β : Type*} (d : DecidableEq β)
    (E : Finset (Sym2 β)) (v : β) :
    @edeg β d E v = @edeg β (Classical.decEq β) E v := by
  have hd : d = Classical.decEq β := Subsingleton.elim _ _
  cases hd
  rfl

def edgeLift (Z : Finset V) : Sym2 (Survivors Z) → Sym2 V := Sym2.map Subtype.val

lemma edgeLift_injective (Z : Finset V) : Function.Injective (edgeLift Z) :=
  Sym2.map.injective Subtype.val_injective

def liftEdges (Z : Finset V) (E : Finset (Sym2 (Survivors Z))) : Finset (Sym2 V) :=
  E.image (edgeLift Z)

def pullEdges (Z : Finset V) (B : Finset (Sym2 V)) : Finset (Sym2 (Survivors Z)) :=
  B.preimage (edgeLift Z) (edgeLift_injective Z).injOn

lemma mem_edgeLift (Z : Finset V) (e : Sym2 (Survivors Z)) (v : Survivors Z) :
    v.1 ∈ edgeLift Z e ↔ v ∈ e := by
  constructor
  · intro hv
    obtain ⟨w,hw,heq⟩ := Sym2.mem_map.mp hv
    exact (Subtype.ext heq : w = v) ▸ hw
  · intro hv
    exact Sym2.mem_map.mpr ⟨v,hv,rfl⟩

lemma liftEdges_avoids (Z : Finset V) (E : Finset (Sym2 (Survivors Z))) :
    ∀ e ∈ liftEdges Z E, ∀ v ∈ e, v ∉ Z := by
  intro e he v hv
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
  exact w.2

lemma triEdges_lift (Z : Finset V) (T : Finset (Survivors Z)) :
    triEdges (liftVertexSet Z T) = liftEdges Z (triEdges T) := by
  ext e
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hx,hy,hxy⟩ := mem_triEdges.mp he
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
      exact mem_image.mpr ⟨s(u,v),mem_triEdges.mpr ⟨hu,hv,fun h => hxy (congrArg Subtype.val h)⟩,rfl⟩
  · intro he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact (mem_triEdges_liftVertexSet Z T f).mpr hf

lemma basal_lift {H : Host V I} {F : Set (Multiset I)} (Z : Finset V)
    {E : Finset (Sym2 (Survivors Z))} (hE : Basal (restrictedHost H Z) F E) :
    Basal H F (liftEdges Z E) := by
  letI : DecidableEq (Survivors Z) := Classical.decEq _
  obtain ⟨D,hD⟩ := hE
  refine ⟨D.image (liftVertexSet Z),?_,?_,?_⟩
  · intro T hT
    obtain ⟨U,hU,rfl⟩ := mem_image.mp hT
    exact isAllowed_mono (vertexDeleted_le H Z) rfl
      ((isAllowed_liftVertexSet_iff H F Z U).mp (hD.1 U hU))
  · intro T hT U hU hne
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hT
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hU
    change Disjoint (triEdges (liftVertexSet Z A)) (triEdges (liftVertexSet Z B))
    rw [triEdges_lift,triEdges_lift]
    apply disjoint_left.mpr
    intro e heA heB
    obtain ⟨a,ha,hae⟩ := mem_image.mp heA
    obtain ⟨b,hb,hbe⟩ := mem_image.mp heB
    have hab : a = b := edgeLift_injective Z (hae.trans hbe.symm)
    exact disjoint_left.mp (hD.2.1 hA hB (fun h => hne (congrArg (liftVertexSet Z) h))) ha (hab ▸ hb)
  · ext e
    simp only [liftEdges,mem_biUnion,mem_image]
    constructor
    · rintro ⟨T,⟨U,hU,rfl⟩,he⟩
      rw [triEdges_lift] at he
      obtain ⟨f,hf,hfe⟩ := mem_image.mp he
      refine ⟨f,?_,hfe⟩
      rw [← hD.2.2]
      exact mem_biUnion.mpr ⟨U,hU,hf⟩
    · rintro ⟨f,hf,hfe⟩
      rw [← hD.2.2] at hf
      obtain ⟨T,hT,hfT⟩ := mem_biUnion.mp hf
      refine ⟨liftVertexSet Z T,⟨T,hT,rfl⟩,?_⟩
      rw [triEdges_lift]
      exact mem_image.mpr ⟨f,hfT,hfe⟩

lemma degree_pull_le (Z : Finset V) (B : Finset (Sym2 V)) (v : Survivors Z) :
    edeg (pullEdges Z B) v ≤ edeg B v.1 := by
  apply card_le_card_of_injOn (edgeLift Z)
  · intro e he
    obtain ⟨heB,hve⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_preimage.mp heB,(mem_edgeLift Z e v).mpr hve⟩
  · exact (edgeLift_injective Z).injOn

lemma degree_lift_le (Z : Finset V) (E : Finset (Sym2 (Survivors Z)))
    {d : ℕ} (hE : ∀ v, edeg E v ≤ d) : ∀ v, edeg (liftEdges Z E) v ≤ d := by
  intro v
  by_cases hv : v ∈ Z
  · have he : (liftEdges Z E).filter (fun e => v ∈ e) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro e he hve
      exact liftEdges_avoids Z E e he v hve hv
    simp [edeg,he]
  · let v' : Survivors Z := ⟨v,hv⟩
    have he : (liftEdges Z E).filter (fun e => v ∈ e) =
        (E.filter (fun e => v' ∈ e)).image (edgeLift Z) := by
      ext e
      simp only [liftEdges,mem_filter,mem_image]
      constructor
      · rintro ⟨⟨f,hf,rfl⟩,hve⟩
        exact ⟨f,⟨hf,(mem_edgeLift Z f v').mp hve⟩,rfl⟩
      · rintro ⟨f,⟨hf,hvf⟩,rfl⟩
        exact ⟨⟨f,hf,rfl⟩,(mem_edgeLift Z f v').mpr hvf⟩
    change ((liftEdges Z E).filter (fun e => v ∈ e)).card ≤ d
    rw [he]
    exact card_image_le.trans (hE v')

/-- Construct the empty-mode payment on the actual core and lift it without
paying |Z|. Roots can occupy almost the whole ambient host. -/
theorem basal_payment_inside_core {H : Host V I} {F : Set (Multiset I)} {α : ℝ}
    (Z : Finset V) (hH3 : CommonNbrCond (restrictedHost H Z) F α)
    (E : Finset (Sym2 (Survivors Z))) (R X B : Finset (Sym2 V))
    {r b q : ℕ} (hq : 0 < q) (hK : liftEdges Z E ⊆ R)
    (hR : Basal H F (R \ liftEdges Z E))
    (hE : ∀ v, edeg E v ≤ r) (hprot : ∀ v, edeg (R ∪ X ∪ B) v ≤ b)
    (htri : ∀ e ∈ E, HasTri (restrictedHost H Z) F e)
    (hwin : ((E.card/q + 2*(b+3*r+2*q) : ℕ) : ℝ) <
      α * Fintype.card (Survivors Z)) :
    ∃ W : Finset (Sym2 V), Disjoint W (R ∪ X ∪ B) ∧
      (∀ e ∈ W, ∀ v ∈ e, v ∉ Z) ∧ Basal H F (R ∪ W) ∧
      Basal H F (liftEdges Z E ∪ W) ∧ ∀ v, edeg W v ≤ 2*(r+q) := by
  letI : DecidableEq (Survivors Z) := Classical.decEq _
  obtain ⟨W,hW,hKW,hdeg⟩ := Envelope.envelope_of_H3 hH3 E
    (pullEdges Z (R ∪ X ∪ B)) ∅ (r := r) (b := b) hq
    (fun v => by simpa only [edeg_eq_classical] using hE v)
    (fun v => by simpa only [edeg_eq_classical] using
      (degree_pull_le Z _ v).trans (hprot v.1)) htri
    (by simpa only [card_empty,zero_add] using hwin)
  have hd : Disjoint (liftEdges Z W) (R ∪ X ∪ B) := by
    apply disjoint_left.mpr
    intro e he hp
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    exact disjoint_left.mp hW hf (mem_union_right _ (mem_preimage.mpr hp))
  have hbas : Basal H F (liftEdges Z E ∪ liftEdges Z W) := by
    have hh := basal_lift Z hKW
    simpa only [liftEdges,image_union] using hh
  refine ⟨liftEdges Z W,hd,liftEdges_avoids Z W,?_,hbas,degree_lift_le Z W ?_⟩
  swap
  · intro v
    simpa only [edeg_eq_classical] using hdeg v
  exact Envelope.pay_empty_mode hK hR hbas
    (hd.mono_right (fun e he => mem_union_left _ (mem_union_left _ he)))

end TypedTriangle.CorePayment
