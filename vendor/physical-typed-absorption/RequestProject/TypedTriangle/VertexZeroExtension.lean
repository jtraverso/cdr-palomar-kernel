/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.RestrictedHostGeometry

@[expose] public section

/-!
# Zero extension and physical generators across the surviving vertex subtype

Local proof candidate; NOT kernel-checked in this campaign.
No geometric hypothesis is required for the coordinate and lattice transport.
-/

open Finset
noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

abbrev Survivors (Z : Finset V) := {v : V // v ∉ Z}

def survivingVertexEmbedding (Z : Finset V) : Survivors Z ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

def liftVertexSet (Z : Finset V) (T : Finset (Survivors Z)) : Finset V :=
  T.map (survivingVertexEmbedding Z)

lemma liftVertexSet_injective (Z : Finset V) : Function.Injective (liftVertexSet Z) :=
  Finset.map_injective (survivingVertexEmbedding Z)

lemma mem_liftVertexSet (Z : Finset V) (T : Finset (Survivors Z)) (v : Survivors Z) :
    v.1 ∈ liftVertexSet Z T ↔ v ∈ T := by
  constructor
  · intro hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_map.1 hv
    have h : w = v := Subtype.ext heq
    simpa [h] using hw
  · intro hv
    exact Finset.mem_map.2 ⟨v, hv, rfl⟩

lemma liftVertexSet_avoids (Z : Finset V) (T : Finset (Survivors Z)) :
    Disjoint (liftVertexSet Z T) Z := by
  rw [Finset.disjoint_left]
  intro v hv hvZ
  obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hv
  exact w.2 hvZ

lemma card_liftVertexSet (Z : Finset V) (T : Finset (Survivors Z)) :
    (liftVertexSet Z T).card = T.card := by simp [liftVertexSet]

lemma subtype_liftVertexSet (Z : Finset V) (T : Finset (Survivors Z)) :
    (liftVertexSet Z T).subtype (fun v => v ∉ Z) = T := by
  ext v
  rw [Finset.mem_subtype, mem_liftVertexSet]

lemma lift_subtypeVertexSet (Z T : Finset V) (hd : Disjoint T Z) :
    liftVertexSet Z (T.subtype (fun v => v ∉ Z)) = T := by
  exact Finset.subtype_map_of_mem (fun v hv hz => Finset.disjoint_left.1 hd hv hz)

lemma labels_liftVertexSet (H : Host V I) (Z : Finset V) (T : Finset (Survivors Z)) :
    (liftVertexSet Z T).val.map H.lab = T.val.map (restrictedHost H Z).lab := by
  simp only [liftVertexSet, Finset.map_val, Multiset.map_map]
  rfl

lemma isAllowed_liftVertexSet_iff (H : Host V I) (F : Set (Multiset I))
    (Z : Finset V) (T : Finset (Survivors Z)) :
    IsAllowed (restrictedHost H Z) F T ↔
      IsAllowed (vertexDeleted H Z) F (liftVertexSet Z T) := by
  constructor
  · intro hT
    apply (isAllowed_vertexDeleted_iff H F Z (liftVertexSet Z T)).2
    refine ⟨⟨?_, ?_, ?_⟩, liftVertexSet_avoids Z T⟩
    · rw [card_liftVertexSet]
      exact hT.1
    · intro u hu v hv huv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hv
      exact hT.2.1 a ha b hb (fun heq => huv (congrArg Subtype.val heq))
    · rw [labels_liftVertexSet]
      exact hT.2.2
  · intro hT
    have hfull := isAllowed_mono (vertexDeleted_le H Z) rfl hT
    refine ⟨?_, ?_, ?_⟩
    · rw [← card_liftVertexSet Z T]
      exact hfull.1
    · intro u hu v hv huv
      exact hfull.2.1 u.1 ((mem_liftVertexSet Z T u).2 hu)
        v.1 ((mem_liftVertexSet Z T v).2 hv) (fun heq => huv (Subtype.ext heq))
    · rw [← labels_liftVertexSet H Z T]
      exact hfull.2.2

lemma isAllowed_subtypeVertexSet (H : Host V I) (F : Set (Multiset I))
    (Z T : Finset V) (hT : IsAllowed (vertexDeleted H Z) F T) :
    IsAllowed (restrictedHost H Z) F (T.subtype (fun v => v ∉ Z)) := by
  apply (isAllowed_liftVertexSet_iff H F Z _).2
  rw [lift_subtypeVertexSet Z T ((isAllowed_vertexDeleted_iff H F Z T).1 hT).2]
  exact hT

/-- Restrict edge coordinates to pairs of surviving vertices. -/
def edgeRestrict (Z : Finset V) : (Sym2 V → ℤ) →ₗ[ℤ] (Sym2 (Survivors Z) → ℤ) where
  toFun x e := x (Sym2.map Subtype.val e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extend by zero, using the canonical attached subtype edge on surviving pairs. -/
def edgeZeroExtend (Z : Finset V) : (Sym2 (Survivors Z) → ℤ) →ₗ[ℤ] (Sym2 V → ℤ) where
  toFun x e := if h : ∀ v ∈ e, v ∉ Z then x (e.attachWith h) else 0
  map_add' x y := by
    funext e
    simp only [Pi.add_apply]
    split_ifs <;> simp_all
  map_smul' k x := by
    funext e
    by_cases h : ∀ v ∈ e, v ∉ Z <;> simp [h]

lemma edgeZeroExtend_apply_map (Z : Finset V) (x : Sym2 (Survivors Z) → ℤ)
    (e : Sym2 (Survivors Z)) :
    edgeZeroExtend Z x (Sym2.map Subtype.val e) = x e := by
  have hav : ∀ v ∈ Sym2.map Subtype.val e, v ∉ Z := by
    intro v hv
    obtain ⟨w, -, rfl⟩ := Sym2.mem_map.1 hv
    exact w.2
  change (if h : ∀ v ∈ Sym2.map Subtype.val e, v ∉ Z then
    x ((Sym2.map Subtype.val e).attachWith h) else 0) = x e
  rw [dif_pos hav]
  congr 1
  apply Sym2.map.injective Subtype.val_injective
  exact Sym2.attachWith_map_subtypeVal hav

lemma edgeRestrict_zeroExtend (Z : Finset V) (x : Sym2 (Survivors Z) → ℤ) :
    edgeRestrict Z (edgeZeroExtend Z x) = x := by
  funext e
  exact edgeZeroExtend_apply_map Z x e

lemma edgeZeroExtend_vanish (Z : Finset V) (x : Sym2 (Survivors Z) → ℤ) :
    ∀ e, TouchZ Z e → edgeZeroExtend Z x e = 0 := by
  intro e he
  obtain ⟨v, hv, hve⟩ := he
  have hav : ¬ ∀ w ∈ e, w ∉ Z := fun h => h v hve hv
  change (if h : ∀ w ∈ e, w ∉ Z then x (e.attachWith h) else 0) = 0
  rw [dif_neg hav]

lemma edgeZeroExtend_restrict (Z : Finset V) (x : Sym2 V → ℤ)
    (hx : ∀ e, TouchZ Z e → x e = 0) : edgeZeroExtend Z (edgeRestrict Z x) = x := by
  funext e
  change (if h : ∀ v ∈ e, v ∉ Z then x (Sym2.map Subtype.val (e.attachWith h)) else 0) = x e
  by_cases h : ∀ v ∈ e, v ∉ Z
  · rw [dif_pos h, Sym2.attachWith_map_subtypeVal]
  · rw [dif_neg h]
    push_neg at h
    obtain ⟨v, hve, hv⟩ := h
    exact (hx e ⟨v, hv, hve⟩).symm

lemma edgeZeroExtend_injective (Z : Finset V) : Function.Injective (edgeZeroExtend Z) := by
  intro x y hxy
  have h := congrArg (edgeRestrict Z) hxy
  simpa only [edgeRestrict_zeroExtend] using h

lemma mem_triEdges_liftVertexSet (Z : Finset V) (T : Finset (Survivors Z))
    (e : Sym2 (Survivors Z)) :
    Sym2.map Subtype.val e ∈ triEdges (liftVertexSet Z T) ↔ e ∈ triEdges T := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [Sym2.map_mk, mem_triEdges, mem_liftVertexSet]
    constructor
    · rintro ⟨hu, hv, huv⟩
      exact ⟨hu, hv, fun heq => huv (congrArg Subtype.val heq)⟩
    · rintro ⟨hu, hv, huv⟩
      exact ⟨hu, hv, fun heq => huv (Subtype.ext heq)⟩

lemma edgeRestrict_triangle_boundary (Z : Finset V) (T : Finset (Survivors Z)) :
    edgeRestrict Z (ind (triEdges (liftVertexSet Z T))) = ind (triEdges T) := by
  funext e
  change (if Sym2.map Subtype.val e ∈ triEdges (liftVertexSet Z T) then (1 : ℤ) else 0) = _
  simp only [mem_triEdges_liftVertexSet, ind]
  split_ifs <;> rfl

lemma triangle_boundary_lift_vanish (Z : Finset V) (T : Finset (Survivors Z)) :
    ∀ e, TouchZ Z e → ind (triEdges (liftVertexSet Z T)) e = 0 := by
  intro e he
  obtain ⟨v, hvZ, hve⟩ := he
  apply if_neg
  intro heT
  have hvT : v ∈ liftVertexSet Z T :=
    Finset.mem_sym2_iff.1 (Finset.mem_filter.1 heT).1 v hve
  exact Finset.disjoint_left.1 (liftVertexSet_avoids Z T) hvT hvZ

lemma edgeZeroExtend_triangle_boundary (Z : Finset V) (T : Finset (Survivors Z)) :
    edgeZeroExtend Z (ind (triEdges T)) = ind (triEdges (liftVertexSet Z T)) := by
  calc edgeZeroExtend Z (ind (triEdges T)) =
      edgeZeroExtend Z (edgeRestrict Z (ind (triEdges (liftVertexSet Z T)))) := by
        rw [edgeRestrict_triangle_boundary]
    _ = ind (triEdges (liftVertexSet Z T)) :=
      edgeZeroExtend_restrict Z _ (triangle_boundary_lift_vanish Z T)

theorem edgeZeroExtend_mem_lattice (H : Host V I) (F : Set (Multiset I)) (Z : Finset V)
    {x : Sym2 (Survivors Z) → ℤ} (hx : x ∈ lattice (restrictedHost H Z) F) :
    edgeZeroExtend Z x ∈ lattice (vertexDeleted H Z) F := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    rw [edgeZeroExtend_triangle_boundary]
    exact Submodule.subset_span ⟨liftVertexSet Z T, (isAllowed_liftVertexSet_iff H F Z T).1 hT, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul k x hx ih => rw [map_smul]; exact Submodule.smul_mem _ k ih

theorem edgeRestrict_mem_lattice (H : Host V I) (F : Set (Multiset I)) (Z : Finset V)
    {x : Sym2 V → ℤ} (hx : x ∈ lattice (vertexDeleted H Z) F) :
    edgeRestrict Z x ∈ lattice (restrictedHost H Z) F := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    have hd := ((isAllowed_vertexDeleted_iff H F Z T).1 hT).2
    have hb : edgeRestrict Z (ind (triEdges T)) = ind (triEdges (T.subtype (fun v => v ∉ Z))) := by
      calc edgeRestrict Z (ind (triEdges T)) =
          edgeRestrict Z (ind (triEdges (liftVertexSet Z (T.subtype (fun v => v ∉ Z))))) := by
            rw [lift_subtypeVertexSet Z T hd]
        _ = ind (triEdges (T.subtype (fun v => v ∉ Z))) := edgeRestrict_triangle_boundary Z _
    rw [hb]
    exact Submodule.subset_span ⟨T.subtype (fun v => v ∉ Z), isAllowed_subtypeVertexSet H F Z T hT, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul k x hx ih => rw [map_smul]; exact Submodule.smul_mem _ k ih

end TypedTriangle
