/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.TypedTriangle.VertexZeroExtension

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-!
# Transport of integer local star equations to the surviving vertex subtype

Local proof candidate; NOT kernel-checked in this campaign.
This transport is a pure change of coordinates and requires no H3 or H4.
-/

open Finset
noncomputable section
open Classical

namespace TypedTriangle

variable {V I : Type*} [Fintype V]

lemma mem_edges_restrictedHost (H : Host V I) (Z : Finset V)
    (e : Sym2 (Survivors Z)) :
    Sym2.map Subtype.val e ∈ edges (vertexDeleted H Z) ↔
      e ∈ edges (restrictedHost H Z) := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [Sym2.map_mk]
    constructor
    · intro he
      have hp := (Finset.mem_filter.mp he).2
      have hp' : H.G.Adj u.1 v.1 ∧ u.1 ∉ Z ∧ v.1 ∉ Z := hp
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hp'.1⟩
    · intro he
      have hp : H.G.Adj u.1 v.1 := (Finset.mem_filter.mp he).2
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, ⟨hp, u.2, v.2⟩⟩

lemma localGroup_vertexDeleted_vanish (H : Host V I) (F : Set (Multiset I))
    (Z : Finset V) {x : Sym2 V → ℤ} (hx : x ∈ localGroup (vertexDeleted H Z) F) :
    ∀ e, TouchZ Z e → x e = 0 := by
  intro e he
  apply hx.1 e
  intro hedge
  obtain ⟨v, hv, hve⟩ := he
  exact ((edges_vertexDeleted_iff H Z e).1 hedge).2 v hv hve

/-- Weighted star sums agree under the actual allowed-triangle bijection. -/
lemma star_sum_liftVertexSet (H : Host V I) (F : Set (Multiset I)) (Z : Finset V)
    (v w : Survivors Z) (c : Finset V → ℤ) :
    (∑ T ∈ (triAt (restrictedHost H Z) F v).filter (w ∈ ·), c (liftVertexSet Z T)) =
      ∑ T ∈ (triAt (vertexDeleted H Z) F v.1).filter (w.1 ∈ ·), c T := by
  refine Finset.sum_bij (fun T _ => liftVertexSet Z T) ?_ ?_ ?_ ?_
  · intro T hT
    obtain ⟨hvT, hwT⟩ := Finset.mem_filter.1 hT
    obtain ⟨ha, hvT⟩ := mem_triAt.1 hvT
    exact Finset.mem_filter.2 ⟨mem_triAt.2
      ⟨(isAllowed_liftVertexSet_iff H F Z T).1 ha, (mem_liftVertexSet Z T v).2 hvT⟩,
      (mem_liftVertexSet Z T w).2 hwT⟩
  · intro T _ T' _ heq
    exact liftVertexSet_injective Z heq
  · intro T hT
    obtain ⟨hvT, hwT⟩ := Finset.mem_filter.1 hT
    obtain ⟨ha, hvT⟩ := mem_triAt.1 hvT
    refine ⟨T.subtype (fun v => v ∉ Z), Finset.mem_filter.2 ⟨mem_triAt.2
      ⟨isAllowed_subtypeVertexSet H F Z T ha, Finset.mem_subtype.2 hvT⟩,
      Finset.mem_subtype.2 hwT⟩, ?_⟩
    exact lift_subtypeVertexSet Z T ((isAllowed_vertexDeleted_iff H F Z T).1 ha).2
  · intro T _
    rfl

theorem edgeRestrict_mem_localGroup (H : Host V I) (F : Set (Multiset I)) (Z : Finset V)
    {x : Sym2 V → ℤ} (hx : x ∈ localGroup (vertexDeleted H Z) F) :
    edgeRestrict Z x ∈ localGroup (restrictedHost H Z) F := by
  refine ⟨?_, ?_⟩
  · intro e he
    apply hx.1 (Sym2.map Subtype.val e)
    exact fun h => he ((mem_edges_restrictedHost H Z e).1 h)
  · intro v
    obtain ⟨c, hc⟩ := hx.2 v.1
    refine ⟨fun T => c (liftVertexSet Z T), fun w hw => ?_⟩
    have hstar := (hc w.1 (fun heq => hw (Subtype.ext heq))).trans
      (star_sum_liftVertexSet H F Z v w c).symm
    convert hstar using 1 <;> congr 1 <;> ext T <;> simp [triAt, allowed]

/-- Transport every integer local star preimage, not only physical demands. -/
theorem edgeZeroExtend_mem_localGroup (H : Host V I) (F : Set (Multiset I)) (Z : Finset V)
    {x : Sym2 (Survivors Z) → ℤ} (hx : x ∈ localGroup (restrictedHost H Z) F) :
    edgeZeroExtend Z x ∈ localGroup (vertexDeleted H Z) F := by
  refine ⟨?_, ?_⟩
  · intro e he
    change (if h : ∀ v ∈ e, v ∉ Z then x (e.attachWith h) else 0) = 0
    split_ifs with hav
    · apply hx.1 (e.attachWith hav)
      intro hsub
      have hmap := (mem_edges_restrictedHost H Z (e.attachWith hav)).2 hsub
      apply he
      simpa only [Sym2.attachWith_map_subtypeVal] using hmap
    · rfl
  · intro v
    by_cases hv : v ∈ Z
    · refine ⟨0, fun w _ => ?_⟩
      have he := edgeZeroExtend_vanish Z x s(v, w) ⟨v, hv, by simp⟩
      simpa using he
    · let v' : Survivors Z := ⟨v, hv⟩
      obtain ⟨c, hc⟩ := hx.2 v'
      let c' : Finset V → ℤ := fun T =>
        if Disjoint T Z then c (T.subtype (fun v => v ∉ Z)) else 0
      have hcoeff : ∀ T : Finset (Survivors Z), c' (liftVertexSet Z T) = c T := by
        intro T
        change (if Disjoint (liftVertexSet Z T) Z then
          c ((liftVertexSet Z T).subtype (fun v => v ∉ Z)) else 0) = c T
        rw [if_pos (liftVertexSet_avoids Z T), subtype_liftVertexSet]
      refine ⟨c', fun w hw => ?_⟩
      by_cases hwZ : w ∈ Z
      · have hleft := edgeZeroExtend_vanish Z x s(v, w) ⟨w, hwZ, by simp⟩
        have hsum : (∑ T ∈ (triAt (vertexDeleted H Z) F v).filter (w ∈ ·), c' T) = 0 := by
          apply Finset.sum_eq_zero
          intro T hT
          obtain ⟨hvT, hwT⟩ := Finset.mem_filter.1 hT
          have ha := (mem_triAt.1 hvT).1
          have hd := ((isAllowed_vertexDeleted_iff H F Z T).1 ha).2
          exact False.elim (Finset.disjoint_left.1 hd hwT hwZ)
        exact hleft.trans hsum.symm
      · let w' : Survivors Z := ⟨w, hwZ⟩
        have hne : w' ≠ v' := fun heq => hw (congrArg Subtype.val heq)
        calc edgeZeroExtend Z x s(v, w) = x s(v', w') :=
              edgeZeroExtend_apply_map Z x s(v', w')
          _ = ∑ T ∈ (triAt (restrictedHost H Z) F v').filter (w' ∈ ·), c T := by
              convert hc w' hne using 1 <;> congr 1 <;> ext T <;> simp [triAt, allowed]
          _ = ∑ T ∈ (triAt (restrictedHost H Z) F v').filter (w' ∈ ·), c' (liftVertexSet Z T) :=
              Finset.sum_congr rfl (fun T _ => (hcoeff T).symm)
          _ = ∑ T ∈ (triAt (vertexDeleted H Z) F v).filter (w ∈ ·), c' T :=
              star_sum_liftVertexSet H F Z v' w' c'

/-- A genuine integer linear equivalence of local groups, independent of geometry. -/
def survivingLocalEquiv (H : Host V I) (F : Set (Multiset I)) (Z : Finset V) :
    localGroup (restrictedHost H Z) F ≃ₗ[ℤ] localGroup (vertexDeleted H Z) F where
  toFun x := ⟨edgeZeroExtend Z x.1, edgeZeroExtend_mem_localGroup H F Z x.2⟩
  invFun y := ⟨edgeRestrict Z y.1, edgeRestrict_mem_localGroup H F Z y.2⟩
  left_inv x := Subtype.ext (edgeRestrict_zeroExtend Z x.1)
  right_inv y := Subtype.ext (edgeZeroExtend_restrict Z y.1
    (localGroup_vertexDeleted_vanish H F Z y.2))
  map_add' x y := Subtype.ext ((edgeZeroExtend Z).map_add x.1 y.1)
  map_smul' k x := Subtype.ext ((edgeZeroExtend Z).map_smul k x.1)

lemma survivingLocalEquiv_map_lattice (H : Host V I) (F : Set (Multiset I)) (Z : Finset V) :
    ((lattice (restrictedHost H Z) F).comap (localGroup (restrictedHost H Z) F).subtype).map
      (survivingLocalEquiv H F Z).toLinearMap =
    (lattice (vertexDeleted H Z) F).comap (localGroup (vertexDeleted H Z) F).subtype := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact edgeZeroExtend_mem_lattice H F Z hx
  · intro hy
    refine ⟨(survivingLocalEquiv H F Z).symm y, ?_, (survivingLocalEquiv H F Z).apply_symm_apply y⟩
    exact edgeRestrict_mem_lattice H F Z hy

/-- Physical quotients of the subtype and of its ambient zero extension are equivalent. -/
def survivingPhysQuotEquiv (H : Host V I) (F : Set (Multiset I)) (Z : Finset V) :
    physQuot (restrictedHost H Z) F ≃ₗ[ℤ] physQuot (vertexDeleted H Z) F :=
  Submodule.Quotient.equiv _ _ (survivingLocalEquiv H F Z)
    (survivingLocalEquiv_map_lattice H F Z)

lemma finrank_survivingPhysQuot (H : Host V I) (F : Set (Multiset I)) (Z : Finset V) :
    Module.finrank ℤ (physQuot (restrictedHost H Z) F) =
      Module.finrank ℤ (physQuot (vertexDeleted H Z) F) :=
  (survivingPhysQuotEquiv H F Z).finrank_eq

lemma torsion_card_survivingPhysQuot (H : Host V I) (F : Set (Multiset I)) (Z : Finset V) :
    Nat.card (Submodule.torsion ℤ (physQuot (restrictedHost H Z) F)) =
      Nat.card (Submodule.torsion ℤ (physQuot (vertexDeleted H Z) F)) := by
  let e := survivingPhysQuotEquiv H F Z
  have hk : LinearMap.ker e.toLinearMap = ⊥ := LinearMap.ker_eq_bot.2 e.injective
  have ht := Robust.torsion_card_of_surjective e.toLinearMap e.surjective
    (by rw [hk]; exact bot_le)
  rw [hk] at ht
  simpa using ht

end TypedTriangle
