/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10K.Transport
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# V23 / S05 §2: one-deleted-edge transport, avoiding all three edges of the source

Deterministic part of the "una arista borrada" step of S05 §2, specialised to
`B = E(T)` for a source triangle `T = {p, q, r}`. A triangle `Q = pqx` (with `x ∉ T`) is
transported to the pivot `P = pqb` (with `b ∉ T`) through a bridge `pqy` and two original
hinges `J` (roots `p,q,x,y`) and `J'` (roots `p,q,y,b`) whose supports avoid `r`:

  `tvec = D_x(J) − D_y(J) + D_y(J') − D_b(J')`,  `A tvec = χ_Q − χ_P`,

and `tvec` vanishes on every triangle sharing two vertices with `T` (`oneEdge_transport`).
Each `D_•` is the FIXED decomposition `decOf` of the corresponding edge set.

Also: unconditional facts on `decOf`, the disjointness helpers, and `cover_facts` (the unique
triangle of a decomposition through a given edge).

No probabilistic or counting input is used here; the hinges are hypotheses of the lemma and
are supplied by the random process (`SourceProcess.lean`).
-/

open Finset

noncomputable section
open Classical

namespace S10V23

open TypedTriangle.SparseEdge S10V22

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-- The physical triangle matrix as a real linear map. -/
abbrev Aop (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) :
    (Finset V → ℝ) →ₗ[ℝ] (Sym2 V → ℝ) :=
  realOp (triMat (allowedTri G lab F))

/-! ## Unconditional facts on the fixed decompositions -/

lemma mem_decOf {X : Finset (Sym2 V)} {S : Finset V} (hS : S ∈ decOf G lab F X) :
    IsDecomposition G lab F X (decOf G lab F X) := by
  by_cases h : ∃ D, IsDecomposition G lab F X D
  · exact decOf_spec h
  · simp [decOf, h] at hS

lemma allowed_of_mem_decOf {X : Finset (Sym2 V)} {S : Finset V} (hS : S ∈ decOf G lab F X) :
    IsAllowed G lab F S := allowed_of_mem_dec (mem_decOf hS) hS

lemma edgesOf_subset_of_mem_decOf {X : Finset (Sym2 V)} {S : Finset V}
    (hS : S ∈ decOf G lab F X) : edgesOf S ⊆ X := edgesOf_subset_of_mem_dec (mem_decOf hS) hS

lemma subset_support_of_mem_decOf {X : Finset (Sym2 V)} {S : Finset V}
    (hS : S ∈ decOf G lab F X) : S ⊆ support X := subset_support_of_mem_dec (mem_decOf hS) hS

omit [Fintype V] in
lemma decVec_eq_zero {D : Finset (Finset V)} {S : Finset V} (h : S ∉ D) : decVec D S = 0 := by
  simp [decVec, h]

omit [Fintype V] in
lemma abs_decVec_le (D : Finset (Finset V)) (S : Finset V) : |decVec D S| ≤ 1 := by
  unfold decVec; split_ifs <;> simp

/-- A decomposition triangle avoids `T` when the edge set misses `E(T)`. -/
lemma decVec_decOf_eq_zero {X : Finset (Sym2 V)} {T S : Finset V}
    (hX : Disjoint X (edgesOf T)) (hS : 2 ≤ (S ∩ T).card) :
    decVec (decOf G lab F X) S = 0 := by
  refine decVec_eq_zero fun hmem => ?_
  have := inter_le_one_of_mem_dec (mem_decOf hmem) hmem hX
  omega

/-! ## Disjointness helpers -/

omit [Fintype V] in
lemma disjoint_union_wedge {J : Finset (Sym2 V)} {T : Finset V} {p q y : V}
    (hJ : Disjoint J (edgesOf T)) (hy : y ∉ T) : Disjoint (J ∪ wedge p q y) (edgesOf T) := by
  refine Finset.disjoint_union_left.2 ⟨hJ, Finset.disjoint_left.2 fun e he heT => ?_⟩
  simp only [wedge, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact hy (mem_edgesOf.1 heT).2.1
  · exact hy (mem_edgesOf.1 heT).2.1

lemma disjoint_of_avoid {J : Finset (Sym2 V)} {p q r : V} (hpq : s(p, q) ∉ J)
    (hr : r ∉ support J) : Disjoint J (edgesOf {p, q, r}) := by
  refine Finset.disjoint_left.2 fun e he heT => ?_
  induction e using Sym2.ind with
  | _ x y =>
  obtain ⟨hx, hy, hxy⟩ := mem_edgesOf.1 heT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  have hxJ := mem_support_of_mem he (by simp : x ∈ s(x, y))
  have hyJ := mem_support_of_mem he (by simp : y ∈ s(x, y))
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first
    | exact hxy rfl
    | exact hr hxJ
    | exact hr hyJ
    | exact hpq he
    | exact hpq (by rwa [Sym2.eq_swap] at he)

lemma disjoint_hinge_left {J : Finset (Sym2 V)} {u v a c : V}
    (hJ : IsHinge G lab F u v a c J) : Disjoint J (edgesOf {u, v, a}) := by
  have := hJ.2.1.mono_right (Finset.subset_union_left (s₂ := triEdges {u, v, c}))
  rwa [triEdges_eq_edgesOf] at this

lemma not_mem_hinge_uv {J : Finset (Sym2 V)} {u v a c : V} (hJ : IsHinge G lab F u v a c J)
    (huv : u ≠ v) : s(u, v) ∉ J := fun h =>
  Finset.disjoint_left.1 (disjoint_hinge_left hJ) h (mem_edgesOf.2 ⟨by simp, by simp, huv⟩)

/-! ## One-deleted-edge transport -/

/-- The transport vector `D_x(J) − D_y(J) + D_y(J') − D_b(J')`. -/
def tvec (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (J J' : Finset (Sym2 V))
    (p q x y b : V) : Finset V → ℝ :=
  decVec (decOf G lab F (J ∪ wedge p q x)) - decVec (decOf G lab F (J ∪ wedge p q y)) +
    (decVec (decOf G lab F (J' ∪ wedge p q y)) - decVec (decOf G lab F (J' ∪ wedge p q b)))

/-- **One-deleted-edge transport (S05 §2, `B = E(T)`).** -/
theorem oneEdge_transport {p q r x y b : V} {J J' : Finset (Sym2 V)}
    (hpq : p ≠ q) (hxT : x ∉ ({p, q, r} : Finset V)) (hyT : y ∉ ({p, q, r} : Finset V))
    (hbT : b ∉ ({p, q, r} : Finset V))
    (hJ : IsHinge G lab F p q x y J) (hrJ : r ∉ support J)
    (hJ' : IsHinge G lab F p q y b J') (hrJ' : r ∉ support J') :
    Aop G lab F (tvec G lab F J J' p q x y b) =
        chiR (edgesOf {p, q, x}) - chiR (edgesOf {p, q, b}) ∧
      ∀ S, 2 ≤ (S ∩ {p, q, r}).card → tvec G lab F J J' p q x y b S = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxT hyT hbT
  obtain ⟨hxp, hxq, hxr⟩ := hxT
  obtain ⟨hyp, hyq, hyr⟩ := hyT
  obtain ⟨hbp, hbq, hbr⟩ := hbT
  refine ⟨?_, fun S hS => ?_⟩
  · unfold tvec
    rw [map_add, A_hinge hJ hpq (Ne.symm hxp) (Ne.symm hxq) (Ne.symm hyp) (Ne.symm hyq)
        (decOf_spec hJ.2.2.1) (decOf_spec hJ.2.2.2),
      A_hinge hJ' hpq (Ne.symm hyp) (Ne.symm hyq) (Ne.symm hbp) (Ne.symm hbq)
        (decOf_spec hJ'.2.2.1) (decOf_spec hJ'.2.2.2)]
    abel
  · have hJd : Disjoint J (edgesOf {p, q, r}) := disjoint_of_avoid
      (not_mem_hinge_uv hJ hpq) hrJ
    have hJd' : Disjoint J' (edgesOf {p, q, r}) := disjoint_of_avoid
      (not_mem_hinge_uv hJ' hpq) hrJ'
    have nx : x ∉ ({p, q, r} : Finset V) := by simp [hxp, hxq, hxr]
    have ny : y ∉ ({p, q, r} : Finset V) := by simp [hyp, hyq, hyr]
    have nb : b ∉ ({p, q, r} : Finset V) := by simp [hbp, hbq, hbr]
    unfold tvec
    simp only [Pi.add_apply, Pi.sub_apply,
      decVec_decOf_eq_zero (disjoint_union_wedge hJd nx) hS,
      decVec_decOf_eq_zero (disjoint_union_wedge hJd ny) hS,
      decVec_decOf_eq_zero (disjoint_union_wedge hJd' ny) hS,
      decVec_decOf_eq_zero (disjoint_union_wedge hJd' nb) hS]
    norm_num

/-! ## The triangle of a decomposition through a given edge -/

/-- The (chosen) triangle of `D` through `e`, or `∅`. -/
def cover (D : Finset (Finset V)) (e : Sym2 V) : Finset V :=
  if h : ∃ S ∈ D, e ∈ edgesOf S then Classical.choose h else ∅

/-- A vertex of `S` other than `p, q` (or `p`). -/
def third (S : Finset V) (p q : V) : V :=
  if h : ∃ x ∈ S, x ≠ p ∧ x ≠ q then Classical.choose h else p

omit [Fintype V] in
lemma cover_spec {D : Finset (Finset V)} {e : Sym2 V} (h : ∃ S ∈ D, e ∈ edgesOf S) :
    cover D e ∈ D ∧ e ∈ edgesOf (cover D e) := by
  unfold cover; rw [dif_pos h]; exact Classical.choose_spec h

omit [Fintype V] in
lemma cover_subset (D : Finset (Finset V)) (e : Sym2 V) :
    cover D e ∈ D ∨ cover D e = ∅ := by
  unfold cover
  split_ifs with h
  · exact Or.inl (Classical.choose_spec h).1
  · exact Or.inr rfl

omit [Fintype V] in
lemma third_mem_or (S : Finset V) (p q : V) : third S p q ∈ S ∨ third S p q = p := by
  unfold third
  split_ifs with h
  · exact Or.inl (Classical.choose_spec h).1
  · exact Or.inr rfl

omit [Fintype V] in
lemma decVec_singleton (Q : Finset V) : decVec {Q} = (Pi.single Q (1 : ℝ) : Finset V → ℝ) := by
  funext S
  simp [decVec, Pi.single_apply]

omit [Fintype V] in
/-- **Facts on the triangle through an edge.** `D` decomposes `X`, `pq ∈ X`, `pr ∉ X`. -/
theorem cover_facts {X : Finset (Sym2 V)} {D : Finset (Finset V)}
    (hD : IsDecomposition G lab F X D) {p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (he : s(p, q) ∈ X) (hpr' : s(p, r) ∉ X) :
    cover D s(p, q) ∈ D ∧ s(p, q) ∈ edgesOf (cover D s(p, q)) ∧
      D.filter (fun S => s(p, q) ∈ edgesOf S) = {cover D s(p, q)} ∧
      r ∉ cover D s(p, q) ∧ IsAllowed G lab F (cover D s(p, q)) ∧
      third (cover D s(p, q)) p q ∉ ({p, q, r} : Finset V) ∧
      cover D s(p, q) = {p, q, third (cover D s(p, q)) p q} := by
  set Q := cover D s(p, q)
  obtain ⟨hQ, heQ⟩ := cover_spec (exists_mem_dec hD he)
  have hall := allowed_of_mem_dec hD hQ
  obtain ⟨hp, hq, -⟩ := mem_edgesOf.1 heQ
  have hrQ : r ∉ Q := fun hr =>
    hpr' (edgesOf_subset_of_mem_dec hD hQ (mem_edgesOf.2 ⟨hp, hr, hpr⟩))
  have hex : ∃ x ∈ Q, x ≠ p ∧ x ≠ q := exists_third hall.1 p q
  have hthird : third Q p q ∈ Q ∧ third Q p q ≠ p ∧ third Q p q ≠ q := by
    unfold third; rw [dif_pos hex]; exact Classical.choose_spec hex
  obtain ⟨hxQ, hxp, hxq⟩ := hthird
  have hQeq : Q = {p, q, third Q p q} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    · rw [hall.1, card_three_of_distinct hpq (Ne.symm hxp) (Ne.symm hxq)]
  refine ⟨hQ, heQ, ?_, hrQ, hall, ?_, hQeq⟩
  · ext S
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hS, heS⟩; exact eq_of_mem_dec hD hS hQ heS heQ
    · rintro rfl; exact ⟨hQ, heQ⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hxp, hxq, fun h => hrQ (h ▸ hxQ)⟩

end S10V23
