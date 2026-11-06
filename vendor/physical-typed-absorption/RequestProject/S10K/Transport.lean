/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S10K.HingeCount
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)

@[expose] public section

/-!
# V23 / S05 §2: deterministic hinge transport on the physical triangle matrix

For the physical matrix `A = realOp (triMat (allowedTri G lab F))`:

* `A_single` : `A δ_S = χ_(E(S))` for a permitted triangle `S`;
* `A_decVec` : a permitted decomposition `D` of an edge set `X` has `A (Σ_(S∈D) δ_S) = χ_X`;
* `A_hinge`  : the two fixed modes of a hinge certify `χ_(uva) − χ_(uvb)`;
* facts about decomposition triangles (`edgesOf S ⊆ X`, vertices in the support, uniqueness
  of the triangle covering an edge, and avoidance of a source triangle `T` when `X` misses
  `E(T)`).

`decOf X` FIXES deterministically one decomposition of each edge set `X` (or `∅`).
No probabilistic or counting input is used here.
-/

open Finset

noncomputable section
open Classical

namespace S10V23

open TypedTriangle.SparseEdge S10V22

variable {V I : Type*} [Fintype V]
  {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-- Real indicator of an edge set. -/
def chiR (X : Finset (Sym2 V)) : Sym2 V → ℝ := fun e => if e ∈ X then 1 else 0

/-- Coefficient vector of a family of triangles. -/
def decVec (D : Finset (Finset V)) : Finset V → ℝ := fun S => if S ∈ D then 1 else 0

/-- The deterministically fixed decomposition witness of an edge set. -/
def decOf (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (X : Finset (Sym2 V)) :
    Finset (Finset V) :=
  if h : ∃ D, IsDecomposition G lab F X D then Classical.choose h else ∅

lemma decOf_spec {X : Finset (Sym2 V)} (h : ∃ D, IsDecomposition G lab F X D) :
    IsDecomposition G lab F X (decOf G lab F X) := by
  unfold decOf
  rw [dif_pos h]
  exact Classical.choose_spec h

omit [Fintype V] in
lemma chiR_union {X Y : Finset (Sym2 V)} (h : Disjoint X Y) :
    chiR (X ∪ Y) = chiR X + chiR Y := by
  funext e
  simp only [chiR, mem_union, Pi.add_apply]
  by_cases hX : e ∈ X
  · simp [hX, Finset.disjoint_left.1 h hX]
  · by_cases hY : e ∈ Y <;> simp [hX, hY]

lemma A_single {S : Finset V} (hS : IsAllowed G lab F S) :
    realOp (triMat (allowedTri G lab F)) (Pi.single S 1) = chiR (edgesOf S) := by
  funext e
  have hS' : S ∈ allowedTri G lab F := mem_allowedTri.2 hS
  simp only [realOp, LinearMap.coe_mk, AddHom.coe_mk, chiR]
  rw [Finset.sum_eq_single S]
  · simp [triMat, hS']
  · intro b _ hb; simp [hb]
  · simp

lemma col_eq {S : Finset V} (hS : IsAllowed G lab F S) :
    col (realOp (triMat (allowedTri G lab F))) S = chiR (edgesOf S) := A_single hS

lemma A_decVec {X : Finset (Sym2 V)} {D : Finset (Finset V)}
    (hD : IsDecomposition G lab F X D) :
    realOp (triMat (allowedTri G lab F)) (decVec D) = chiR X := by
  obtain ⟨hall, hdisj, hU⟩ := hD
  have hsum : decVec D = ∑ S ∈ D, (Pi.single S (1 : ℝ) : Finset V → ℝ) := by
    funext S
    simp [decVec, Finset.sum_apply, Pi.single_apply]
  rw [hsum, map_sum]
  rw [Finset.sum_congr rfl (fun S hS => A_single (hall S hS))]
  rw [← hU]
  clear hU hsum
  induction D using Finset.induction_on with
  | empty => funext e; simp [chiR]
  | insert S D hS ih =>
    rw [Finset.sum_insert hS, Finset.biUnion_insert]
    have hd' : (D : Set (Finset V)).PairwiseDisjoint triEdges := hdisj.subset (by simp)
    rw [ih (fun T hT => hall T (by simp [hT])) hd']
    rw [chiR_union, ← triEdges_eq_edgesOf]
    rw [Finset.disjoint_biUnion_right]
    intro T hT
    exact hdisj (by simp) (by simp [hT]) (fun h => hS (h ▸ hT))

omit [Fintype V] in
lemma edgesOf_triple {u v a : V} (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) :
    edgesOf ({u, v, a} : Finset V) = insert s(u, v) (wedge u v a) := by
  rw [← triEdges_eq_edgesOf]
  convert triEdges_triple huv hua hva

/-- **Hinge transport.** -/
theorem A_hinge {u v a b : V} {J : Finset (Sym2 V)} (hJ : IsHinge G lab F u v a b J)
    (huv : u ≠ v) (hua : u ≠ a) (hva : v ≠ a) (hub : u ≠ b) (hvb : v ≠ b)
    {Da Db : Finset (Finset V)} (hDa : IsDecomposition G lab F (J ∪ wedge u v a) Da)
    (hDb : IsDecomposition G lab F (J ∪ wedge u v b) Db) :
    realOp (triMat (allowedTri G lab F)) (decVec Da - decVec Db) =
      chiR (edgesOf {u, v, a}) - chiR (edgesOf {u, v, b}) := by
  rw [map_sub, A_decVec hDa, A_decVec hDb]
  have hJa : Disjoint J (wedge u v a) := by
    refine hJ.2.1.mono_right ?_
    rw [triEdges_triple huv hua hva]
    exact (Finset.subset_insert _ _).trans Finset.subset_union_left
  have hJb : Disjoint J (wedge u v b) := by
    refine hJ.2.1.mono_right ?_
    rw [triEdges_triple huv hub hvb]
    exact (Finset.subset_insert _ _).trans Finset.subset_union_right
  rw [edgesOf_triple huv hua hva, edgesOf_triple huv hub hvb, chiR_union hJa, chiR_union hJb,
    Finset.insert_eq, Finset.insert_eq,
    chiR_union (Finset.disjoint_singleton_left.2 (not_mem_wedge_uv huv hua hva)),
    chiR_union (Finset.disjoint_singleton_left.2 (not_mem_wedge_uv huv hub hvb))]
  abel

/-! ## Triangles of a decomposition -/

section DecFacts

variable {X : Finset (Sym2 V)} {D : Finset (Finset V)}

omit [Fintype V] in
lemma allowed_of_mem_dec (hD : IsDecomposition G lab F X D) {S : Finset V} (hS : S ∈ D) :
    IsAllowed G lab F S := hD.1 S hS

omit [Fintype V] in
lemma edgesOf_subset_of_mem_dec (hD : IsDecomposition G lab F X D) {S : Finset V}
    (hS : S ∈ D) : edgesOf S ⊆ X := by
  intro e he
  rw [← hD.2.2, ← triEdges_eq_edgesOf] at *
  exact Finset.mem_biUnion.2 ⟨S, hS, by rwa [triEdges_eq_edgesOf] at he ⊢⟩

omit [Fintype V] in
lemma exists_mem_dec (hD : IsDecomposition G lab F X D) {e : Sym2 V} (he : e ∈ X) :
    ∃ S ∈ D, e ∈ edgesOf S := by
  rw [← hD.2.2] at he
  obtain ⟨S, hS, heS⟩ := Finset.mem_biUnion.1 he
  exact ⟨S, hS, by rwa [triEdges_eq_edgesOf] at heS⟩

omit [Fintype V] in
lemma eq_of_mem_dec (hD : IsDecomposition G lab F X D) {S S' : Finset V} (hS : S ∈ D)
    (hS' : S' ∈ D) {e : Sym2 V} (he : e ∈ edgesOf S) (he' : e ∈ edgesOf S') : S = S' := by
  by_contra hne
  have := hD.2.1 hS hS' hne
  rw [Function.onFun, triEdges_eq_edgesOf, triEdges_eq_edgesOf] at this
  exact Finset.disjoint_left.1 this he he'

omit [Fintype V] in
lemma mem_edgesOf {T : Finset V} {x y : V} : s(x, y) ∈ edgesOf T ↔ x ∈ T ∧ y ∈ T ∧ x ≠ y := by
  rw [← triEdges_eq_edgesOf]; exact mem_triEdges

/-- Vertices of a decomposition triangle are in the support of `X`. -/
lemma subset_support_of_mem_dec (hD : IsDecomposition G lab F X D) {S : Finset V}
    (hS : S ∈ D) : S ⊆ support X := by
  intro x hx
  have h3 := (hD.1 S hS).1
  obtain ⟨y, hy, hyx, -⟩ := exists_third h3 x x
  have : s(x, y) ∈ X := edgesOf_subset_of_mem_dec hD hS (mem_edgesOf.2 ⟨hx, hy, hyx.symm⟩)
  exact mem_support_of_mem this (by simp)

omit [Fintype V] in
/-- A 3-set sharing two vertices with `T` contains an edge of `T`. -/
lemma exists_edge_of_two_le {S T : Finset V} (h : 2 ≤ (S ∩ T).card) :
    ∃ x y, x ≠ y ∧ x ∈ S ∧ y ∈ S ∧ x ∈ T ∧ y ∈ T := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h
  rw [Finset.mem_inter] at hx hy
  exact ⟨x, y, hxy, hx.1, hy.1, hx.2, hy.2⟩

omit [Fintype V] in
/-- A triangle of a decomposition of an edge set missing `E(T)` shares at most one vertex
with `T`. -/
lemma inter_le_one_of_mem_dec (hD : IsDecomposition G lab F X D) {S T : Finset V}
    (hS : S ∈ D) (hX : Disjoint X (edgesOf T)) : (S ∩ T).card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨x, y, hxy, hxS, hyS, hxT, hyT⟩ := exists_edge_of_two_le h
  have h1 : s(x, y) ∈ X := edgesOf_subset_of_mem_dec hD hS (mem_edgesOf.2 ⟨hxS, hyS, hxy⟩)
  exact Finset.disjoint_left.1 hX h1 (mem_edgesOf.2 ⟨hxT, hyT, hxy⟩)

end DecFacts

end S10V23
