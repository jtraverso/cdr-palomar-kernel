/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.TypedTriangle.SparseEdgeDefs
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# Simultaneous terminal absorbers for a catalogue of pieces (V28): definitions and basics

* `IsAbsorber G lab F P A`: `A` disjoint from `P`, and BOTH `A` and `A ∪ P` have permitted
  triangle decompositions (the two modes).
* `RobustAbsorberSupply G lab F P s D σ`: the transparent interface of a single-piece
  absorber construction: for every forbidden edge set of maximum degree `≤ D` and every
  forbidden vertex set of size `≤ σ`, an absorber with `≤ s` edges avoiding those edges and
  using no forbidden vertex outside the support of `P`. This is a HYPOTHESIS, not a
  construction; no single-piece terminal absorber construction is present in this tree.
* `ind_mem_lattice_of_absorber`: obstruction — a piece with an absorber lies in the physical
  lattice.
-/

open Finset

noncomputable section
open Classical

namespace S07V28

open TypedTriangle.SparseEdge

variable {V I : Type*} [Fintype V]

/-- `A` is an absorber for `P`: disjoint from `P`, and both `A` and `A ∪ P` have permitted
triangle decompositions. -/
def IsAbsorber (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (P A : Finset (Sym2 V)) : Prop :=
  Disjoint A P ∧ (∃ D, IsDecomposition G lab F A D) ∧ (∃ D, IsDecomposition G lab F (A ∪ P) D)

/-- Robust single-piece absorber supply with size bound `s`, edge-avoidance degree `D` and
vertex-avoidance budget `σ` (interface; a hypothesis, not a construction). -/
def RobustAbsorberSupply (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (P : Finset (Sym2 V)) (s D σ : ℕ) : Prop :=
  ∀ Fb : Finset (Sym2 V), (∀ v, degIn Fb v ≤ D) → ∀ S : Finset V, S.card ≤ σ →
    ∃ A, IsAbsorber G lab F P A ∧ Disjoint A Fb ∧ A.card ≤ s ∧
      ∀ x ∈ support A, x ∈ S → x ∈ support P

/-! ### Basic facts -/

omit [Fintype V] in
lemma isDecomposition_empty (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) :
    IsDecomposition G lab F ∅ ∅ := by
  refine ⟨by simp, by simp, by simp⟩

omit [Fintype V] in
/-- The empty set absorbs the empty piece. -/
lemma isAbsorber_empty (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) :
    IsAbsorber G lab F ∅ ∅ :=
  ⟨by simp, ⟨∅, isDecomposition_empty G lab F⟩, ⟨∅, by simpa using isDecomposition_empty G lab F⟩⟩

/-- Sanity check (non-vacuity of the interface, trivial class only): an already decomposable
piece is robustly absorbed by the empty set. This does NOT supply absorbers for general
physical pieces. -/
lemma robustSupply_of_dec {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {P : Finset (Sym2 V)} (hP : ∃ D, IsDecomposition G lab F P D) (s D σ : ℕ) :
    RobustAbsorberSupply G lab F P s D σ := by
  intro Fb _ S _
  refine ⟨∅, ⟨by simp, ⟨∅, isDecomposition_empty G lab F⟩, by simpa using hP⟩, by simp,
    by simp, ?_⟩
  intro x hx
  simp [support] at hx

omit [Fintype V] in
lemma ind_mem_lattice_of_dec {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {J : Finset (Sym2 V)} {D : Finset (Finset V)} (h : IsDecomposition G lab F J D) :
    ind J ∈ lattice G lab F := by
  obtain ⟨hA, hD, rfl⟩ := h
  rw [ind_biUnion hD]
  exact Submodule.sum_mem _ (fun T hT => ind_mem_lattice (hA T hT))

omit [Fintype V] in
/-- Necessary condition (obstruction): a piece with an absorber lies in the physical
lattice. -/
theorem ind_mem_lattice_of_absorber {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {P A : Finset (Sym2 V)} (h : IsAbsorber G lab F P A) : ind P ∈ lattice G lab F := by
  obtain ⟨hd, ⟨D1, h1⟩, ⟨D2, h2⟩⟩ := h
  have e : ind P = ind (A ∪ P) - ind A := by
    rw [ind_union_of_disjoint hd]; abel
  rw [e]
  exact Submodule.sub_mem _ (ind_mem_lattice_of_dec h2) (ind_mem_lattice_of_dec h1)

omit [Fintype V] in
lemma degIn_union_le (X Y : Finset (Sym2 V)) (v : V) :
    degIn (X ∪ Y) v ≤ degIn X v + degIn Y v := by
  unfold degIn
  rw [filter_union]
  exact card_union_le _ _

omit [Fintype V] in
lemma degIn_biUnion_le {ι : Type*} (s : Finset ι) (f : ι → Finset (Sym2 V)) (v : V) :
    degIn (s.biUnion f) v ≤ ∑ i ∈ s, degIn (f i) v := by
  unfold degIn
  rw [filter_biUnion]
  exact card_biUnion_le

omit [Fintype V] in
lemma degIn_le_card (X : Finset (Sym2 V)) (v : V) : degIn X v ≤ X.card :=
  card_filter_le _ _

lemma degIn_eq_zero_of_not_mem {X : Finset (Sym2 V)} {v : V} (hv : v ∉ support X) :
    degIn X v = 0 := by
  unfold degIn
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hve
  exact hv (mem_support_of_mem he hve)

lemma degIn_le_card_support (X : Finset (Sym2 V)) (v : V) :
    degIn X v ≤ (support X).card := by
  unfold degIn
  have : X.filter (fun e => v ∈ e) ⊆ (support X).image (fun w => s(v, w)) := by
    intro e he
    rw [mem_filter] at he
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 he.2
    exact mem_image.2 ⟨w, mem_support_of_mem he.1 (Sym2.mem_mk_right v w), rfl⟩
  exact (card_le_card this).trans card_image_le

lemma support_nonempty {X : Finset (Sym2 V)} (hX : X ≠ ∅) : (support X).Nonempty := by
  obtain ⟨e, he⟩ := nonempty_iff_ne_empty.2 hX
  induction e using Sym2.ind with
  | h a b => exact ⟨a, mem_support_of_mem he (Sym2.mem_mk_left a b)⟩

lemma ne_empty_of_mem_support {X : Finset (Sym2 V)} {v : V} (hv : v ∈ support X) : X ≠ ∅ := by
  rintro rfl
  simp [support] at hv

lemma card_support_le (X : Finset (Sym2 V)) : (support X).card ≤ 2 * X.card := by
  have : support X ⊆ X.biUnion (fun e => {(Quot.out e).1, (Quot.out e).2}) := by
    intro x hx
    simp only [support, mem_filter, mem_univ, true_and] at hx
    obtain ⟨e, he, hxe⟩ := hx
    refine mem_biUnion.2 ⟨e, he, ?_⟩
    have h1 : e = s((Quot.out e).1, (Quot.out e).2) := (Quot.out_eq e).symm
    rw [h1, Sym2.mem_iff] at hxe
    rcases hxe with h | h <;> simp [h]
  refine (card_le_card this).trans (card_biUnion_le.trans ?_)
  rw [mul_comm]
  exact sum_le_card_nsmul _ _ _ (fun e _ => card_le_two)

end S07V28
