/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.ReserveSize

/-!
# The actual group-plus-reserve pieces of a Wilson residual

Every residual edge meeting a group belongs to a unique piece. Reserve pairs
belong to all pieces. Every residual clique is contained in one piece.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle CDRBicolour.Absorption
open scoped Classical

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}
variable (h : Setup lab κ g t) {S : Finset (Finset (Fin g))}

def group (i : Fin g) : Finset (Fin n) :=
  univ.image fun p : A × Fin t => gv h i p.1 p.2

def piece (i : Fin g) : Finset (Fin n) := group h i ∪ reserve h

theorem mem_group {i : Fin g} {v : Fin n} :
    v ∈ group h i ↔ ∃ P α, v = gv h i P α := by
  simp only [group, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨⟨P,α⟩, he⟩; exact ⟨P,α,he.symm⟩
  · rintro ⟨P,α,he⟩; exact ⟨(P,α),he.symm⟩

theorem group_index_unique {i j : Fin g} {u : Fin n}
    (hi : u ∈ group h i) (hj : u ∈ group h j) : i = j := by
  obtain ⟨P,α,hP⟩ := (mem_group h).mp hi
  obtain ⟨Q,β,hQ⟩ := (mem_group h).mp hj
  exact (gv_inj h (hP.symm.trans hQ)).1

theorem group_not_reserve {i : Fin g} {u : Fin n} (hu : u ∈ group h i) :
    u ∉ reserve h := by
  obtain ⟨P,α,hP⟩ := (mem_group h).mp hu
  exact fun hR => (mem_reserve h).mp hR i P α hP

theorem not_reserve_iff {u : Fin n} :
    u ∉ reserve h ↔ ∃ i, u ∈ group h i := by
  rw [mem_reserve]
  push_neg
  simp only [mem_group]

theorem group_piece_index {i j : Fin g} {u : Fin n} (hu : u ∈ group h i) :
    u ∈ piece h j ↔ j = i := by
  constructor
  · intro hj
    rcases mem_union.mp hj with hj | hj
    · exact group_index_unique h hj hu
    · exact (group_not_reserve h hu hj).elim
  · rintro rfl; exact mem_union.mpr (Or.inl hu)

theorem piece_complete (hS : _root_.STS.IsSTS S) (Λ : LFam A S t) (i : Fin g)
    {u v : Fin n} (hu : u ∈ piece h i) (hv : v ∈ piece h i) (huv : u ≠ v) :
    (rG ((crossP h Λ).biUnion triEdges)).Adj u v := by
  rw [rG_adj]
  refine ⟨fun he => ?_, huv⟩
  obtain ⟨p,q,P,Q,α,β,hpq,rfl,rfl⟩ := (mem_crossEdges h hS Λ).mp he
  have hp := (group_piece_index h ((mem_group h).mpr ⟨P,α,rfl⟩)).mp hu
  have hq := (group_piece_index h ((mem_group h).mpr ⟨Q,β,rfl⟩)).mp hv
  exact hpq (hp.symm.trans hq)

theorem residual_neighbor_piece (hS : _root_.STS.IsSTS S) (Λ : LFam A S t)
    {i : Fin g} {u v : Fin n} (hu : u ∈ group h i)
    (hadj : (rG ((crossP h Λ).biUnion triEdges)).Adj u v) : v ∈ piece h i := by
  by_cases hvR : v ∈ reserve h
  · exact mem_union.mpr (Or.inr hvR)
  · obtain ⟨j,hv⟩ := (not_reserve_iff h).mp hvR
    have hij : i = j := by
      by_contra hij
      obtain ⟨P,α,hP⟩ := (mem_group h).mp hu
      obtain ⟨Q,β,hQ⟩ := (mem_group h).mp hv
      exact (rG_adj.mp hadj).1 ((mem_crossEdges h hS Λ).mpr ⟨i,j,P,Q,α,β,hij,hP,hQ⟩)
    exact mem_union.mpr (Or.inl (hij ▸ hv))

theorem residual_edge_unique_piece (hS : _root_.STS.IsSTS S) (Λ : LFam A S t)
    {u v : Fin n} (hadj : (rG ((crossP h Λ).biUnion triEdges)).Adj u v)
    (hRR : ¬(u ∈ reserve h ∧ v ∈ reserve h)) :
    ∃ i0 : Fin g, ∀ i : Fin g, (u ∈ piece h i ∧ v ∈ piece h i) ↔ i = i0 := by
  have key : ∀ {u v : Fin n},
      (rG ((crossP h Λ).biUnion triEdges)).Adj u v → u ∉ reserve h →
      ∃ i0 : Fin g, ∀ i : Fin g, (u ∈ piece h i ∧ v ∈ piece h i) ↔ i = i0 := by
    intro u v hadj huR
    obtain ⟨i0,hu⟩ := (not_reserve_iff h).mp huR
    refine ⟨i0, fun i => ⟨fun hi => (group_piece_index h hu).mp hi.1, ?_⟩⟩
    rintro rfl
    exact ⟨mem_union.mpr (Or.inl hu), residual_neighbor_piece h hS Λ hu hadj⟩
  by_cases huR : u ∈ reserve h
  · obtain ⟨i0,hi0⟩ := key hadj.symm (fun hvR => hRR ⟨huR,hvR⟩)
    exact ⟨i0, fun i => by rw [and_comm]; exact hi0 i⟩
  · exact key hadj huR

theorem residual_clique_piece (hS : _root_.STS.IsSTS S) (Λ : LFam A S t) (hg : 0 < g)
    {T : Finset (Fin n)}
    (hT : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (rG ((crossP h Λ).biUnion triEdges)).Adj u v) :
    ∃ i : Fin g, T ⊆ piece h i := by
  by_cases hR : ∀ u ∈ T, u ∈ reserve h
  · exact ⟨⟨0,hg⟩, fun u hu => mem_union.mpr (Or.inr (hR u hu))⟩
  · push_neg at hR
    obtain ⟨u,hu,huR⟩ := hR
    obtain ⟨i,hi⟩ := (not_reserve_iff h).mp huR
    refine ⟨i, fun v hv => ?_⟩
    by_cases huv : u = v
    · exact huv ▸ mem_union.mpr (Or.inl hi)
    · exact residual_neighbor_piece h hS Λ hi (hT u hu v hv huv)

end CDRBicolour.KBicolor.Wilson
