/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Classes

/-!
# Unions of edge-disjoint factors

Adjacency and degrees in `T.sup F` for a family of edge-disjoint near 1-factors, and colouring
`B ⊔ T.sup F` with `#T` more colours than `B`.
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem finsetSup_adj {F : ℕ → SimpleGraph V} (T : Finset ℕ) {a b : V} :
    (T.sup F).Adj a b ↔ ∃ k ∈ T, (F k).Adj a b := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
    rw [sup_insert, sup_adj, ih]
    simp only [mem_insert]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨j, Or.inl rfl, h⟩
      · exact ⟨k, Or.inr hk, h⟩
    · rintro ⟨k, rfl | hk, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, hk, h⟩

/-- Degrees add up over edge-disjoint graphs. -/
theorem degree_finsetSup {F : ℕ → SimpleGraph V} (T : Finset ℕ)
    (hdisj : ∀ j ∈ T, ∀ k ∈ T, j ≠ k → Disjoint (F j) (F k)) (v : V) :
    (T.sup F).degree v = ∑ k ∈ T, (F k).degree v := by
  induction T using Finset.induction_on with
  | empty =>
    rw [sum_empty, ← card_neighborFinset_eq_degree, card_eq_zero]
    ext u; simp [mem_neighborFinset, finsetSup_adj]
  | insert j T hj ih =>
    rw [sum_insert hj, ← ih fun a ha b hb hab => hdisj a (mem_insert_of_mem ha) b
      (mem_insert_of_mem hb) hab]
    simp only [← card_neighborFinset_eq_degree]
    have heq' : ((insert j T).sup F).neighborFinset v =
        (F j).neighborFinset v ∪ (T.sup F).neighborFinset v := by
      ext u; simp only [mem_neighborFinset, mem_union, sup_insert, sup_adj]
    rw [heq', card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [mem_neighborFinset] at hu hu'
    obtain ⟨k, hk, hk'⟩ := (finsetSup_adj T).1 hu'
    have hjk : j ≠ k := fun h => hj (h ▸ hk)
    exact (disjoint_iff_inf_le.1 (hdisj j (mem_insert_self _ _) k (mem_insert_of_mem hk) hjk))
      ⟨hu, hk'⟩

/-- Degree of a near 1-factor. -/
theorem IsFactor.degree {G' : SimpleGraph V} {w m : V} {F : SimpleGraph V}
    (h : IsFactor G' w m F) (v : V) : F.degree v = if v ≠ w ∧ v ≠ m then 1 else 0 := by
  split_ifs with hv
  · obtain ⟨u, hu⟩ := h.covers v hv.1 hv.2
    exact degree_eq_one_of_matching h.matching (mem_cover.2 ⟨u, hu⟩)
  · apply degree_eq_zero_of_not_cover
    intro hc
    obtain ⟨u, hu⟩ := mem_cover.1 hc
    rcases not_and_or.1 hv with h1 | h1
    · rw [not_not] at h1; subst h1; exact h.miss_w u hu
    · rw [not_not] at h1; subst h1; exact h.miss_m u hu

/-- **Adding edge-disjoint matchings.** -/
theorem colorable_sup_family {B : SimpleGraph V} {F : ℕ → SimpleGraph V} (T : Finset ℕ)
    (hm : ∀ k ∈ T, IsMatchingGraph (F k)) (hB : ∀ k ∈ T, Disjoint B (F k))
    (hdisj : ∀ j ∈ T, ∀ k ∈ T, j ≠ k → Disjoint (F j) (F k)) {c : ℕ}
    (hc : B.lineGraph.Colorable c) : (B ⊔ T.sup F).lineGraph.Colorable (c + #T) := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.sup_empty, sup_bot_eq, card_empty, add_zero]; exact hc
  | insert j T hj ih =>
    have ih' := ih (fun k hk => hm k (mem_insert_of_mem hk))
      (fun k hk => hB k (mem_insert_of_mem hk))
      (fun a ha b hb hab => hdisj a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab)
    have hd : Disjoint (B ⊔ T.sup F) (F j) := by
      rw [disjoint_sup_left]
      refine ⟨hB j (mem_insert_self _ _), ?_⟩
      rw [Finset.disjoint_sup_left]
      intro k hk
      exact hdisj k (mem_insert_of_mem hk) j (mem_insert_self _ _) (fun h => hj (h ▸ hk))
    have := colorable_sup_matching hd (hm j (mem_insert_self _ _)) ih'
    have heq : B ⊔ (insert j T).sup F = B ⊔ T.sup F ⊔ F j := by
      rw [sup_insert, sup_comm (F j), ← sup_assoc]
    rw [card_insert_of_notMem hj, ← add_assoc, heq]
    exact this

end OneFactor
