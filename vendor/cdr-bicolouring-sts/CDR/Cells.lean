/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDR.DeWerra

/-!
# de Werra's theorem for sets of cells

A set of cells `E ⊆ N × N` is the bipartite graph `cellGraph E` between row copies and column
copies of `N`. If every row and every column has at most `b` cells of `E` and `|E| = b · d`, the
cells can be coloured with `b` colours, no colour repeating in a row or a column, each colour
used exactly `d` times (`deWerra_cells`).
-/

@[expose] public section

namespace CDR

open Finset LeanPool.Vizing.ColourClasses

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The bipartite graph of a set of cells: row `r` (left copy) is joined to column `g` (right
copy) when `(r, g)` is a cell. -/
def cellGraph (E : N → N → Prop) : SimpleGraph (N ⊕ N) where
  Adj x y := (∃ r g, x = .inl r ∧ y = .inr g ∧ E r g) ∨ (∃ r g, y = .inl r ∧ x = .inr g ∧ E r g)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨r, g, h1, h2, -⟩ | ⟨r, g, h1, h2, -⟩ <;> exact Sum.inl_ne_inr (h1.symm.trans h2)⟩

noncomputable instance (E : N → N → Prop) : DecidableRel (cellGraph E).Adj := Classical.decRel _

variable {E : N → N → Prop} [DecidableRel E]

@[simp] theorem cellGraph_adj_inl_inr {r g : N} : (cellGraph E).Adj (.inl r) (.inr g) ↔ E r g := by
  constructor
  · rintro (⟨r', g', h1, h2, h⟩ | ⟨r', g', h1, h2, -⟩)
    · obtain rfl := Sum.inl_injective h1
      obtain rfl := Sum.inr_injective h2
      exact h
    · exact absurd h1 Sum.inr_ne_inl
  · exact fun h => Or.inl ⟨r, g, rfl, rfl, h⟩

@[simp] theorem cellGraph_adj_inr_inl {r g : N} : (cellGraph E).Adj (.inr g) (.inl r) ↔ E r g := by
  rw [(cellGraph E).adj_comm]
  exact cellGraph_adj_inl_inr

@[simp] theorem cellGraph_not_adj_inl_inl {r r' : N} : ¬ (cellGraph E).Adj (.inl r) (.inl r') := by
  rintro (⟨_, _, _, h2, _⟩ | ⟨_, _, _, h2, _⟩) <;> exact Sum.inl_ne_inr h2

@[simp] theorem cellGraph_not_adj_inr_inr {g g' : N} : ¬ (cellGraph E).Adj (.inr g) (.inr g') := by
  rintro (⟨_, _, h1, _, _⟩ | ⟨_, _, h1, _, _⟩) <;> exact Sum.inr_ne_inl h1

variable (E) in
theorem cellGraph_colorable : (cellGraph E).Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk (Sum.elim (fun _ => 0) (fun _ => 1)) fun {x y} h => by
    rcases x with r | g <;> rcases y with r' | g' <;> simp_all⟩

theorem cellGraph_degree_inl (r : N) :
    (cellGraph E).degree (.inl r) = #(univ.filter fun g => E r g) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (cellGraph E).neighborFinset (.inl r) =
      (univ.filter fun g => E r g).map ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext x
    rcases x with r' | g <;> simp
  rw [this, card_map]

theorem cellGraph_degree_inr (g : N) :
    (cellGraph E).degree (.inr g) = #(univ.filter fun r => E r g) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (cellGraph E).neighborFinset (.inr g) =
      (univ.filter fun r => E r g).map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext x
    rcases x with r | g' <;> simp
  rw [this, card_map]

/-- The cells of `E` as a finset. -/
def cells (E : N → N → Prop) [DecidableRel E] : Finset (N × N) :=
  univ.filter fun p => E p.1 p.2

theorem mem_cells {p : N × N} : p ∈ cells E ↔ E p.1 p.2 := by
  simp [cells]

theorem sum_rows_eq_card_cells : ∑ r, #(univ.filter fun g => E r g) = #(cells E) := by
  rw [cells, card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun r _ => ?_
  refine card_bij (fun g _ => (r, g)) (fun g hg => by simpa using hg)
    (fun g _ g' _ h => (Prod.mk.inj h).2) ?_
  rintro ⟨r', g⟩ hp
  simp only [mem_filter, mem_univ, true_and] at hp
  obtain ⟨hE, rfl⟩ := hp
  exact ⟨g, by simpa using hE, rfl⟩

theorem sum_cols_eq_card_cells : ∑ g, #(univ.filter fun r => E r g) = #(cells E) := by
  rw [cells, card_eq_sum_card_fiberwise (f := Prod.snd) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun g _ => ?_
  refine card_bij (fun r _ => (r, g)) (fun r hr => by simpa using hr)
    (fun r _ r' _ h => (Prod.mk.inj h).1) ?_
  rintro ⟨r, g'⟩ hp
  simp only [mem_filter, mem_univ, true_and] at hp
  obtain ⟨hE, rfl⟩ := hp
  exact ⟨r, by simpa using hE, rfl⟩

theorem card_edgeFinset_cellGraph : #(cellGraph E).edgeFinset = #(cells E) := by
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges (cellGraph E)
  rw [Fintype.sum_sum_type] at h
  simp only [cellGraph_degree_inl, cellGraph_degree_inr] at h
  rw [sum_rows_eq_card_cells (E := E), sum_cols_eq_card_cells (E := E)] at h
  omega

/-- **de Werra for cells.** If every row and every column contains at most `b` cells of `E`
(`0 < b`) and `|E| = b · d`, the cells can be coloured with `b` colours, injectively along rows
and columns, each colour used exactly `d` times. -/
theorem deWerra_cells {b d : ℕ} (hb : 0 < b)
    (hrow : ∀ r, #(univ.filter fun g => E r g) ≤ b)
    (hcol : ∀ g, #(univ.filter fun r => E r g) ≤ b) (hcard : #(cells E) = b * d) :
    ∃ f : N → N → Fin b,
      (∀ r g g', E r g → E r g' → f r g = f r g' → g = g') ∧
      (∀ g r r', E r g → E r' g → f r g = f r' g → r = r') ∧
      ∀ i, #((cells E).filter fun p => f p.1 p.2 = i) = d := by
  have hdeg : (cellGraph E).maxDegree ≤ b := by
    refine (cellGraph E).maxDegree_le_of_forall_degree_le b fun x => ?_
    rcases x with r | g
    · rw [cellGraph_degree_inl]; exact hrow r
    · rw [cellGraph_degree_inr]; exact hcol g
  obtain ⟨colour, hproper, hclass⟩ := deWerra (cellGraph E) (cellGraph_colorable E) hb hdeg
    (by rw [card_edgeFinset_cellGraph, hcard])
  have hedge : ∀ {r g}, E r g → s(Sum.inl r, Sum.inr g) ∈ (cellGraph E).edgeFinset := by
    intro r g h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact cellGraph_adj_inl_inr.2 h
  refine ⟨fun r g => colour s(Sum.inl r, Sum.inr g), ?_, ?_, fun i => ?_⟩
  · intro r g g' h h' hf
    by_contra hne
    have hne' : s(Sum.inl r, Sum.inr g) ≠ s((Sum.inl r : N ⊕ N), Sum.inr g') := by
      intro heq
      rcases Sym2.eq_iff.1 heq with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hne (Sum.inr_injective h2)
      · exact Sum.inl_ne_inr h1
    have := hproper _ (hedge h) _ (hedge h') hne' hf
    exact Finset.disjoint_left.1 this (Sym2.mem_toFinset.2 (Sym2.mem_mk_left _ _))
      (Sym2.mem_toFinset.2 (Sym2.mem_mk_left _ _))
  · intro g r r' h h' hf
    by_contra hne
    have hne' : s(Sum.inl r, Sum.inr g) ≠ s((Sum.inl r' : N ⊕ N), Sum.inr g) := by
      intro heq
      rcases Sym2.eq_iff.1 heq with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hne (Sum.inl_injective h1)
      · exact Sum.inl_ne_inr h1
    have := hproper _ (hedge h) _ (hedge h') hne' hf
    exact Finset.disjoint_left.1 this (Sym2.mem_toFinset.2 (Sym2.mem_mk_right _ _))
      (Sym2.mem_toFinset.2 (Sym2.mem_mk_right _ _))
  · rw [← hclass i]
    refine card_bij (fun p _ => s(Sum.inl p.1, Sum.inr p.2)) (fun p hp => ?_) ?_ ?_
    · rw [mem_filter, mem_cells] at hp
      simp only [colourClass, mem_filter]
      exact ⟨hedge hp.1, hp.2⟩
    · rintro ⟨r, g⟩ _ ⟨r', g'⟩ _ h
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, -⟩
      · obtain rfl := Sum.inl_injective h1
        obtain rfl := Sum.inr_injective h2
        rfl
      · exact absurd h1 Sum.inl_ne_inr
    · intro e he
      simp only [colourClass, mem_filter, SimpleGraph.mem_edgeFinset] at he
      obtain ⟨he, hc⟩ := he
      induction e using Sym2.ind with
      | _ x y =>
        rw [SimpleGraph.mem_edgeSet] at he
        rcases x with r | g <;> rcases y with r' | g'
        · exact absurd he cellGraph_not_adj_inl_inl
        · exact ⟨(r, g'), mem_filter.2 ⟨mem_cells.2 (cellGraph_adj_inl_inr.1 he), hc⟩, rfl⟩
        · refine ⟨(r', g), mem_filter.2 ⟨mem_cells.2 (cellGraph_adj_inr_inl.1 he), ?_⟩,
            Sym2.eq_swap⟩
          simpa [Sym2.eq_swap] using hc
        · exact absurd he cellGraph_not_adj_inr_inr

end CDR
