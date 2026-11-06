/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Pivot
public import Overfull.Counting
public import Balanced.Bridge

/-!
# Adding matchings, and re-inserting a vertex of a regular graph

* `colorable_sup_matching`: a matching disjoint from `B` takes one new colour.
* `colorable_of_regular_keepAt`: if `G` is `d`-regular of even order and `G` minus the edges at
  `w` is `d`-edge-colourable, then so is `G`. In such a colouring every colour misses exactly one
  vertex other than `w` (count), so the neighbours of `w` miss distinct colours.
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset LeanPool.Vizing LeanPool.Vizing.PEC Overfull

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A matching (no two edges at a vertex). -/
def IsMatchingGraph (M : SimpleGraph V) : Prop := ∀ v a b, M.Adj v a → M.Adj v b → a = b

/-- A matching disjoint from `B` takes one more colour. -/
theorem colorable_sup_matching {B M : SimpleGraph V} (hdisj : Disjoint B M)
    (hM : IsMatchingGraph M) {k : ℕ} (hB : B.lineGraph.Colorable k) :
    (B ⊔ M).lineGraph.Colorable (k + 1) := by
  classical
  obtain ⟨C⟩ := hB
  have hmem : ∀ e : (B ⊔ M).edgeSet, e.1 ∉ M.edgeSet → e.1 ∈ B.edgeSet := fun e he => by
    obtain ⟨e, he'⟩ := e
    induction e using Sym2.inductionOn with
    | hf a b =>
      rw [mem_edgeSet, sup_adj] at he'
      rcases he' with h | h
      · exact h
      · exact absurd h he
  let col : (B ⊔ M).edgeSet → Fin (k + 1) := fun e =>
    if he : e.1 ∈ M.edgeSet then Fin.last k else (C ⟨e.1, hmem e he⟩).castSucc
  refine ⟨Coloring.mk col ?_⟩
  intro e f hef hcol
  rw [lineGraph_adj_iff_exists] at hef
  obtain ⟨hne, v, hve, hvf⟩ := hef
  simp only [col] at hcol
  by_cases he : e.1 ∈ M.edgeSet <;> by_cases hf : f.1 ∈ M.edgeSet
  · apply hne
    obtain ⟨e, he'⟩ := e
    obtain ⟨f, hf'⟩ := f
    obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.1 hve
    obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.1 hvf
    have := hM v a b ((mem_edgeSet M).1 he) ((mem_edgeSet M).1 hf)
    subst this
    rfl
  · rw [dif_pos he, dif_neg hf] at hcol
    exact (Fin.castSucc_lt_last _).ne' hcol
  · rw [dif_neg he, dif_pos hf] at hcol
    exact (Fin.castSucc_lt_last _).ne hcol
  · rw [dif_neg he, dif_neg hf] at hcol
    refine C.valid ?_ (Fin.castSucc_injective _ hcol)
    rw [lineGraph_adj_iff_exists]
    exact ⟨fun h => hne (Subtype.ext (Subtype.mk.inj h)), v, hve, hvf⟩

theorem keepAt_empty_adj (G : SimpleGraph V) (x : V) {a b : V} :
    (keepAt G x ∅).Adj a b ↔ G.Adj a b ∧ a ≠ x ∧ b ≠ x := by
  simp only [keepAt, deleteEdges_adj, Set.mem_setOf_eq, notMem_empty, IsEmpty.forall_iff,
    implies_true, and_true, Sym2.mem_iff, not_or]
  constructor
  · rintro ⟨h, h1, h2⟩; exact ⟨h, Ne.symm h1, Ne.symm h2⟩
  · rintro ⟨h, h1, h2⟩; exact ⟨h, Ne.symm h1, Ne.symm h2⟩

section Regular

open scoped Classical

variable (G : SimpleGraph V)

theorem degree_keepAt_empty_add (x : V) {v : V} (hv : v ≠ x) :
    (keepAt G x ∅).degree v + (if G.Adj v x then 1 else 0) = G.degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have h : (keepAt G x ∅).neighborFinset v = (G.neighborFinset v).erase x := by
    ext u
    rw [mem_neighborFinset, keepAt_empty_adj, mem_erase, mem_neighborFinset]
    tauto
  rw [h, card_erase_eq_ite]
  by_cases hvx : G.Adj v x
  · have hx : x ∈ G.neighborFinset v := (mem_neighborFinset _ _ _).2 hvx
    rw [if_pos hx, if_pos hvx]
    have := card_pos.2 ⟨x, hx⟩; omega
  · have hx : x ∉ G.neighborFinset v := fun h => hvx ((mem_neighborFinset _ _ _).1 h)
    rw [if_neg hx, if_neg hvx, add_zero]

theorem degree_keepAt_empty_self (x : V) : (keepAt G x ∅).degree x = 0 := by
  rw [← card_neighborFinset_eq_degree, card_eq_zero]
  ext u
  rw [mem_neighborFinset, keepAt_empty_adj]
  simp

/-- The sum of degrees after removing the edges at `x`. -/
theorem sum_degree_keepAt_empty (x : V) {d : ℕ} (hreg : ∀ v, G.degree v = d) :
    ∑ v, (keepAt G x ∅).degree v + 2 * d = Fintype.card V * d := by
  rw [← sum_erase_add _ _ (mem_univ x), degree_keepAt_empty_self, add_zero]
  have h1 : ∑ v ∈ univ.erase x, ((keepAt G x ∅).degree v + (if G.Adj v x then 1 else 0)) =
      ∑ v ∈ univ.erase x, d :=
    sum_congr rfl fun v hv => by rw [degree_keepAt_empty_add G x (ne_of_mem_erase hv), hreg]
  rw [sum_add_distrib, sum_const, card_erase_of_mem (mem_univ x), card_univ, smul_eq_mul] at h1
  have h2 : ∑ v ∈ univ.erase x, (if G.Adj v x then 1 else 0) = d := by
    rw [← hreg x, ← sum_filter, sum_const, smul_eq_mul, mul_one, ← card_neighborFinset_eq_degree]
    congr 1
    ext v
    simp only [mem_filter, mem_erase, mem_univ, and_true, mem_neighborFinset]
    constructor
    · rintro ⟨-, h⟩; exact h.symm
    · intro h; exact ⟨h.ne', h.symm⟩
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨x⟩
  have : (Fintype.card V - 1) * d + d = Fintype.card V * d := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]
  omega

/-- **Re-inserting a vertex of a regular graph of even order.** -/
theorem colorable_of_regular_keepAt {d : ℕ} (hev : Even (Fintype.card V))
    (hreg : ∀ v, G.degree v = d) (w : V) (hcol : (keepAt G w ∅).lineGraph.Colorable d) :
    G.lineGraph.Colorable d := by
  set G' := keepAt G w ∅
  obtain ⟨C⟩ := hcol
  set c := Balanced.ofColoring C
  have htot : ∀ u v, G'.Adj u v → c.col u v ≠ none := Balanced.total_ofColoring C
  -- missing colours
  have hmiss : ∀ v, #(missing c v) + G'.degree v = d := fun v => by
    have h := card_missing_add_colNbrs c v
    have : colNbrs c v = G'.neighborFinset v := by
      ext u; simp only [colNbrs, mem_filter, and_iff_left_iff_imp, mem_neighborFinset]
      exact fun h => htot v u h
    rwa [this, card_neighborFinset_eq_degree] at h
  -- every colour is free at exactly two vertices (one of them `w`)
  have hnf : ∀ θ : Fin d, #(univ.filter fun v => ¬ c.IsFree v θ) = Fintype.card V - 2 := by
    have hle : ∀ θ : Fin d, #(univ.filter fun v => ¬ c.IsFree v θ) ≤ Fintype.card V - 2 := by
      intro θ
      have hsub : (univ.filter fun v => ¬ c.IsFree v θ) ⊆ univ.erase w := by
        intro v hv
        refine mem_erase.2 ⟨fun h => ?_, mem_univ v⟩
        subst h
        apply (mem_filter.1 hv).2
        intro u hu
        have := c.col_adj hu
        rw [keepAt_empty_adj] at this
        exact this.2.1 rfl
      have h1 := card_le_card hsub
      rw [card_erase_of_mem (mem_univ w), card_univ] at h1
      have h2 := even_card_not_free c θ
      obtain ⟨t, ht⟩ := hev
      obtain ⟨r, hr⟩ := h2
      omega
    have hsum : ∑ θ : Fin d, #(univ.filter fun v => ¬ c.IsFree v θ) =
        ∑ v, G'.degree v := by
      simp only [card_filter]
      rw [sum_comm]
      refine sum_congr rfl fun v _ => ?_
      have h := hmiss v
      have h2 := card_filter_add_card_filter_not (s := (univ : Finset (Fin d)))
        (p := fun θ => c.IsFree v θ)
      rw [card_univ, Fintype.card_fin] at h2
      rw [← card_filter]
      have : missing c v = univ.filter fun θ => c.IsFree v θ := by
        ext θ; rw [mem_missing]; simp
      rw [this] at h
      omega
    have htot' := sum_degree_keepAt_empty G w hreg
    intro θ
    by_contra hne
    have hlt : #(univ.filter fun v => ¬ c.IsFree v θ) < Fintype.card V - 2 :=
      lt_of_le_of_ne (hle θ) hne
    have : ∑ θ : Fin d, #(univ.filter fun v => ¬ c.IsFree v θ) <
        ∑ _θ : Fin d, (Fintype.card V - 2) :=
      sum_lt_sum (fun θ _ => hle θ) ⟨θ, mem_univ _, hlt⟩
    rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, hsum] at this
    have h2 : (Fintype.card V - 2) * d + 2 * d = Fintype.card V * d := by
      rcases Nat.lt_or_ge (Fintype.card V) 2 with h | h
      · have := hle θ; omega
      · rw [mul_comm 2 d, mul_comm (Fintype.card V - 2) d, mul_comm (Fintype.card V) d,
          ← Nat.mul_add, Nat.sub_add_cancel h]
    nlinarith
  -- uniqueness of the free vertex
  have huniq : ∀ θ u u', u ≠ w → u' ≠ w → c.IsFree u θ → c.IsFree u' θ → u = u' := by
    intro θ u u' hu hu' hfu hfu'
    have hw : c.IsFree w θ := fun z hz => by
      have := c.col_adj hz; rw [keepAt_empty_adj] at this; exact this.2.1 rfl
    have h2 := card_filter_add_card_filter_not (s := (univ : Finset V))
      (p := fun v => c.IsFree v θ)
    rw [hnf θ, card_univ] at h2
    by_contra hne
    have : ({w, u, u'} : Finset V) ⊆ univ.filter fun v => c.IsFree v θ := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> simp [*]
    have h3 := card_le_card this
    rw [card_insert_of_notMem (by simp [Ne.symm hu, Ne.symm hu']), card_pair hne] at h3
    have := Fintype.card_pos_iff.2 ⟨w⟩
    have : 2 ≤ Fintype.card V := by
      have := card_le_univ ({u, u'} : Finset V); rw [card_pair hne] at this; omega
    omega
  -- the colour missing at a neighbour of `w`
  have hex : ∀ u, G.Adj w u → ∃ θ, c.IsFree u θ := fun u hu => by
    have h := hmiss u
    have h2 : G'.degree u + 1 = d := by
      have := degree_keepAt_empty_add G w hu.ne'
      rw [if_pos hu.symm, hreg] at this
      exact this
    obtain ⟨θ, hθ⟩ := card_pos.1 (show 0 < #(missing c u) by omega)
    exact ⟨θ, mem_missing.1 hθ⟩
  let m : ∀ u, G.Adj w u → Fin d := fun u h => (hex u h).choose
  have hm : ∀ u (h : G.Adj w u), c.IsFree u (m u h) := fun u h => (hex u h).choose_spec
  let col : V → V → Option (Fin d) := fun a b =>
    if a = w then (if h : G.Adj w b then some (m b h) else none)
    else if b = w then (if h : G.Adj w a then some (m a h) else none) else c.col a b
  have hcol_w : ∀ b, col w b = if h : G.Adj w b then some (m b h) else none := fun b => by
    simp [col]
  have hcol_w' : ∀ a, a ≠ w → col a w = if h : G.Adj w a then some (m a h) else none :=
    fun a ha => by simp [col, ha]
  have hcol_o : ∀ a b, a ≠ w → b ≠ w → col a b = c.col a b := fun a b ha hb => by
    simp [col, ha, hb]
  have hfree_w : ∀ a, a ≠ w → ∀ γ, (if h : G.Adj w a then some (m a h) else none) = some γ →
      c.IsFree a γ := fun a ha γ h => by
    split_ifs at h with hwa
    · rw [← Option.some.inj h]; exact hm a hwa
  have hsymm : ∀ a b, col a b = col b a := by
    intro a b
    by_cases ha : a = w <;> by_cases hb : b = w
    · subst ha; subst hb; rfl
    · subst ha; rw [hcol_w, hcol_w' b hb]
    · subst hb; rw [hcol_w, hcol_w' a ha]
    · rw [hcol_o a b ha hb, hcol_o b a hb ha, c.col_symm]
  have hadj : ∀ {a b γ}, col a b = some γ → G.Adj a b := by
    intro a b γ h
    by_cases ha : a = w
    · subst ha; rw [hcol_w] at h; split_ifs at h with hh; exact hh
    · by_cases hb : b = w
      · subst hb; rw [hcol_w' a ha] at h; split_ifs at h with hh; exact hh.symm
      · rw [hcol_o a b ha hb] at h
        exact ((keepAt_empty_adj G w).1 (c.col_adj h)).1
  have hproper : ∀ {a b b' γ}, col a b = some γ → col a b' = some γ → b = b' := by
    intro a b b' γ h1 h2
    by_cases ha : a = w
    · subst ha
      rw [hcol_w] at h1 h2
      split_ifs at h1 h2 with hb hb'
      have e1 := Option.some.inj h1
      have e2 := Option.some.inj h2
      exact huniq γ b b' hb.ne' hb'.ne' (e1 ▸ hm b hb) (e2 ▸ hm b' hb')
    · by_cases hb : b = w <;> by_cases hb' : b' = w
      · rw [hb, hb']
      · rw [hb, hcol_w' a ha] at h1
        rw [hcol_o a b' ha hb'] at h2
        exact absurd h2 (hfree_w a ha γ h1 b')
      · rw [hb', hcol_w' a ha] at h2
        rw [hcol_o a b ha hb] at h1
        exact absurd h1 (hfree_w a ha γ h2 b)
      · rw [hcol_o a b ha hb] at h1
        rw [hcol_o a b' ha hb'] at h2
        exact c.col_proper h1 h2
  let cG : PEC G (Fin d) := ⟨col, hsymm, hadj, hproper⟩
  have htotG : ∀ u v, G.Adj u v → cG.col u v ≠ none := by
    intro u v huv
    show col u v ≠ none
    by_cases hu : u = w
    · subst hu; rw [hcol_w, dif_pos huv]; exact Option.some_ne_none _
    · by_cases hv : v = w
      · subst hv; rw [hcol_w' u hu, dif_pos huv.symm]; exact Option.some_ne_none _
      · rw [hcol_o u v hu hv]
        exact htot u v ((keepAt_empty_adj G w).2 ⟨huv, hu, hv⟩)
  exact ⟨cG.lineGraphColoring htotG⟩

end Regular

end OneFactor
