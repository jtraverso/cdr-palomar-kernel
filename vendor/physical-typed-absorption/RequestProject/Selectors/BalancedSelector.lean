/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Selectors.RandomExpansion
public import RequestProject.Selectors.BalancedHall

@[expose] public section

/-!
# The balanced selector with uniform linear resources

Ports `U_L = Fin l`, `U_R = Fin r`, `k = max l r ≥ 1`, auxiliaries `A = B = Fin (4k)`.
A sample `ω = ((π, τ), (σ, υ))` consists of four `20`-tuples of permutations of `Fin (4k)`.
Round `i` joins `a ∈ A` to `π i a`, the left port `p` to `τ i p` (an injection `U_L → B`),
`b ∈ B` to `σ i b` and the right port `q` to `υ i q` (an injection `U_R → A`).

* `selGraph_degree_le`, `selGraph_card_edgeFinset_le`, `selGraph_bipartite` hold for EVERY
  sample (deterministic bounds: degree `≤ 60`, at most `200 k` edges, bipartite between
  `A ⊕ U_L` and `B ⊕ U_R`).
* `exists_good_sample` : some sample has small-set expansion on both sides (union bound).
* `selGraph_modes_of_good` : for a good sample, every balanced pair `|S_L| = |S_R|` gives a
  perfect matching of the graph induced on `A ∪ B ∪ S_L ∪ S_R` (Hall).
* `balancedSelector_exists` : the endpoint.  Expansion is proved, not assumed.
-/

namespace SelBalanced

open Finset SelRandom SelBound SelHall

open Classical

/-- The vertex type: `(A ⊕ U_L) ⊕ (B ⊕ U_R)` with `|A| = |B| = 4 max(l,r)`. -/
abbrev BV (l r : ℕ) := (Fin (4 * max l r) ⊕ Fin l) ⊕ (Fin (4 * max l r) ⊕ Fin r)

/-- A sample: `((π, τ), (σ, υ))`. -/
abbrev Sample (N : ℕ) := (Rounds N × Rounds N) × (Rounds N × Rounds N)

lemma le_four_max_left (l r : ℕ) : l ≤ 4 * max l r := by
  have := le_max_left l r; omega

lemma le_four_max_right (l r : ℕ) : r ≤ 4 * max l r := by
  have := le_max_right l r; omega

/-- Port embedding on the left. -/
def eL (l r : ℕ) : Fin l ↪ Fin (4 * max l r) := Fin.castLEEmb (le_four_max_left l r)
/-- Port embedding on the right. -/
def eR (l r : ℕ) : Fin r ↪ Fin (4 * max l r) := Fin.castLEEmb (le_four_max_right l r)

/-- The edge relation of the sampled selector (left vertex, right vertex). -/
def selRel (l r : ℕ) (ω : Sample (4 * max l r)) :
    Fin (4 * max l r) ⊕ Fin l → Fin (4 * max l r) ⊕ Fin r → Prop := fun x y =>
  (∃ i, y = Sum.inl (img (eL l r) ω.1.1 ω.1.2 i x)) ∨
  (∃ i, x = Sum.inl (img (eR l r) ω.2.1 ω.2.2 i y))

/-- The sampled selector graph. -/
def selGraph (l r : ℕ) (ω : Sample (4 * max l r)) : SimpleGraph (BV l r) :=
  bipGraph (selRel l r ω)

/-- Auxiliaries and the active ports: `A ∪ B ∪ S_L ∪ S_R`. -/
def activeVerts {l r : ℕ} (SL : Finset (Fin l)) (SR : Finset (Fin r)) : Finset (BV l r) :=
  ((univ : Finset (Fin (4 * max l r))).disjSum SL).map Function.Embedding.inl ∪
    ((univ : Finset (Fin (4 * max l r))).disjSum SR).map Function.Embedding.inr

lemma mem_activeVerts {l r : ℕ} (SL : Finset (Fin l)) (SR : Finset (Fin r)) (v : BV l r) :
    v ∈ activeVerts SL SR ↔
      (∃ a, v = Sum.inl (Sum.inl a)) ∨ (∃ b, v = Sum.inr (Sum.inl b)) ∨
      (∃ p ∈ SL, v = Sum.inl (Sum.inr p)) ∨ (∃ q ∈ SR, v = Sum.inr (Sum.inr q)) := by
  rcases v with (a | p) | (b | q) <;> simp [activeVerts]

/-! ### Deterministic bounds (every sample) -/

theorem selGraph_bipartite (l r : ℕ) (ω : Sample (4 * max l r)) (u v : BV l r)
    (h : (selGraph l r ω).Adj u v) :
    (u.isLeft ∧ v.isRight) ∨ (u.isRight ∧ v.isLeft) := by
  rcases u with x | y <;> rcases v with x' | y' <;> simp_all [selGraph, bipGraph, bAdj]

/-- Candidate neighbours of `v` created in round `i` (at most three). -/
def roundNbrs (l r : ℕ) (ω : Sample (4 * max l r)) (i : Fin 20) : BV l r → Finset (BV l r)
  | Sum.inl (Sum.inl a) =>
      {Sum.inr (Sum.inl (ω.1.1 i a)), Sum.inr (Sum.inl ((ω.2.1 i).symm a))} ∪
        (univ.filter (fun q : Fin r => eR l r q = (ω.2.2 i).symm a)).image
          (fun q => Sum.inr (Sum.inr q))
  | Sum.inl (Sum.inr p) => {Sum.inr (Sum.inl (ω.1.2 i (eL l r p)))}
  | Sum.inr (Sum.inl b) =>
      {Sum.inl (Sum.inl ((ω.1.1 i).symm b)), Sum.inl (Sum.inl (ω.2.1 i b))} ∪
        (univ.filter (fun p : Fin l => eL l r p = (ω.1.2 i).symm b)).image
          (fun p => Sum.inl (Sum.inr p))
  | Sum.inr (Sum.inr q) => {Sum.inl (Sum.inl (ω.2.2 i (eR l r q)))}

lemma card_filter_emb_le {α β : Type*} [Fintype α] (e : α ↪ β) (c : β)
    [DecidablePred (fun x => e x = c)] :
    (univ.filter (fun x => e x = c)).card ≤ 1 := by
  rw [card_le_one]
  intro x hx y hy
  simp only [mem_filter, mem_univ, true_and] at hx hy
  exact e.injective (hx.trans hy.symm)

lemma card_roundNbrs_le (l r : ℕ) (ω : Sample (4 * max l r)) (i : Fin 20) (v : BV l r) :
    (roundNbrs l r ω i v).card ≤ 3 := by
  rcases v with (a | p) | (b | q)
  · refine (card_union_le _ _).trans ?_
    have h1 := card_insert_le (Sum.inr (Sum.inl (ω.1.1 i a)) : BV l r)
      {Sum.inr (Sum.inl ((ω.2.1 i).symm a))}
    have h2 := (card_image_le (f := fun q => (Sum.inr (Sum.inr q) : BV l r))
      (s := univ.filter (fun q : Fin r => eR l r q = (ω.2.2 i).symm a))).trans
      (card_filter_emb_le (eR l r) _)
    have h1' := h1.trans_eq (by rw [card_singleton])
    omega
  · simp [roundNbrs]
  · refine (card_union_le _ _).trans ?_
    have h1 := card_insert_le (Sum.inl (Sum.inl ((ω.1.1 i).symm b)) : BV l r)
      {Sum.inl (Sum.inl (ω.2.1 i b))}
    have h2 := (card_image_le (f := fun p => (Sum.inl (Sum.inr p) : BV l r))
      (s := univ.filter (fun p : Fin l => eL l r p = (ω.1.2 i).symm b))).trans
      (card_filter_emb_le (eL l r) _)
    have h1' := h1.trans_eq (by rw [card_singleton])
    omega
  · simp [roundNbrs]

lemma adj_mem_roundNbrs (l r : ℕ) (ω : Sample (4 * max l r)) (v w : BV l r)
    (h : (selGraph l r ω).Adj v w) : ∃ i, w ∈ roundNbrs l r ω i v := by
  rcases v with (a | p) | (b | q) <;> rcases w with (a' | p') | (b' | q') <;>
    simp only [selGraph, bipGraph, bAdj, selRel, img] at h
  · -- `a ~ b'`
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
    · simp only [Sum.elim_inl, Sum.inl.injEq] at hi
      exact ⟨i, by simp [roundNbrs, hi]⟩
    · simp only [Sum.elim_inl, Sum.inl.injEq] at hi
      exact ⟨i, by simp [roundNbrs, hi]⟩
  · -- `a ~ q'`
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
    · simp at hi
    · simp only [Sum.elim_inr, Sum.inl.injEq] at hi
      refine ⟨i, ?_⟩
      simp only [roundNbrs, mem_union, mem_insert, mem_singleton, mem_image, mem_filter,
        mem_univ, true_and]
      right; exact ⟨q', by rw [hi]; simp, rfl⟩
  · -- `p ~ b'`
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
    · simp only [Sum.elim_inr, Sum.inl.injEq] at hi
      exact ⟨i, by simp [roundNbrs, hi]⟩
    · simp at hi
  · -- `p ~ q'`
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> simp at hi
  · -- `b ~ a'`
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
    · simp only [Sum.elim_inl, Sum.inl.injEq] at hi
      exact ⟨i, by simp [roundNbrs, hi]⟩
    · simp only [Sum.elim_inl, Sum.inl.injEq] at hi
      exact ⟨i, by simp [roundNbrs, hi]⟩
  · -- `b ~ p'`
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
    · simp only [Sum.elim_inr, Sum.inl.injEq] at hi
      refine ⟨i, ?_⟩
      simp only [roundNbrs, mem_union, mem_insert, mem_singleton, mem_image, mem_filter,
        mem_univ, true_and]
      right; exact ⟨p', by rw [hi]; simp, rfl⟩
    · simp at hi
  · -- `q ~ a'`
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩
    · simp at hi
    · simp only [Sum.elim_inr, Sum.inl.injEq] at hi
      exact ⟨i, by simp [roundNbrs, hi]⟩
  · -- `q ~ p'`
    rcases h with ⟨i, hi⟩ | ⟨i, hi⟩ <;> simp at hi

/-- **Degree bound** (every sample): maximum degree `≤ 60`. -/
theorem selGraph_degree_le (l r : ℕ) (ω : Sample (4 * max l r)) (v : BV l r) :
    (selGraph l r ω).degree v ≤ 60 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : (selGraph l r ω).neighborFinset v ⊆
      (univ : Finset (Fin 20)).biUnion (fun i => roundNbrs l r ω i v) := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    obtain ⟨i, hi⟩ := adj_mem_roundNbrs l r ω v w hw
    exact mem_biUnion.mpr ⟨i, mem_univ _, hi⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ i : Fin 20, (roundNbrs l r ω i v).card := card_biUnion_le
    _ ≤ ∑ _i : Fin 20, 3 := sum_le_sum fun i _ => card_roundNbrs_le l r ω i v
    _ = 60 := by simp

theorem selGraph_maxDegree_le (l r : ℕ) (ω : Sample (4 * max l r)) :
    (selGraph l r ω).maxDegree ≤ 60 :=
  SimpleGraph.maxDegree_le_of_forall_degree_le _ _ (selGraph_degree_le l r ω)

/-- Edge slots: one per round and per vertex of the sampling side. -/
def edgeSlot (l r : ℕ) (ω : Sample (4 * max l r)) :
    (Fin 20 × (Fin (4 * max l r) ⊕ Fin l)) ⊕ (Fin 20 × (Fin (4 * max l r) ⊕ Fin r)) →
      Sym2 (BV l r)
  | Sum.inl (i, x) => s(Sum.inl x, Sum.inr (Sum.inl (img (eL l r) ω.1.1 ω.1.2 i x)))
  | Sum.inr (i, y) => s(Sum.inl (Sum.inl (img (eR l r) ω.2.1 ω.2.2 i y)), Sum.inr y)

/-- **Edge bound** (every sample): at most `200 max(l,r)` edges. -/
theorem selGraph_card_edgeFinset_le (l r : ℕ) (ω : Sample (4 * max l r)) :
    (selGraph l r ω).edgeFinset.card ≤ 200 * max l r := by
  have hsub : (selGraph l r ω).edgeFinset ⊆ univ.image (edgeSlot l r ω) := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      simp only [mem_image, mem_univ, true_and]
      rcases u with x | y <;> rcases v with x' | y' <;>
        simp only [selGraph, bipGraph, bAdj, selRel] at he
      · rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · exact ⟨Sum.inl (i, x), rfl⟩
        · exact ⟨Sum.inr (i, y'), rfl⟩
      · rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · exact ⟨Sum.inl (i, x'), Sym2.eq_swap⟩
        · exact ⟨Sum.inr (i, y), Sym2.eq_swap⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ = 20 * (4 * max l r + l) + 20 * (4 * max l r + r) := by
        simp [Fintype.card_sum, Fintype.card_prod]
    _ ≤ 200 * max l r := by
        have := le_max_left l r; have := le_max_right l r; omega

/-! ### A good sample exists -/

/-- A sample is good if both sides expand. -/
def Good (l r : ℕ) (ω : Sample (4 * max l r)) : Prop :=
  ¬ Bad (eL l r) (window (max l r)) ω.1 ∧ ¬ Bad (eR l r) (window (max l r)) ω.2

theorem exists_good_sample (l r : ℕ) (hk : 1 ≤ max l r) :
    ∃ ω : Sample (4 * max l r), Good l r ω := by
  have hbL := card_bad_le (max l r) hk (by simp) (eL l r)
  have hbR := card_bad_le (max l r) hk (by simp) (eR l r)
  set Q : ℝ := ((4 * max l r).factorial : ℝ) ^ 40 with hQ
  have hQpos : 0 < Q := by positivity
  have hcardR : (Fintype.card (Rounds (4 * max l r) × Rounds (4 * max l r)) : ℝ) = Q := by
    rw [hQ, Fintype.card_prod, Fintype.card_fun, Fintype.card_perm, Fintype.card_fin,
      Fintype.card_fin]
    push_cast; ring
  by_contra hno
  push_neg at hno
  have hcover : (univ : Finset (Sample (4 * max l r))) ⊆
      ((univ.filter (fun ω : Rounds (4 * max l r) × Rounds (4 * max l r) =>
          Bad (eL l r) (window (max l r)) ω)) ×ˢ univ) ∪
      (univ ×ˢ (univ.filter (fun ω : Rounds (4 * max l r) × Rounds (4 * max l r) =>
          Bad (eR l r) (window (max l r)) ω))) := by
    intro ω _
    have := hno ω
    simp only [Good, not_and_or, not_not] at this
    rcases this with h | h
    · exact mem_union_left _ (mem_product.mpr ⟨by simpa using h, mem_univ _⟩)
    · exact mem_union_right _ (mem_product.mpr ⟨mem_univ _, by simpa using h⟩)
  have h1 := card_le_card hcover
  have h2 := h1.trans (card_union_le _ _)
  rw [card_product, card_product, card_univ, card_univ, Fintype.card_prod] at h2
  have h3 : (Fintype.card (Rounds (4 * max l r) × Rounds (4 * max l r)) : ℝ) *
      Fintype.card (Rounds (4 * max l r) × Rounds (4 * max l r)) ≤
      ((univ.filter (fun ω : Rounds (4 * max l r) × Rounds (4 * max l r) =>
          Bad (eL l r) (window (max l r)) ω)).card : ℝ) * Fintype.card (Rounds (4 * max l r) × Rounds (4 * max l r)) +
      (Fintype.card (Rounds (4 * max l r) × Rounds (4 * max l r)) : ℝ) *
      ((univ.filter (fun ω : Rounds (4 * max l r) × Rounds (4 * max l r) =>
          Bad (eR l r) (window (max l r)) ω)).card : ℝ) := by
    exact_mod_cast h2
  rw [hcardR] at h3
  nlinarith

/-! ### All balanced modes of a good sample -/

theorem selGraph_modes_of_good (l r : ℕ) (ω : Sample (4 * max l r))
    (hω : Good l r ω) (SL : Finset (Fin l)) (SR : Finset (Fin r)) (hS : SL.card = SR.card) :
    ∃ Mt : (selGraph l r ω).Subgraph, Mt.verts = ↑(activeVerts SL SR) ∧ Mt.IsMatching := by
  have hexpL : ∀ X : Finset (Fin (4 * max l r) ⊕ Fin l), X.card ≤ window (max l r) →
      X.card ≤ (nbB (selRel l r ω) X).card := by
    intro X hX
    have hnb : ¬ (nbr (eL l r) ω.1.1 ω.1.2 X).card < X.card := fun h => hω.1 ⟨X, hX, h⟩
    refine (not_lt.mp hnb).trans (card_le_card ?_)
    intro b hb
    simp only [nbr, mem_filter, mem_univ, true_and] at hb
    obtain ⟨x, hx, i, rfl⟩ := hb
    simp only [nbB, mem_filter, mem_univ, true_and]
    exact ⟨x, hx, Or.inl ⟨i, rfl⟩⟩
  have hexpR : ∀ Y : Finset (Fin (4 * max l r) ⊕ Fin r), Y.card ≤ window (max l r) →
      Y.card ≤ (nbA (selRel l r ω) Y).card := by
    intro Y hY
    have hnb : ¬ (nbr (eR l r) ω.2.1 ω.2.2 Y).card < Y.card := fun h => hω.2 ⟨Y, hY, h⟩
    refine (not_lt.mp hnb).trans (card_le_card ?_)
    intro a ha
    simp only [nbr, mem_filter, mem_univ, true_and] at ha
    obtain ⟨y, hy, i, rfl⟩ := ha
    simp only [nbA, mem_filter, mem_univ, true_and]
    exact ⟨y, hy, Or.inr ⟨i, rfl⟩⟩
  have hM : Fintype.card (Fin (4 * max l r)) + Fintype.card (Fin l) + 1 ≤ 2 * window (max l r) := by
    simp only [Fintype.card_fin, window]
    have := le_max_left l r; omega
  exact balanced_mode_of_expansion (selRel l r ω) (window (max l r)) (by simp) hM hexpL hexpR
    SL SR hS

/-- **Balanced selector, uniform linear resources.**  For port sets `Fin l`, `Fin r` with
`k = max l r ≥ 1` there is ONE bipartite graph on `(A ⊕ U_L) ⊕ (B ⊕ U_R)`,
`|A| = |B| = 4k`, with maximum degree `≤ 60` and at most `200 k` edges, such that for EVERY
`S_L ⊆ U_L`, `S_R ⊆ U_R` with `|S_L| = |S_R|` the graph has a matching subgraph whose vertex
set is exactly `A ∪ B ∪ S_L ∪ S_R` (a perfect matching of the induced subgraph). -/
theorem balancedSelector_exists (l r : ℕ) (hk : 1 ≤ max l r) :
    ∃ G : SimpleGraph (BV l r),
      (∀ u v, G.Adj u v → (u.isLeft ∧ v.isRight) ∨ (u.isRight ∧ v.isLeft)) ∧
      (∀ v, G.degree v ≤ 60) ∧ G.maxDegree ≤ 60 ∧
      G.edgeFinset.card ≤ 200 * max l r ∧
      ∀ (SL : Finset (Fin l)) (SR : Finset (Fin r)), SL.card = SR.card →
        ∃ Mt : G.Subgraph, Mt.verts = ↑(activeVerts SL SR) ∧ Mt.IsMatching := by
  obtain ⟨ω, hω⟩ := exists_good_sample l r hk
  exact ⟨selGraph l r ω, selGraph_bipartite l r ω, selGraph_degree_le l r ω,
    selGraph_maxDegree_le l r ω, selGraph_card_edgeFinset_le l r ω,
    selGraph_modes_of_good l r ω hω⟩

end SelBalanced
