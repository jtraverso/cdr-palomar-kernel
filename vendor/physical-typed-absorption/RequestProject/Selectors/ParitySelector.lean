/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# The linear parity selector

For `r` ports `u_i` and `2r` auxiliaries `a_i, b_i` (`0 ≤ i < r`) we build the simple graph
with edges `a_i b_i`, `u_i a_i`, `u_i b_i` (`i < r`) and `b_i a_(i+1)` (`i + 1 < r`).

* `paritySelector_degree_le` : every degree is `≤ 3` (and `paritySelector_maxDegree_le`).
* `paritySelector_card_edgeFinset_le` : at most `4 r` edges.
* `paritySelector_even_mode` : for EVERY even set `S` of ports there is a matching subgraph
  of the (fixed, `S`-independent) graph whose vertex set is exactly the auxiliaries together
  with the ports of `S`.  The matching is built from the prefix-parity carry
  `carry S i = |S ∩ [0,i)| mod 2`.
* `paritySelector_even_mode_edges` : the same mode as a genuine `Finset (Sym2 _)` of graph
  edges, every covered vertex lying in exactly one edge and no other vertex in any edge.
-/

namespace ParitySel

open Finset

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Vertices: ports `u_i` (left summand), auxiliaries `a_i` and `b_i`. -/
abbrev PV (r : ℕ) := Fin r ⊕ (Fin r ⊕ Fin r)

/-- port `u_i` -/
abbrev pu {r : ℕ} (i : Fin r) : PV r := Sum.inl i
/-- auxiliary `a_i` -/
abbrev pa {r : ℕ} (i : Fin r) : PV r := Sum.inr (Sum.inl i)
/-- auxiliary `b_i` -/
abbrev pb {r : ℕ} (i : Fin r) : PV r := Sum.inr (Sum.inr i)

/-- Oriented edge list: `u_i a_i`, `u_i b_i`, `a_i b_i`, `b_i a_(i+1)`. -/
def pe {r : ℕ} : PV r → PV r → Bool
  | Sum.inl i, Sum.inr (Sum.inl j) => decide (i = j)
  | Sum.inl i, Sum.inr (Sum.inr j) => decide (i = j)
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr j) => decide (i = j)
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inl j) => decide (j.val = i.val + 1)
  | _, _ => false

lemma pe_irrefl {r : ℕ} (x : PV r) : pe x x = false := by
  rcases x with i | i | i <;> simp [pe]

/-- The parity selector graph. -/
def paritySelector (r : ℕ) : SimpleGraph (PV r) where
  Adj x y := pe x y = true ∨ pe y x = true
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun x h => by simp [pe_irrefl] at h⟩

instance (r : ℕ) : DecidableRel (paritySelector r).Adj := fun x y => by
  unfold paritySelector; infer_instance

/-- The auxiliary vertices. -/
def auxSet (r : ℕ) : Finset (PV r) := univ.filter (fun x => x.isRight)

/-- The ports of a set `S`. -/
def portSet {r : ℕ} (S : Finset (Fin r)) : Finset (PV r) := S.map Function.Embedding.inl

/-! ### Degree and edge bounds -/

lemma neighborFinset_pu_sub {r : ℕ} (i : Fin r) :
    (paritySelector r).neighborFinset (pu i) ⊆ {pa i, pb i} := by
  intro y hy
  rw [SimpleGraph.mem_neighborFinset] at hy
  rcases y with j | j | j
  · simp [paritySelector, pe] at hy
  · simp only [paritySelector, pe, decide_eq_true_eq, Bool.false_eq_true, or_false] at hy
    subst hy; simp
  · simp only [paritySelector, pe, decide_eq_true_eq, Bool.false_eq_true, or_false] at hy
    subst hy; simp

lemma neighborFinset_pa_sub {r : ℕ} (i : Fin r) :
    (paritySelector r).neighborFinset (pa i) ⊆ {pu i, pb i, pb ⟨i.val - 1, by omega⟩} := by
  intro y hy
  rw [SimpleGraph.mem_neighborFinset] at hy
  rcases y with j | j | j
  · simp only [paritySelector, pe, decide_eq_true_eq, Bool.false_eq_true, false_or] at hy
    subst hy; simp
  · simp [paritySelector, pe] at hy
  · simp only [paritySelector, pe, decide_eq_true_eq] at hy
    simp only [mem_insert, mem_singleton, Sum.inr.injEq, reduceCtorEq, false_or]
    rcases hy with h | h
    · exact Or.inl h.symm
    · right; ext; simp; omega

lemma neighborFinset_pb_sub {r : ℕ} (i : Fin r) :
    (paritySelector r).neighborFinset (pb i) ⊆
      {pu i, pa i} ∪ (univ.filter (fun j : Fin r => j.val = i.val + 1)).image pa := by
  intro y hy
  rw [SimpleGraph.mem_neighborFinset] at hy
  rcases y with j | j | j
  · simp only [paritySelector, pe, decide_eq_true_eq, Bool.false_eq_true, false_or] at hy
    subst hy; simp
  · simp only [paritySelector, pe, decide_eq_true_eq] at hy
    simp only [mem_union, mem_insert, mem_singleton, reduceCtorEq, Sum.inr.injEq,
      Sum.inl.injEq, false_or, mem_image, mem_filter, mem_univ, true_and]
    rcases hy with h | h
    · exact Or.inr ⟨j, h, rfl⟩
    · exact Or.inl h
  · simp [paritySelector, pe] at hy

lemma card_filter_val_eq_le {r : ℕ} (m : ℕ) :
    (univ.filter (fun j : Fin r => j.val = m)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [mem_filter, mem_univ, true_and] at ha hb
  exact Fin.ext (ha.trans hb.symm)

theorem paritySelector_degree_le (r : ℕ) (v : PV r) : (paritySelector r).degree v ≤ 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rcases v with i | i | i
  · exact (card_le_card (neighborFinset_pu_sub i)).trans
      ((card_insert_le _ _).trans (by simp))
  · exact (card_le_card (neighborFinset_pa_sub i)).trans
      ((card_insert_le _ _).trans (by
        have := card_insert_le (pb i) {pb ⟨i.val - 1, by omega⟩}
        simp only [card_singleton] at this; omega))
  · refine (card_le_card (neighborFinset_pb_sub i)).trans ?_
    refine (card_union_le _ _).trans ?_
    have h1 := card_insert_le (pu i) {pa i}
    have h2 := (card_image_le (s := univ.filter (fun j : Fin r => j.val = i.val + 1))
      (f := pa)).trans (card_filter_val_eq_le (r := r) (i.val + 1))
    simp only [card_singleton] at h1
    omega

theorem paritySelector_maxDegree_le (r : ℕ) : (paritySelector r).maxDegree ≤ 3 :=
  SimpleGraph.maxDegree_le_of_forall_degree_le _ _ (paritySelector_degree_le r)

/-- Four edge slots per index `i`. -/
def edgeSlot {r : ℕ} (p : Fin r × Fin 4) : Sym2 (PV r) :=
  match p.2 with
  | 0 => s(pu p.1, pa p.1)
  | 1 => s(pu p.1, pb p.1)
  | 2 => s(pa p.1, pb p.1)
  | 3 => s(pb ⟨p.1.val - 1, by omega⟩, pa p.1)

theorem paritySelector_card_edgeFinset_le (r : ℕ) :
    (paritySelector r).edgeFinset.card ≤ 4 * r := by
  have hsub : (paritySelector r).edgeFinset ⊆ univ.image edgeSlot := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      simp only [mem_image, mem_univ, true_and, Prod.exists]
      have key : ∀ i j : Fin r, (i = j ∨ i.val = j.val + 1) →
          ∃ a b, edgeSlot (a, b) = s(pa i, pb j) := by
        intro i j h
        rcases h with rfl | h
        · exact ⟨i, 2, rfl⟩
        · refine ⟨i, 3, ?_⟩
          have : j = ⟨i.val - 1, by omega⟩ := by ext; simp only; omega
          rw [this]; exact Sym2.eq_swap
      rcases x with i | i | i <;> rcases y with j | j | j <;>
        simp only [paritySelector, pe, decide_eq_true_eq, Bool.false_eq_true, or_false,
          false_or, or_self] at he
      · subst he; exact ⟨_, 0, rfl⟩
      · subst he; exact ⟨_, 1, rfl⟩
      · subst he; exact ⟨_, 0, Sym2.eq_swap⟩
      · exact key i j he
      · subst he; exact ⟨_, 1, Sym2.eq_swap⟩
      · obtain ⟨a, b, h⟩ := key j i he.symm
        exact ⟨a, b, h.trans Sym2.eq_swap⟩
  calc (paritySelector r).edgeFinset.card ≤ (univ.image (edgeSlot (r := r))).card :=
        card_le_card hsub
    _ ≤ (univ : Finset (Fin r × Fin 4)).card := card_image_le
    _ = 4 * r := by simp [mul_comm]

/-! ### The prefix-parity carry and the matching modes -/

/-- `carry S i` is the parity of the number of ports of `S` with index `< i`. -/
def carry {r : ℕ} (S : Finset (Fin r)) (i : ℕ) : Bool :=
  (S.filter (fun j : Fin r => j.val < i)).card % 2 == 1

lemma carry_zero {r : ℕ} (S : Finset (Fin r)) : carry S 0 = false := by
  simp [carry]

lemma carry_succ {r : ℕ} (S : Finset (Fin r)) (i : Fin r) :
    carry S (i.val + 1) = xor (carry S i.val) (decide (i ∈ S)) := by
  have hsplit : S.filter (fun j : Fin r => j.val < i.val + 1) =
      S.filter (fun j : Fin r => j.val < i.val) ∪ S.filter (fun j => j = i) := by
    ext j; simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, Fin.ext h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, rfl⟩)
      · exact ⟨h1, by omega⟩
      · exact ⟨h1, by omega⟩
  have hdisj : Disjoint (S.filter (fun j : Fin r => j.val < i.val)) (S.filter (fun j => j = i)) := by
    rw [disjoint_filter]; intro j _ h1 h2; subst h2; omega
  simp only [carry, hsplit, card_union_of_disjoint hdisj]
  by_cases hi : i ∈ S
  · have : S.filter (fun j => j = i) = {i} := by
      ext j; simp only [mem_filter, mem_singleton]; constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨hi, rfl⟩
    rw [this, card_singleton]; simp only [hi, decide_true]
    obtain ⟨c, hc⟩ : ∃ c, (S.filter (fun j : Fin r => j.val < i.val)).card = c := ⟨_, rfl⟩
    rw [hc]
    rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [Nat.add_mod, h]
  · have : S.filter (fun j => j = i) = ∅ := by
      ext j; simp only [mem_filter, Finset.notMem_empty, iff_false, not_and]
      rintro hj rfl; exact hi hj
    rw [this]; simp [hi]

lemma carry_top {r : ℕ} (S : Finset (Fin r)) (hS : Even S.card) : carry S r = false := by
  have : S.filter (fun j : Fin r => j.val < r) = S := by
    ext j; simp
  simp only [carry, this]
  rw [Nat.even_iff] at hS
  simp [hS]

/-- Membership in the covered set `aux ∪ S`. -/
def inW {r : ℕ} (S : Finset (Fin r)) : PV r → Prop
  | Sum.inl i => i ∈ S
  | Sum.inr _ => True

/-- The partner of each covered vertex in the mode of `S`. -/
def partner {r : ℕ} (S : Finset (Fin r)) : PV r → PV r
  | Sum.inl i => if carry S i.val then pb i else pa i
  | Sum.inr (Sum.inl i) =>
      if carry S i.val then pb ⟨i.val - 1, by omega⟩ else if i ∈ S then pu i else pb i
  | Sum.inr (Sum.inr i) =>
      if h : i.val + 1 < r ∧ carry S (i.val + 1) = true then pa ⟨i.val + 1, h.1⟩
      else if i ∈ S then pu i else pa i

lemma carry_pos {r : ℕ} (S : Finset (Fin r)) (i : ℕ) (h : carry S i = true) : 0 < i := by
  rcases Nat.eq_zero_or_pos i with rfl | h'
  · simp [carry_zero] at h
  · exact h'

lemma carry_succ_false_of_not {r : ℕ} (S : Finset (Fin r)) (hS : Even S.card) (i : Fin r)
    (h : ¬ (i.val + 1 < r ∧ carry S (i.val + 1) = true)) : carry S (i.val + 1) = false := by
  by_cases hr : i.val + 1 < r
  · simpa [hr] using h
  · have : i.val + 1 = r := by omega
    rw [this]; exact carry_top S hS

theorem partner_spec {r : ℕ} (S : Finset (Fin r)) (hS : Even S.card) (x : PV r)
    (hx : inW S x) :
    inW S (partner S x) ∧ partner S (partner S x) = x ∧
      (paritySelector r).Adj x (partner S x) := by
  rcases x with i | i | i
  · -- port `u_i`, `i ∈ S`
    simp only [inW] at hx
    have hc := carry_succ S i
    cases h : carry S i.val
    · simp only [partner, h, Bool.false_eq_true, if_false, inW, true_and, if_true, hx]
      simp [paritySelector, pe]
    · simp only [partner, h, if_true, inW, true_and]
      have hn : ¬ (i.val + 1 < r ∧ carry S (i.val + 1) = true) := by
        rw [hc, h]; simp [hx]
      refine ⟨?_, ?_⟩
      · rw [dif_neg hn]; simp [hx]
      · simp [paritySelector, pe]
  · -- auxiliary `a_i`
    cases h : carry S i.val
    · by_cases hi : i ∈ S
      · simp [partner, h, hi, inW, paritySelector, pe]
      · simp only [partner, h, Bool.false_eq_true, if_false, hi, inW, true_and]
        have hn : ¬ (i.val + 1 < r ∧ carry S (i.val + 1) = true) := by
          rw [carry_succ, h]; simp [hi]
        refine ⟨?_, by simp [paritySelector, pe]⟩
        rw [dif_neg hn]
    · have hpos := carry_pos S _ h
      simp only [partner, h, if_true, inW, true_and]
      have e : (⟨i.val - 1, by omega⟩ : Fin r).val + 1 = i.val := by simp; omega
      refine ⟨?_, ?_⟩
      · rw [dif_pos ⟨by omega, by rw [e]; exact h⟩]
        congr 2
      · right; simp [pe]; omega
  · -- auxiliary `b_i`
    by_cases hc : i.val + 1 < r ∧ carry S (i.val + 1) = true
    · simp only [partner, dif_pos hc, inW, true_and]
      refine ⟨?_, ?_⟩
      · rw [if_pos hc.2]; congr 2
      · simp [paritySelector, pe]
    · have h0 := carry_succ_false_of_not S hS i hc
      rw [carry_succ] at h0
      simp only [partner, dif_neg hc]
      by_cases hi : i ∈ S
      · have : carry S i.val = true := by simpa [hi] using h0
        simp [hi, inW, this, paritySelector, pe]
      · have : carry S i.val = false := by simpa [hi] using h0
        simp only [hi, if_false, inW, true_and, this, Bool.false_eq_true]
        simp [paritySelector, pe]

/-- The matching subgraph realising the mode `S`. -/
def modeSubgraph {r : ℕ} (S : Finset (Fin r)) (hS : Even S.card) :
    (paritySelector r).Subgraph where
  verts := {x | inW S x}
  Adj x y := inW S x ∧ partner S x = y
  adj_sub := by
    rintro x y ⟨hx, rfl⟩; exact (partner_spec S hS x hx).2.2
  edge_vert := fun h => h.1
  symm := by
    constructor
    rintro x y ⟨hx, rfl⟩
    exact ⟨(partner_spec S hS x hx).1, (partner_spec S hS x hx).2.1⟩

lemma inW_iff {r : ℕ} (S : Finset (Fin r)) (x : PV r) :
    inW S x ↔ x ∈ auxSet r ∪ portSet S := by
  rcases x with i | i | i <;> simp [inW, auxSet, portSet]

/-- **Parity selector, all even modes.** The graph `paritySelector r` is fixed before `S`;
for every even set of ports `S` it has a matching subgraph covering exactly the
auxiliaries and the ports of `S`. -/
theorem paritySelector_even_mode (r : ℕ) (S : Finset (Fin r)) (hS : Even S.card) :
    ∃ M : (paritySelector r).Subgraph,
      M.verts = ↑(auxSet r ∪ portSet S) ∧ M.IsMatching := by
  refine ⟨modeSubgraph S hS, ?_, ?_⟩
  · ext x; simp [modeSubgraph, inW_iff]
  · rintro v hv
    exact ⟨partner S v, ⟨hv, rfl⟩, fun w hw => hw.2.symm⟩

/-- Edge-set form of a mode: a `Finset` of genuine graph edges (`Sym2`), every vertex of
`aux ∪ S` in exactly one of them, and no other vertex in any of them. -/
theorem paritySelector_even_mode_edges (r : ℕ) (S : Finset (Fin r)) (hS : Even S.card) :
    ∃ F : Finset (Sym2 (PV r)), F ⊆ (paritySelector r).edgeFinset ∧
      (∀ v, v ∈ auxSet r ∪ portSet S → (F.filter (fun e => v ∈ e)).card = 1) ∧
      (∀ v, v ∉ auxSet r ∪ portSet S → ∀ e ∈ F, v ∉ e) := by
  classical
  refine ⟨univ.filter (fun e => e ∈ (modeSubgraph S hS).edgeSet), ?_, ?_, ?_⟩
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    rw [SimpleGraph.mem_edgeFinset]
    exact (modeSubgraph S hS).edgeSet_subset he
  · intro v hv
    rw [← inW_iff] at hv
    rw [Finset.card_eq_one]
    refine ⟨s(v, partner S v), ?_⟩
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨he, hve⟩
      induction e using Sym2.ind with
      | h x y =>
        simp only [SimpleGraph.Subgraph.mem_edgeSet, modeSubgraph] at he
        rcases he with ⟨hx, rfl⟩
        rcases Sym2.mem_iff.mp hve with rfl | rfl
        · rfl
        · rw [(partner_spec S hS x hx).2.1]; exact Sym2.eq_swap
    · rintro rfl
      exact ⟨⟨hv, rfl⟩, Sym2.mem_mk_left _ _⟩
  · intro v hv e he hve
    rw [← inW_iff] at hv
    simp only [mem_filter, mem_univ, true_and] at he
    induction e using Sym2.ind with
    | h x y =>
      simp only [SimpleGraph.Subgraph.mem_edgeSet, modeSubgraph] at he
      rcases he with ⟨hx, rfl⟩
      rcases Sym2.mem_iff.mp hve with rfl | rfl
      · exact hv hx
      · exact hv (partner_spec S hS x hx).1

/-- The empty mode. -/
theorem paritySelector_empty_mode (r : ℕ) :
    ∃ M : (paritySelector r).Subgraph, M.verts = ↑(auxSet r) ∧ M.IsMatching := by
  obtain ⟨M, hM, hm⟩ := paritySelector_even_mode r ∅ (by simp)
  exact ⟨M, by simpa [portSet] using hM, hm⟩

/-- `r = 0`: the selector is the empty graph and its unique mode is the empty matching. -/
theorem paritySelector_zero :
    (paritySelector 0).edgeFinset = ∅ ∧
    ∃ M : (paritySelector 0).Subgraph, M.verts = ∅ ∧ M.IsMatching := by
  refine ⟨?_, ?_⟩
  · ext e; induction e using Sym2.ind with
    | h x y => rcases x with i | i | i <;> exact i.elim0
  · obtain ⟨M, hM, hm⟩ := paritySelector_empty_mode 0
    refine ⟨M, ?_, hm⟩
    rw [hM]; ext x; rcases x with i | i | i <;> exact i.elim0

/-- `r = 1`: the only even mode is the empty one, matched by the edge `a_0 b_0`. -/
theorem paritySelector_one :
    (paritySelector 1).edgeFinset.card ≤ 4 ∧
    ∀ S : Finset (Fin 1), Even S.card → S = ∅ ∧
      ∃ M : (paritySelector 1).Subgraph, M.verts = ↑(auxSet 1) ∧ M.IsMatching := by
  refine ⟨paritySelector_card_edgeFinset_le 1, fun S hS => ?_⟩
  have hS0 : S = ∅ := by
    rcases Finset.subset_univ S |> fun h => (Finset.card_le_univ S) with h
    simp only [Fintype.card_fin] at h
    have : S.card = 0 := by
      rcases hS with ⟨m, hm⟩; omega
    exact Finset.card_eq_zero.mp this
  exact ⟨hS0, paritySelector_empty_mode 1⟩

end ParitySel
