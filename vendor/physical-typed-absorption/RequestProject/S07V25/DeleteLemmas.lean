/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V25.CoreH3H4

@[expose] public section

/-!
# V25 — auxiliary facts for post-sampling deletion

* `support_of_pathsLen` — a vertex of a path of length `t` is an end or an internal vertex.
* `walk_support_comp` — a walk starting in a link component stays in it.
* `col_parity` — along a walk inside a properly coloured set, the colour changes with parity.
* `commonNbr_link_adj` — a common neighbour (H3 pool element) of `v` and `w` with the label of a
  link neighbour of `w` is again a link neighbour of `w`.
* `colG_proper` — the row colouring is proper on a bipartite component.
-/

open Finset Classical

namespace S07V25

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24

variable {V I : Type*} [Fintype V]

omit [Fintype V] in
lemma support_of_pathsLen [DecidableEq V] {L : SimpleGraph V} [DecidableRel L.Adj] [Fintype V]
    {t : ℕ} {x y : V} {p : L.Walk x y} (hp : p ∈ pathsLen L t x y) {z : V}
    (hz : z ∈ p.support) : z = x ∨ z = y ∨ z ∈ intlSet (t - 1) p := by
  have hlen : p.length = t := by
    simp only [pathsLen, mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hp; exact hp.1
  obtain ⟨k, rfl, hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hz
  by_cases h0 : k = 0
  · left; subst h0; exact p.getVert_zero
  by_cases ht : k = t
  · right; left; subst ht; rw [← hlen]; exact p.getVert_length
  right; right
  rw [mem_intlSet]
  refine ⟨⟨k - 1, by omega⟩, ?_⟩
  simp only [intl]
  congr 1; omega

lemma walk_support_comp {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v x0 : V} :
    ∀ {x y : V} (p : (link G lab F v).Walk x y), x ∈ comp G lab F v x0 →
      ∀ z ∈ p.support, z ∈ comp G lab F v x0 := by
  intro x y p hx z hz
  have h1 := comp_eq_of_mem hx
  rw [← h1, mem_comp_iff]
  exact (p.takeUntil z hz).reachable

omit [Fintype V] in
lemma col_parity {L : SimpleGraph V} {D : Set V} {c : V → Bool}
    (hc : ∀ u ∈ D, ∀ w ∈ D, L.Adj u w → c u ≠ c w) :
    ∀ {x y : V} (p : L.Walk x y), (∀ z ∈ p.support, z ∈ D) → (c y = c x ↔ Even p.length) := by
  intro x y p
  induction p with
  | nil => intro _; simp
  | @cons a b y h p ih =>
    intro hs
    have hab := hc a (hs a (by simp)) b (hs b (by simp)) h
    have := ih (fun z hz => hs z (by simp [hz]))
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ← this]
    revert hab; cases c a <;> cases c b <;> cases c y <;> simp

lemma commonNbr_link_adj {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v w y z : V}
    (hwy : (link G lab F v).Adj w y) (hz : z ∈ commonNbrs G lab (lab y) v w) :
    (link G lab F v).Adj w z := by
  obtain ⟨-, hall⟩ := hwy
  obtain ⟨hvw, hvy, hwy'⟩ := distinct_of_card_three hall.1
  simp only [commonNbrs, mem_filter, mem_univ, true_and] at hz
  obtain ⟨hvz, hwz, hlz⟩ := hz
  have hval : ∀ z, v ≠ z → w ≠ z →
      ((({v, w, z} : Finset V).val.map lab) = ({lab v, lab w, lab z} : Multiset I)) := by
    intro z hvz hwz
    classical
    rw [Finset.insert_val_of_notMem (by simp [hvw, hvz]),
      Finset.insert_val_of_notMem (by simp [hwz])]
    simp
  have hF : ({lab v, lab w, lab y} : Multiset I) ∈ F := by
    rw [← hval y hvy hwy']; convert hall.2.2
  refine ⟨hwz.ne, ?_⟩
  refine ⟨card_three_of_distinct hvw hvz.ne hwz.ne, ?_, ?_⟩
  · intro x hx x' hx' hxx'
    simp only [mem_insert, mem_singleton] at hx hx'
    have hGvw : G.Adj v w := hall.2.1 v (by simp) w (by simp) hvw
    rcases hx with rfl | rfl | rfl <;> rcases hx' with rfl | rfl | rfl
    all_goals first | exact absurd rfl hxx' | assumption | exact SimpleGraph.Adj.symm ‹_›
  · rw [hval z hvz.ne hwz.ne, hlz]; exact hF

omit [Fintype V] in
lemma link_root_ne {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v w y : V}
    (hwy : (link G lab F v).Adj w y) : v ≠ w ∧ ({lab v, lab w, lab y} : Multiset I) ∈ F := by
  obtain ⟨-, hall⟩ := hwy
  obtain ⟨hvw, hvy, hwy'⟩ := distinct_of_card_three hall.1
  refine ⟨hvw, ?_⟩
  classical
  have : (({v, w, y} : Finset V).val.map lab) = ({lab v, lab w, lab y} : Multiset I) := by
    rw [Finset.insert_val_of_notMem (by simp [hvw, hvy]),
      Finset.insert_val_of_notMem (by simp [hwy'])]
    simp
  rw [← this]; convert hall.2.2

lemma colG_proper {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v x0 : V}
    (hb : IsBip G lab F (v, comp G lab F v x0)) {w w' : V} (hw : w ∈ comp G lab F v x0)
    (hw' : w' ∈ comp G lab F v x0) (h : (link G lab F v).Adj w w') :
    colG G lab F v w ≠ colG G lab F v w' := by
  unfold colG
  rw [comp_eq_of_mem hw, comp_eq_of_mem hw']
  unfold col; rw [dif_pos hb]
  exact Classical.choose_spec hb w hw w' hw' h

end S07V25
