/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.Setting
public import RequestProject.S07V38.NativeAnnihilator
public import RequestProject.TypedTriangle.SparseEdgeLattice
set_option maxHeartbeats 4000000 -- build option (original: -DmaxHeartbeats=1600000; raised)
set_option maxRecDepth 16384 -- build option (original: -DmaxRecDepth=8192; raised)
@[expose] public section

/-!
# V42 §7a — elementary facts for integer charge polarization

Indicator algebra (`ind_insert`, `ind_union`, `triEdges_triple`, `ind_triangle`), allowed
triangles of the deleted core host `indG H (W \ Z)` (`allowed_indG`), the data of a native column
(`triple_of_allowed`), and the fresh-vertex choice from H3 of the TRUE core subtype
(`exists_fresh`: a common neighbour with a prescribed label in `W \ Z`, outside any prescribed
avoid set, joined to both ends by edges outside the sparse forbidden set `B`).
-/

open Finset Classical

noncomputable section

namespace S07V42

open TypedTriangle.SparseEdge

variable {V I : Type*}

/-! ### Indicator algebra -/

lemma ind_insert {e : Sym2 V} {Y : Finset (Sym2 V)} (he : e ∉ Y) :
    ind (insert e Y) = ind {e} + ind Y := by
  funext f
  simp only [ind, Finset.mem_insert, Finset.mem_singleton, Pi.add_apply]
  by_cases h : f = e
  · subst h; simp [he]
  · simp [h]

lemma ind_union {A B : Finset (Sym2 V)} (h : Disjoint A B) : ind (A ∪ B) = ind A + ind B := by
  funext f
  simp only [ind, Finset.mem_union, Pi.add_apply]
  by_cases ha : f ∈ A
  · have hb : f ∉ B := Finset.disjoint_left.1 h ha
    simp [ha, hb]
  · simp [ha]

lemma ind_empty' : ind (∅ : Finset (Sym2 V)) = 0 := by
  funext f; simp [ind]

lemma triEdges_triple {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    triEdges ({a, b, c} : Finset V) = {s(a, b), s(a, c), s(b, c)} := by
  ext e
  induction e using Sym2.ind with
  | h p q =>
    rw [mem_triEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨hp, hq, hpq⟩
      rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        simp_all [Ne.symm]

lemma ind_triangle {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ind (triEdges ({a, b, c} : Finset V)) = ind {s(a, b)} + ind {s(a, c)} + ind {s(b, c)} := by
  rw [triEdges_triple hab hac hbc, ind_insert, ind_insert, add_assoc]
  · simp [hab, hac, Ne.symm hbc]
  · simp [hab, hac, hbc, Ne.symm hab]

/-! ### Multisets of three labels -/

lemma mset_swap12 (a b c : I) : ({a, b, c} : Multiset I) = {b, a, c} := by
  simp only [Multiset.insert_eq_cons]; exact Multiset.cons_swap a b _

lemma mset_swap23 (a b c : I) : ({a, b, c} : Multiset I) = {a, c, b} := by
  rw [Multiset.pair_comm b c]

lemma triple_val {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset V).val = {a, b, c} := by
  simp [Finset.insert_val, hab, hac, hbc, Multiset.ndinsert_of_notMem]

/-! ### Allowed triangles of the deleted core host -/

variable [Fintype V]

omit [Fintype V] in
/-- a triangle of `H` inside `W \ Z` with an allowed label type is allowed in
`indG H (W \ Z)` -/
lemma allowed_indG {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {U : Finset V}
    {a b c : V} (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) (hab : H.Adj a b) (hac : H.Adj a c)
    (hbc : H.Adj b c) (hF : ({lab a, lab b, lab c} : Multiset I) ∈ F) :
    IsAllowed (indG H U) lab F {a, b, c} := by
  have h1 := hab.ne; have h2 := hac.ne; have h3 := hbc.ne
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
      Finset.card_insert_of_notMem (by simp [h3]), Finset.card_singleton]
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    have key : H.Adj x y := by
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first | exact absurd rfl hxy | assumption | exact SimpleGraph.Adj.symm ‹_›
    refine ⟨key, ?_, ?_⟩
    · rcases hx with rfl | rfl | rfl <;> assumption
    · rcases hy with rfl | rfl | rfl <;> assumption
  · rw [triple_val h1 h2 h3]; simpa using hF

omit [Fintype V] in
/-- the data of a native column -/
lemma triple_of_allowed {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {T : Finset V} (hT : IsAllowed G lab F T) {u v : V} (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) :
    ∃ w0, w0 ∈ T ∧ w0 ≠ u ∧ w0 ≠ v ∧ T = {u, v, w0} ∧
      ({lab u, lab v, lab w0} : Multiset I) ∈ F := by
  have hsub : ({u, v} : Finset V) ⊆ T := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hc : (T \ {u, v}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hT.1, Finset.card_pair huv]
  obtain ⟨w0, hw0⟩ := Finset.card_pos.1 (by omega : 0 < (T \ {u, v}).card)
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hw0
  obtain ⟨hw0T, hw0u, hw0v⟩ := hw0
  have hT3 : T = {u, v, w0} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · rw [hT.1, Finset.card_insert_of_notMem (by simp [huv, Ne.symm hw0u]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hw0v]), Finset.card_singleton]
  refine ⟨w0, hw0T, hw0u, hw0v, hT3, ?_⟩
  have := hT.2.2
  rw [hT3, triple_val huv (Ne.symm hw0u) (Ne.symm hw0v)] at this
  simpa using this

/-! ### Fresh vertices from H3 of the true core subtype -/

/-- **fresh common neighbour** -/
lemma exists_fresh {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V}
    {β : ℝ}
    (hH3 : CommonNbrCond (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) F β)
    (Z : Finset V) {B : Finset (Sym2 V)} {b : ℕ} (hB : ∀ v, degIn B v ≤ b) {p q : V}
    (hp : p ∈ W) (hq : q ∈ W) (hpq : p ≠ q) {k : I}
    (hk : ({lab p, lab q, k} : Multiset I) ∈ F) (Avoid : Finset V)
    (hroom : (Avoid.card : ℝ) + Z.card + 2 * b < β * W.card) :
    ∃ w, w ∈ W ∧ w ∉ Z ∧ w ∉ Avoid ∧ H.Adj p w ∧ H.Adj q w ∧ lab w = k ∧
      s(p, w) ∉ B ∧ s(w, q) ∉ B := by
  have h0 := hH3 ⟨p, hp⟩ ⟨q, hq⟩ (fun h => hpq (congrArg Subtype.val h)) k hk
  rw [Fintype.card_coe] at h0
  set Cn := (commonNbrs (H.comap (Subtype.val : {x // x ∈ W} → V)) (lab ∘ Subtype.val) k
    ⟨p, hp⟩ ⟨q, hq⟩).map (Function.Embedding.subtype _) with hCn
  have hCn_card : β * W.card ≤ (Cn.card : ℝ) := by rw [hCn, Finset.card_map]; exact h0
  set Bad := Avoid ∪ Z ∪ nbrIn B p ∪ nbrIn B q with hBad
  have hBad_card : (Bad.card : ℝ) ≤ Avoid.card + Z.card + b + b := by
    have h1 : Bad.card ≤ Avoid.card + Z.card + (nbrIn B p).card + (nbrIn B q).card := by
      refine (Finset.card_union_le _ _).trans ?_
      refine Nat.add_le_add_right ((Finset.card_union_le _ _).trans ?_) _
      exact Nat.add_le_add_right (Finset.card_union_le _ _) _
    have h2 := (card_nbrIn_le B p).trans (hB p)
    have h3 := (card_nbrIn_le B q).trans (hB q)
    have : Bad.card ≤ Avoid.card + Z.card + b + b := by omega
    exact_mod_cast this
  obtain ⟨w, hwC, hwB⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := Bad) (t := Cn) (by
      have : (Bad.card : ℝ) < Cn.card := by linarith
      exact_mod_cast this)
  rw [hCn, Finset.mem_map] at hwC
  obtain ⟨x, hx, rfl⟩ := hwC
  simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.comap_adj,
    Function.comp] at hx
  simp only [hBad, Finset.mem_union, not_or, Function.Embedding.coe_subtype] at hwB
  obtain ⟨⟨⟨hA, hZ⟩, hnp⟩, hnq⟩ := hwB
  refine ⟨x.1, x.2, hZ, hA, hx.1, hx.2.1, hx.2.2, ?_, ?_⟩
  · intro h; exact hnp (by simp [nbrIn, h])
  · intro h; exact hnq (by rw [Sym2.eq_swap] at h; simp [nbrIn, h])

end S07V42
