/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Stair
public import OneFactor.Labels

/-!
# The staircase labelling of `H*` (Chetwynd–Hilton 1989, §4)

`M` is a maximal matching inside `HV` (`exists_maximal_matching`). Each edge of `M` has a left end
and a right end, chosen by the priority `X < P < Y` (ties by a fixed code): an `X`-vertex goes
right unless its partner is in `X`, a `Y`-vertex goes left unless its partner is in `Y`. The left
ends get the indices `1, …, m`, the right ends the index of their partner, `v*` the index `m + 1`,
and the unmatched vertices the indices `t, …, 0` (`Y` first, `X` last).
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A maximal matching inside `S`.** -/
theorem exists_maximal_matching (G : SimpleGraph V) (S : Finset V) :
    ∃ M : SimpleGraph V, M ≤ G ∧ IsMatchingGraph M ∧ (∀ a b, M.Adj a b → a ∈ S ∧ b ∈ S) ∧
      ∀ a b, a ∈ S → b ∈ S → G.Adj a b → a ∈ cover M ∨ b ∈ cover M := by
  set T := (univ : Finset (SimpleGraph V)).filter fun M =>
    M ≤ G ∧ IsMatchingGraph M ∧ ∀ a b, M.Adj a b → a ∈ S ∧ b ∈ S
  have hne : T.Nonempty := ⟨⊥, mem_filter.2 ⟨mem_univ _, bot_le,
    fun v a b h => absurd h (by simp), fun a b h => absurd h (by simp)⟩⟩
  obtain ⟨M, hM, hmax⟩ := T.exists_max_image (fun M => #M.edgeFinset) hne
  obtain ⟨-, hMG, hMm, hMS⟩ := mem_filter.1 hM
  refine ⟨M, hMG, hMm, hMS, fun a b ha hb hab => ?_⟩
  by_contra hc
  push_neg at hc
  obtain ⟨hac, hbc⟩ := hc
  have hna : ∀ u, ¬ M.Adj a u := fun u h => hac (mem_cover.2 ⟨u, h⟩)
  have hnb : ∀ u, ¬ M.Adj b u := fun u h => hbc (mem_cover.2 ⟨u, h⟩)
  set M' := M ⊔ SimpleGraph.fromEdgeSet {s(a, b)}
  have hM'adj : ∀ u v, M'.Adj u v ↔ M.Adj u v ∨ (s(u, v) = s(a, b) ∧ u ≠ v) := by
    intro u v
    simp [M', fromEdgeSet_adj]
  have hM'T : M' ∈ T := by
    refine mem_filter.2 ⟨mem_univ _, fun u v h => ?_, fun v x y hx hy => ?_, fun u v h => ?_⟩
    · rcases (hM'adj u v).1 h with h | ⟨he, -⟩
      · exact hMG h
      · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hab
        · exact hab.symm
    · rcases (hM'adj v x).1 hx with hxM | ⟨hex, hvx⟩ <;>
        rcases (hM'adj v y).1 hy with hyM | ⟨hey, hvy⟩
      · exact hMm v x y hxM hyM
      · exfalso
        rcases Sym2.eq_iff.1 hey with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hna x hxM
        · exact hnb x hxM
      · exfalso
        rcases Sym2.eq_iff.1 hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hna y hyM
        · exact hnb y hyM
      · rcases Sym2.eq_iff.1 hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases Sym2.eq_iff.1 hey with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> simp_all
    · rcases (hM'adj u v).1 h with h | ⟨he, -⟩
      · exact hMS u v h
      · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨ha, hb⟩
        · exact ⟨hb, ha⟩
  have hlt : #M.edgeFinset < #M'.edgeFinset := by
    apply card_lt_card
    refine ⟨edgeFinset_mono le_sup_left, fun hsub => ?_⟩
    have hmem : s(a, b) ∈ M'.edgeFinset := by
      rw [mem_edgeFinset, mem_edgeSet]
      exact (hM'adj a b).2 (Or.inr ⟨rfl, hab.ne⟩)
    have := hsub hmem
    rw [mem_edgeFinset, mem_edgeSet] at this
    exact hna b this
  have h2 := hmax M' hM'T
  exact (not_le.2 hlt) (by convert h2)

/-- The partner of `v` in a matching. -/
noncomputable def partner (M : SimpleGraph V) (v : V) : V :=
  if h : ∃ u, M.Adj v u then h.choose else v

theorem adj_partner {M : SimpleGraph V} {v : V} (hv : v ∈ cover M) : M.Adj v (partner M v) := by
  have h := mem_cover.1 hv
  unfold partner
  rw [dif_pos h]
  exact h.choose_spec

theorem partner_eq {M : SimpleGraph V} (hM : IsMatchingGraph M) {v u : V} (h : M.Adj v u) :
    partner M v = u :=
  hM v _ u (adj_partner (mem_cover.2 ⟨u, h⟩)) h

theorem partner_mem_cover {M : SimpleGraph V} {v : V} (hv : v ∈ cover M) :
    partner M v ∈ cover M :=
  mem_cover.2 ⟨v, (adj_partner hv).symm⟩

theorem partner_partner {M : SimpleGraph V} (hM : IsMatchingGraph M) {v : V} (hv : v ∈ cover M) :
    partner M (partner M v) = v :=
  partner_eq hM (adj_partner hv).symm

theorem partner_ne {M : SimpleGraph V} {v : V} (hv : v ∈ cover M) : partner M v ≠ v :=
  (adj_partner hv).ne'

/-- The rank of `v` in `S` for the key `key`. -/
noncomputable def rankIn (S : Finset V) (key : V → ℕ) (v : V) : ℕ := #(S.filter fun u => key u < key v)

theorem rankIn_lt {S : Finset V} {key : V → ℕ} {v : V} (hv : v ∈ S) : rankIn S key v < #S := by
  unfold rankIn
  apply card_lt_card
  refine ⟨filter_subset _ _, fun h => ?_⟩
  have := h hv
  simp at this

theorem rankIn_injOn {S : Finset V} {key : V → ℕ} (hkey : Set.InjOn key S) {u v : V} (hu : u ∈ S)
    (hv : v ∈ S) (h : rankIn S key u = rankIn S key v) : u = v := by
  by_contra hne
  have hk : key u ≠ key v := fun e => hne (hkey hu hv e)
  have key_lt : ∀ a b, a ∈ S → key a < key b → rankIn S key a < rankIn S key b := by
    intro a b ha hab
    unfold rankIn
    apply card_lt_card
    refine ⟨fun z hz => ?_, fun hsub => ?_⟩
    · rw [mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans hab⟩
    · have := hsub (mem_filter.2 ⟨ha, hab⟩)
      simp at this
  rcases lt_or_gt_of_ne hk with h1 | h1
  · have := key_lt u v hu h1; omega
  · have := key_lt v u hv h1; omega

/-- A code of the vertices. -/
noncomputable def code (v : V) : ℕ := (Fintype.equivFin V v : ℕ)

theorem code_inj {u v : V} (h : code u = code v) : u = v :=
  (Fintype.equivFin V).injective (Fin.ext h)

theorem code_lt (v : V) : code v < Fintype.card V := (Fintype.equivFin V v).isLt

section Labelling

variable (M : SimpleGraph V) (X Y HV : Finset V) (vs : V)

/-- The priority class: `X ↦ 0`, `Y ↦ 2`, others `↦ 1`. -/
noncomputable def prio (v : V) : ℕ := if v ∈ X then 0 else if v ∈ Y then 2 else 1

/-- `a` precedes `b` for the left side. -/
def Pref (a b : V) : Prop := prio X Y b < prio X Y a ∨ (prio X Y a = prio X Y b ∧ code b < code a)

/-- The matched left ends. -/
noncomputable def leftM : Finset V := HV.filter fun v => v ∈ cover M ∧ Pref X Y v (partner M v)

/-- The unmatched vertices. -/
noncomputable def unm : Finset V := HV.filter fun v => v ∉ cover M

/-- The key ordering the unmatched vertices: `Y` first, `X` last. -/
noncomputable def ukey (v : V) : ℕ :=
  (if v ∈ Y then 0 else if v ∈ X then 2 else 1) * Fintype.card V + code v

/-- The side. -/
noncomputable def sideOf (v : V) : Bool := decide (v = vs ∨ v ∈ leftM M X Y HV)

/-- The index. -/
noncomputable def idxOf (v : V) : ℤ :=
  if v = vs then (#(leftM M X Y HV) : ℤ) + 1
  else if v ∈ leftM M X Y HV then 1 + rankIn (leftM M X Y HV) code v
  else if v ∈ cover M then 1 + rankIn (leftM M X Y HV) code (partner M v)
  else 1 - (#(unm M HV) : ℤ) + rankIn (unm M HV) (ukey X Y) v

end Labelling

theorem pref_or {X Y : Finset V} {a b : V} (h : a ≠ b) : Pref X Y a b ∨ Pref X Y b a := by
  unfold Pref
  have := fun e => h (code_inj e)
  rcases lt_trichotomy (prio X Y a) (prio X Y b) with h1 | h1 | h1
  · exact Or.inr (Or.inl h1)
  · rcases lt_or_gt_of_ne (fun e => h (code_inj e) : code a ≠ code b) with h2 | h2
    · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
  · exact Or.inl (Or.inl h1)

theorem pref_asymm {X Y : Finset V} {a b : V} (h : Pref X Y a b) : ¬ Pref X Y b a := by
  unfold Pref at *
  omega

theorem ukey_inj {X Y : Finset V} {u v : V} (h : ukey X Y u = ukey X Y v) : u = v := by
  unfold ukey at h
  have hu := code_lt u
  have hv := code_lt v
  apply code_inj
  split_ifs at h <;> omega

end OneFactor
