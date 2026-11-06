/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Labels
public import Mathlib.Tactic.LinearCombination

/-!
# Round-robin classes on the labelled vertices

`cls a b = (λa + λb)/2 ∈ ℤ_N`. `classGraph k`: the edges of `G − w` inside `H = {v*} ∪ X ∪ W`
of class `k` — a matching that misses `missed k`, the vertex of `X` labelled `k` if there is one,
and `v*` otherwise.
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset

open scoped Classical

attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w vs : V)

/-- The class of a pair. -/
noncomputable def cls (a b : V) : ZMod (modN G w vs) :=
  ((label G w vs a + label G w vs b : ℕ) : ZMod (modN G w vs)) *
    (((modN G w vs + 1) / 2 : ℕ) : ZMod (modN G w vs))

/-- The graph of class `k`. -/
def classGraph (k : ℕ) : SimpleGraph V where
  Adj a b := (keepAt G w ∅).Adj a b ∧ a ∈ setH G w vs ∧ b ∈ setH G w vs ∧
    cls G w vs a b = (k : ZMod (modN G w vs))
  symm.symm := fun a b h => ⟨h.1.symm, h.2.2.1, h.2.1, by
    rw [← h.2.2.2, cls, cls, add_comm]⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- The vertex missed by class `k`. -/
noncomputable def missed (k : ℕ) : V :=
  if h : ∃ x ∈ setX G w vs, label G w vs x = k then h.choose else vs

variable {G w vs}

theorem two_mul_half :
    (2 : ZMod (modN G w vs)) * (((modN G w vs + 1) / 2 : ℕ) : ZMod (modN G w vs)) = 1 := by
  have h2 : 2 * ((modN G w vs + 1) / 2) = modN G w vs + 1 := by unfold modN; omega
  have : ((2 * ((modN G w vs + 1) / 2) : ℕ) : ZMod (modN G w vs)) = 1 := by
    rw [h2, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  simpa [Nat.cast_mul] using this

theorem natCast_inj_of_lt {a b : ℕ} (ha : a < modN G w vs) (hb : b < modN G w vs)
    (h : (a : ZMod (modN G w vs)) = b) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

/-- Cancel the factor `1/2`. -/
theorem cls_eq_iff {a b a' b' : V} :
    cls G w vs a b = cls G w vs a' b' ↔
      ((label G w vs a + label G w vs b : ℕ) : ZMod (modN G w vs)) =
        ((label G w vs a' + label G w vs b' : ℕ) : ZMod (modN G w vs)) := by
  constructor
  · intro h
    simp only [cls] at h
    have h2 := two_mul_half (G := G) (w := w) (vs := vs)
    linear_combination (2 : ZMod (modN G w vs)) * h -
      (((label G w vs a + label G w vs b : ℕ) : ZMod (modN G w vs)) -
        ((label G w vs a' + label G w vs b' : ℕ) : ZMod (modN G w vs))) * h2
  · intro h; simp only [cls]; rw [h]

theorem cls_eq_label_iff {a b : V} :
    cls G w vs a b = (label G w vs a : ZMod (modN G w vs)) ↔
      ((label G w vs b : ℕ) : ZMod (modN G w vs)) = label G w vs a := by
  have hl : (label G w vs a : ZMod (modN G w vs)) =
      ((label G w vs a + label G w vs a : ℕ) : ZMod (modN G w vs)) *
        (((modN G w vs + 1) / 2 : ℕ) : ZMod (modN G w vs)) := by
    rw [Nat.cast_add, ← two_mul, mul_comm (2 : ZMod (modN G w vs)), mul_assoc, two_mul_half,
      mul_one]
  constructor
  · intro h
    rw [hl] at h
    have := (cls_eq_iff (a := a) (b := b) (a' := a) (b' := a)).1 h
    rw [Nat.cast_add, Nat.cast_add] at this
    exact add_left_cancel this
  · intro h
    rw [hl]
    show cls G w vs a b = cls G w vs a a
    rw [cls_eq_iff, Nat.cast_add, Nat.cast_add, h]

section Pair

variable (hXY : #(setX G w vs) = #(setY G w vs))
include hXY

/-- The partner in `X` of a vertex of `Y`. -/
theorem exists_partner {y : V} (hy : y ∈ setY G w vs) :
    ∃ x ∈ setX G w vs, label G w vs y = 2 * label G w vs x := by
  set i := (setY G w vs).equivFin ⟨y, hy⟩
  set x := ((setX G w vs).equivFin.symm (Fin.cast hXY.symm i))
  refine ⟨x.1, x.2, ?_⟩
  rw [label_Y hy, label_X x.2]
  have : (setX G w vs).equivFin ⟨x.1, x.2⟩ = Fin.cast hXY.symm i := by
    simp [x]
  rw [this, Fin.val_cast]
  omega

theorem classGraph_matching (k : ℕ) : IsMatchingGraph (classGraph G w vs k) := by
  intro a b b' hb hb'
  have h := hb.2.2.2.trans hb'.2.2.2.symm
  rw [cls_eq_iff, Nat.cast_add, Nat.cast_add] at h
  have h' := add_left_cancel h
  exact label_injOn hXY hb.2.2.1 hb'.2.2.1
    (natCast_inj_of_lt (label_lt hXY hb.2.2.1) (label_lt hXY hb'.2.2.1) h')

theorem missed_mem (k : ℕ) : missed G w vs k ∈ setH G w vs := by
  unfold missed
  split_ifs with h
  · exact mem_setH.2 (Or.inr (Or.inl h.choose_spec.1))
  · exact mem_setH.2 (Or.inl rfl)

theorem missed_not_adj (k : ℕ) (hk : k < modN G w vs) (u : V) :
    ¬ (classGraph G w vs k).Adj (missed G w vs k) u := by
  intro hadj
  unfold missed at hadj
  split_ifs at hadj with h
  · obtain ⟨hx, hlx⟩ := h.choose_spec
    have h1 := hadj.2.2.2
    have h1' : cls G w vs h.choose u = (label G w vs h.choose : ZMod (modN G w vs)) := by
      rw [hlx]; exact h1
    rw [cls_eq_label_iff] at h1'
    replace h1 := h1'
    have := label_injOn hXY hadj.2.2.1 hadj.2.1
      (natCast_inj_of_lt (label_lt hXY hadj.2.2.1) (label_lt hXY hadj.2.1) h1)
    exact hadj.1.ne this.symm
  · -- `u` is a neighbour of `v*` in `H`, hence in `Y`
    have hGu : G.Adj vs u := ((keepAt_empty_adj G w).1 hadj.1).1
    have huY : u ∈ setY G w vs := by
      rcases mem_setH.1 hadj.2.2.1 with rfl | hu | hu | hu
      · exact absurd hGu (G.loopless.irrefl _)
      · exact absurd hGu (mem_setX.1 hu).2.2
      · exact hu
      · exact absurd hGu (mem_setP.1 hu).2.2
    obtain ⟨x, hx, hlx⟩ := exists_partner hXY huY
    apply h
    refine ⟨x, hx, ?_⟩
    have h1 := hadj.2.2.2
    have hc : cls G w vs vs u = (label G w vs x : ZMod (modN G w vs)) := by
      rw [cls, label_vs, hlx, zero_add, Nat.cast_mul, Nat.cast_ofNat,
        mul_comm (2 : ZMod (modN G w vs)), mul_assoc, two_mul_half, mul_one]
    rw [hc] at h1
    have hxlt := label_lt hXY (mem_setH.2 (Or.inr (Or.inl hx)))
    exact natCast_inj_of_lt hxlt hk h1

end Pair

end OneFactor
