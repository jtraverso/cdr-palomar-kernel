/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07.ManyOddPaths

@[expose] public section

/-!
# V25 — local robustness ⇒ robust connectivity ⇒ edge expansion (abstract graphs)

For a finite graph `K` and deletion budgets `s` (vertices) and `d` (maximum degree of the
deleted edge set `B ⊆ Sym2 β`):

* `RobustLocal K s d` — any two neighbours `a ≠ b` of a common vertex are joined by a path
  meeting `S` at most in its ends and using no edge of `B`;
* `RobustConn K s d` — any two vertices outside `S` are joined by a walk avoiding `S` and `B`;
* `conn_of_local` — `K` preconnected, `RobustLocal K s d`, minimum degree `≥ s + 2`
  ⇒ `RobustConn K s d`;
* `expansion_of_conn` — `RobustConn K s d` ⇒ `(d + 1) · min(|T|, s + 1) ≤ 2 · cutCount K T`
  for every `T` with `2|T| ≤ |β|` (the `cutCount` of S07V24);
* double cover: `lift_walk`, `cover_local` (an *even* local path supply lifts to the cover
  `S07V24.dcover`), `cover_preconnected` (a preconnected graph with no proper Bool colouring
  has a preconnected double cover).
-/

open Finset

namespace S07V25

open S07V24

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- degree of `x` in a finite edge set -/
def degB (B : Finset (Sym2 β)) (x : β) : ℕ := (B.filter (fun e => x ∈ e)).card

/-- local robustness -/
def RobustLocal (K : SimpleGraph β) (s d : ℕ) : Prop :=
  ∀ u a b, K.Adj u a → K.Adj u b → a ≠ b → ∀ S : Finset β, S.card ≤ s →
    ∀ B : Finset (Sym2 β), (∀ x, degB B x ≤ d) →
      ∃ p : K.Walk a b, p.IsPath ∧ (∀ x ∈ p.support, x ∈ S → x = a ∨ x = b) ∧
        ∀ e ∈ p.edges, e ∉ B

/-- local robustness with paths of even length -/
def EvenRobustLocal (K : SimpleGraph β) (s d : ℕ) : Prop :=
  ∀ u a b, K.Adj u a → K.Adj u b → a ≠ b → ∀ S : Finset β, S.card ≤ s →
    ∀ B : Finset (Sym2 β), (∀ x, degB B x ≤ d) →
      ∃ p : K.Walk a b, p.IsPath ∧ Even p.length ∧ (∀ x ∈ p.support, x ∈ S → x = a ∨ x = b) ∧
        ∀ e ∈ p.edges, e ∉ B

omit [Fintype β] in
lemma EvenRobustLocal.toLocal {K : SimpleGraph β} {s d : ℕ} (h : EvenRobustLocal K s d) :
    RobustLocal K s d := by
  intro u a b hua hub hab S hS B hB
  obtain ⟨p, h1, -, h3, h4⟩ := h u a b hua hub hab S hS B hB
  exact ⟨p, h1, h3, h4⟩

/-- robust connectivity -/
def RobustConn (K : SimpleGraph β) (s d : ℕ) : Prop :=
  ∀ S : Finset β, S.card ≤ s → ∀ B : Finset (Sym2 β), (∀ x, degB B x ≤ d) →
    ∀ x y, x ∉ S → y ∉ S → ∃ p : K.Walk x y, (∀ z ∈ p.support, z ∉ S) ∧ ∀ e ∈ p.edges, e ∉ B

section conn

variable (K : SimpleGraph β) (S : Finset β) (B : Finset (Sym2 β))

/-- joined by a walk avoiding `S` and `B` -/
def Good (x y : β) : Prop :=
  ∃ p : K.Walk x y, (∀ z ∈ p.support, z ∉ S) ∧ ∀ e ∈ p.edges, e ∉ B

variable {K S B}

omit [Fintype β] [DecidableEq β] in
lemma Good.refl {x : β} (hx : x ∉ S) : Good K S B x x :=
  ⟨.nil, by simpa using hx, by simp⟩

omit [Fintype β] [DecidableEq β] in
lemma Good.symm {x y : β} (h : Good K S B x y) : Good K S B y x := by
  obtain ⟨p, h1, h2⟩ := h
  exact ⟨p.reverse, by simpa using h1, by simpa using h2⟩

omit [Fintype β] [DecidableEq β] in
lemma Good.trans {x y z : β} (h : Good K S B x y) (h' : Good K S B y z) : Good K S B x z := by
  obtain ⟨p, h1, h2⟩ := h
  obtain ⟨q, h1', h2'⟩ := h'
  refine ⟨p.append q, fun w hw => ?_, fun e he => ?_⟩
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hw
    rcases hw with hw | hw
    exacts [h1 w hw, h1' w hw]
  · rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    exacts [h2 e he, h2' e he]

end conn

/-- **local robustness ⇒ robust connectivity** -/
theorem conn_of_local (K : SimpleGraph β) [DecidableRel K.Adj] (s d : ℕ)
    (hK : K.Preconnected) (hloc : RobustLocal K s d) (hdeg : ∀ w, s + 2 ≤ K.degree w) :
    RobustConn K s d := by
  intro S hS B hB
  set N : β → Finset β := fun w => K.neighborFinset w \ S with hN
  have hNcard : ∀ w, s + 2 ≤ (N w).card + s := by
    intro w
    have h1 := Finset.le_card_sdiff S (K.neighborFinset w)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
    have := hdeg w
    simp only [hN]; omega
  have memN : ∀ {w x}, x ∈ N w ↔ K.Adj w x ∧ x ∉ S := by
    intro w x; simp [hN]
  -- step A
  have stepA : ∀ w, ∀ a ∈ N w, ∀ b ∈ N w, Good K S B a b := by
    intro w a ha b hb
    rw [memN] at ha hb
    by_cases hab : a = b
    · subst hab; exact Good.refl ha.2
    obtain ⟨p, -, hp2, hp3⟩ := hloc w a b ha.1 hb.1 hab S hS B hB
    refine ⟨p, fun z hz hzS => ?_, hp3⟩
    rcases hp2 z hz hzS with rfl | rfl
    exacts [ha.2 hzS, hb.2 hzS]
  -- step B'
  have stepB' : ∀ w w', K.Adj w w' → ∀ b ∈ N w, b ≠ w' → ∀ a' ∈ N w', Good K S B b a' := by
    intro w w' hww' b hb hbw' a' ha'
    have hb' := memN.1 hb
    obtain ⟨p, hpath, hp2, hp3⟩ := hloc w w' b hww' hb'.1 (Ne.symm hbw') S hS B hB
    cases p with
    | nil => exact absurd rfl hbw'
    | @cons _ p1 _ h q =>
      have hp1S : p1 ∉ S := by
        intro hS1
        rcases hp2 p1 (by simp) hS1 with h1 | h1
        · exact h.ne h1.symm
        · exact hb'.2 (h1 ▸ hS1)
      have hw'q : w' ∉ q.support := ((SimpleGraph.Walk.cons_isPath_iff _ _).1 hpath).2
      have hq : Good K S B p1 b := by
        refine ⟨q, fun z hz hzS => ?_, fun e he => hp3 e (by simp [he])⟩
        rcases hp2 z (by simp [hz]) hzS with rfl | rfl
        · exact hw'q hz
        · exact hb'.2 hzS
      exact hq.symm.trans (stepA w' p1 (memN.2 ⟨h, hp1S⟩) a' ha')
  -- step B
  have stepB : ∀ w w', K.Adj w w' → ∀ a ∈ N w, ∀ a' ∈ N w', Good K S B a a' := by
    intro w w' hww' a ha a' ha'
    have : 0 < ((N w).erase w').card := by
      have := Finset.pred_card_le_card_erase (s := N w) (a := w')
      have := hNcard w; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.1 this
    rw [Finset.mem_erase] at hb
    exact (stepA w a ha b hb.2).trans (stepB' w w' hww' b hb.2 hb.1 a' ha')
  have hNne : ∀ w, (N w).Nonempty := fun w => by
    rw [← Finset.card_pos]; have := hNcard w; omega
  -- step C
  have stepC : ∀ w w' (p : K.Walk w w'), ∀ a ∈ N w, ∀ a' ∈ N w', Good K S B a a' := by
    intro w w' p
    induction p with
    | nil => intro a ha a' ha'; exact stepA _ a ha a' ha'
    | @cons w w1 w' h q ih =>
      intro a ha a' ha'
      obtain ⟨c, hc⟩ := hNne w1
      exact (stepB w w1 h a ha c hc).trans (ih c hc a' ha')
  -- step D
  intro x y hx hy
  have hdx : 0 < K.degree x := by have := hdeg x; omega
  have hdy : 0 < K.degree y := by have := hdeg y; omega
  obtain ⟨zx, hzx⟩ := (SimpleGraph.degree_pos_iff_exists_adj K x).1 hdx
  obtain ⟨zy, hzy⟩ := (SimpleGraph.degree_pos_iff_exists_adj K y).1 hdy
  obtain ⟨p⟩ := hK zx zy
  exact stepC zx zy p x (memN.2 ⟨hzx.symm, hx⟩) y (memN.2 ⟨hzy.symm, hy⟩)

end S07V25
