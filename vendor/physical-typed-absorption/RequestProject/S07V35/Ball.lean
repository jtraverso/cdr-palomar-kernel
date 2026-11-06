/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# BFS balls in a finite simple graph and the disjoint-neighbourhood radius bound (V35)

* `ball G S k`: vertices at graph distance `≤ k` from the finite set `S` (iterated BFS step).
* `mem_ball_of_walk`, `exists_walk_of_mem_ball`: ball membership ↔ walk of length `≤ k`.
* `mem_ball_of_stall`: if `ball G S (k+1) = ball G S k`, the ball is closed under reachability.
* `card_ball_growth`: if every vertex reached outside `S` has at least `m` distinct neighbours,
  then while the BFS keeps growing, `(a+1) * m ≤ |ball G S (3a+2)|`. The neighbourhood of a
  vertex at exact distance `3a+4` is disjoint from `ball G S (3a+2)` and contained in
  `ball G S (3a+5)` (the disjoint-neighbourhood argument along BFS layers).
* `ball_stall`: with `0 < m` and `|V| ≤ N`, the BFS from `S` stalls at radius `3 * (N / m)`.
-/

@[expose] public section

namespace S07V35

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One BFS step: `S` together with all neighbours of vertices of `S`. -/
def step (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S ∪ univ.filter (fun y => ∃ x ∈ S, G.Adj x y)

/-- `ball G S k`: the vertices at distance at most `k` from `S`. -/
def ball (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (k : ℕ) : Finset V :=
  (step G)^[k] S

/-- The open neighbourhood of `x` (distinct neighbours). -/
def nbrs (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Finset V :=
  univ.filter (G.Adj x)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem ball_zero (S : Finset V) : ball G S 0 = S := rfl

theorem ball_succ (S : Finset V) (k : ℕ) : ball G S (k + 1) = step G (ball G S k) :=
  Function.iterate_succ_apply' _ _ _

theorem ball_subset_succ (S : Finset V) (k : ℕ) : ball G S k ⊆ ball G S (k + 1) := by
  rw [ball_succ]; exact subset_union_left

theorem ball_mono (S : Finset V) {k j : ℕ} (h : k ≤ j) : ball G S k ⊆ ball G S j := by
  induction h with
  | refl => exact subset_refl _
  | step _ ih => exact ih.trans (ball_subset_succ G S _)

theorem subset_ball (S : Finset V) (k : ℕ) : S ⊆ ball G S k :=
  ball_mono G S (Nat.zero_le k)

theorem adj_mem_ball_succ {S : Finset V} {k : ℕ} {x y : V} (hx : x ∈ ball G S k)
    (h : G.Adj x y) : y ∈ ball G S (k + 1) := by
  rw [ball_succ]; exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, x, hx, h⟩)

theorem mem_ball_succ {S : Finset V} {k : ℕ} {y : V} :
    y ∈ ball G S (k + 1) ↔ y ∈ ball G S k ∨ ∃ x ∈ ball G S k, G.Adj x y := by
  rw [ball_succ, step, mem_union, mem_filter]; simp

theorem mem_ball_of_walk {S : Finset V} {u v : V} (p : G.Walk u v) :
    ∀ {j : ℕ}, u ∈ ball G S j → v ∈ ball G S (j + p.length) := by
  induction p with
  | nil => intro j h; simpa using h
  | cons h _ ih =>
    intro j hu
    have := ih (adj_mem_ball_succ G hu h)
    simpa [SimpleGraph.Walk.length_cons, Nat.add_assoc, Nat.add_comm 1] using this

theorem exists_walk_of_mem_ball {S : Finset V} :
    ∀ {k : ℕ} {y : V}, y ∈ ball G S k → ∃ x ∈ S, ∃ p : G.Walk x y, p.length ≤ k := by
  intro k
  induction k with
  | zero => intro y hy; exact ⟨y, hy, SimpleGraph.Walk.nil, le_rfl⟩
  | succ k ih =>
    intro y hy
    rcases (mem_ball_succ G).1 hy with hy | ⟨x, hx, hxy⟩
    · obtain ⟨z, hz, p, hp⟩ := ih hy
      exact ⟨z, hz, p, by omega⟩
    · obtain ⟨z, hz, p, hp⟩ := ih hx
      exact ⟨z, hz, p.concat hxy, by simp [SimpleGraph.Walk.length_concat]; omega⟩

theorem reachable_of_mem_ball {S : Finset V} {k : ℕ} {y : V} (hy : y ∈ ball G S k) :
    ∃ x ∈ S, G.Reachable x y := by
  obtain ⟨x, hx, p, -⟩ := exists_walk_of_mem_ball G hy
  exact ⟨x, hx, p.reachable⟩

theorem ball_stable {S : Finset V} {k : ℕ} (h : ball G S (k + 1) = ball G S k) :
    ∀ j, k ≤ j → ball G S j = ball G S k := by
  intro j hj
  induction hj with
  | refl => rfl
  | step _ ih => rw [ball_succ, ih, ← ball_succ, h]

theorem mem_ball_of_stall {S : Finset V} {k : ℕ} (h : ball G S (k + 1) = ball G S k)
    {x y : V} (hx : x ∈ ball G S k) (hr : G.Reachable x y) : y ∈ ball G S k := by
  obtain ⟨p⟩ := hr
  have := mem_ball_of_walk G p hx
  rwa [ball_stable G h _ (Nat.le_add_right _ _)] at this

/-- **Disjoint-neighbourhood growth.** If every vertex reached by the BFS outside `S` has at
least `m` distinct neighbours, then as long as layer `3a+1` is nonempty, the ball of radius
`3a+2` has at least `(a+1) m` vertices. -/
theorem card_ball_growth {S : Finset V} {m : ℕ}
    (hdeg : ∀ k, ∀ x ∈ ball G S k, x ∉ S → m ≤ (nbrs G x).card) :
    ∀ a : ℕ, ball G S (3 * a + 1) ≠ ball G S (3 * a) →
      (a + 1) * m ≤ (ball G S (3 * a + 2)).card := by
  have key : ∀ k, ball G S (k + 1) ≠ ball G S k →
      ∃ x ∈ ball G S (k + 1), x ∉ ball G S k ∧ m ≤ (nbrs G x).card ∧
        nbrs G x ⊆ ball G S (k + 2) ∧ ∀ j, j + 1 ≤ k → Disjoint (nbrs G x) (ball G S j) := by
    intro k hk
    obtain ⟨x, hx1, hx0⟩ : ∃ x ∈ ball G S (k + 1), x ∉ ball G S k := by
      by_contra hc
      push_neg at hc
      exact hk (Subset.antisymm hc (ball_subset_succ G S k))
    refine ⟨x, hx1, hx0, hdeg _ x hx1 (fun hS => hx0 (subset_ball G S k hS)), ?_, ?_⟩
    · intro y hy
      exact adj_mem_ball_succ G hx1 (mem_filter.1 hy).2
    · intro j hj
      rw [Finset.disjoint_left]
      intro y hy hyj
      have hadj : G.Adj y x := ((mem_filter.1 hy).2).symm
      exact hx0 (ball_mono G S (by omega) (adj_mem_ball_succ G hyj hadj))
  intro a
  induction a with
  | zero =>
    intro h
    obtain ⟨x, -, -, hm, hsub, -⟩ := key 0 h
    simpa using hm.trans (card_le_card hsub)
  | succ a ih =>
    intro h
    have h' : ball G S (3 * a + 1) ≠ ball G S (3 * a) := by
      intro hs
      apply h
      rw [ball_stable G hs (3 * (a + 1) + 1) (by omega), ball_stable G hs (3 * (a + 1)) (by omega)]
    have ih' := ih h'
    have h3 : ball G S (3 * a + 3 + 1) ≠ ball G S (3 * a + 3) := by
      simpa [show 3 * (a + 1) + 1 = 3 * a + 3 + 1 by ring, show 3 * (a + 1) = 3 * a + 3 by ring]
        using h
    obtain ⟨x, -, -, hm, hsub, hdisj⟩ := key (3 * a + 3) h3
    have hd := hdisj (3 * a + 2) (by omega)
    have hU : ball G S (3 * a + 2) ∪ nbrs G x ⊆ ball G S (3 * (a + 1) + 2) := by
      refine union_subset (ball_mono G S (by omega)) ?_
      simpa [show 3 * (a + 1) + 2 = 3 * a + 3 + 2 by ring] using hsub
    have := card_le_card hU
    rw [card_union_of_disjoint hd.symm] at this
    nlinarith

/-- **Radius bound.** If `0 < m`, `|V| ≤ N`, and every vertex reached by the BFS from `S`
outside `S` has at least `m` distinct neighbours, the BFS stalls at radius `3 * (N / m)`. -/
theorem ball_stall {S : Finset V} {m N : ℕ} (hm : 0 < m) (hN : Fintype.card V ≤ N)
    (hdeg : ∀ k, ∀ x ∈ ball G S k, x ∉ S → m ≤ (nbrs G x).card) :
    ball G S (3 * (N / m) + 1) = ball G S (3 * (N / m)) := by
  by_contra h
  have h1 := card_ball_growth G hdeg (N / m) h
  have h2 : (ball G S (3 * (N / m) + 2)).card ≤ N := (card_le_univ _).trans hN
  have h3 := Nat.div_add_mod N m
  have h4 := Nat.mod_lt N hm
  nlinarith

end S07V35
