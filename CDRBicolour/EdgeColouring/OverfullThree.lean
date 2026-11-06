/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.EdgeColouring.Defs

/-!
# The condition `|S| ≥ 3` in the BHV convention

Bongard–Hoffmann–Volkmann only consider odd orders `≥ 3` for `Δ(G)`-full/overfull subgraphs.

* For **overfull** sets this condition is automatic: a set with at most one vertex spans no
  edge, so `k·(|S|-1) < 2·e(G[S])` fails.  Hence `InducesOverfull` is equivalent to the
  same predicate without `3 ≤ |S|` (`inducesOverfull_iff`).  Every use of overfull sets in
  the route (CCJS, Plantholt's Corollary 1.7, L183) is therefore unaffected.
* For **full** sets the condition is essential: a singleton is always `k`-full
  (`singleton_full`), so Plantholt's Lemma 1.3 is false without it.
-/

@[expose] public section

namespace CDRBicolour

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A set with at most one vertex spans no edge. -/
theorem edgesIn_eq_empty_of_card_le_one {S : Finset V} (h : S.card ≤ 1) : edgesIn G S = ∅ := by
  ext e
  simp only [edgesIn, mem_filter, SimpleGraph.mem_edgeFinset, notMem_empty, iff_false,
    not_and]
  intro he hall
  induction e using Sym2.ind with
  | _ x y =>
    have hx := hall x (Sym2.mem_mk_left x y)
    have hy := hall y (Sym2.mem_mk_right x y)
    have hxy : x = y := Finset.card_le_one.1 h x hx y hy
    exact (G.ne_of_adj ((SimpleGraph.mem_edgeSet G).1 he)) hxy

/-- The `|S| ≥ 3` clause is redundant for overfull sets. -/
theorem inducesOverfull_iff (k : ℕ) (S : Finset V) :
    InducesOverfull G k S ↔ Odd S.card ∧ k * (S.card - 1) < 2 * (edgesIn G S).card := by
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨hodd, hlt⟩
    refine ⟨hodd, ?_, hlt⟩
    by_contra h
    have hle : S.card ≤ 1 := by obtain ⟨j, hj⟩ := hodd; omega
    rw [edgesIn_eq_empty_of_card_le_one G hle] at hlt
    simp at hlt

/-- Without `|S| ≥ 3`, every singleton would count as `k`-full: the clause cannot be
dropped from the "full or overfull" predicate. -/
theorem singleton_full (k : ℕ) (v : V) :
    Odd ({v} : Finset V).card ∧ k * (({v} : Finset V).card - 1) ≤ 2 * (edgesIn G {v}).card := by
  simp
end CDRBicolour
