/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V26.ForkNative
public import RequestProject.Selectors.GreedyEmbedding

@[expose] public section

/-!
# V26 — single-root adapter: V25 core routes ⇒ `SelEmbed.RobustOddPaths` inside the core

This is only the FIRST (single-root) piece of the selector step; the simultaneous layer with
global auxiliary counters and no `|Z|` term is NOT done here (see `LEDGER_V26.md`).

For a root `v`, a port set `Pv` and a forbidden edge graph `B` (`Δ(B) ≤ d ≤ εn`), the host
`coreHost G lab F v W Pv B` keeps the link edges of `L_v` with both ends in `W ∪ Pv` and not in
`B`. Every walk of this host has all its vertices in `W ∪ Pv`; so an internal vertex that is not
a port lies in `W`.

`routes_robustOddPaths`: the route property of the V25 core (exactly the last conjunct of
`S07V25.S07_core_H3H4`) gives `SelEmbed.RobustOddPaths (coreHost …) Allowed t ⌊εn⌋` with
`Allowed x y = AdmPair … v x y ∧ x, y ∈ W ∪ Pv`, i.e. the input of `SelEmbed.greedy_embedding`,
with paths of odd length exactly `t`.
-/

open Finset

noncomputable section
open Classical

namespace S07V26

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24 S07V25

variable {V I : Type*} [Fintype V]

/-- the routing host of root `v` inside the core: link edges with both ends in `W ∪ Pv`,
avoiding `B` -/
def coreHost (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V)
    (W Pv : Finset V) (B : SimpleGraph V) : SimpleGraph V where
  Adj x y := (link G lab F v).Adj x y ∧ x ∈ W ∪ Pv ∧ y ∈ W ∪ Pv ∧ ¬ B.Adj x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, fun h' => h.2.2.2 h'.symm⟩⟩
  loopless := ⟨fun _ h => (link G lab F v).loopless.irrefl _ h.1⟩

omit [Fintype V] in
/-- every vertex of a `coreHost` walk lies in `W ∪ Pv` (ends included when the walk is
non-trivial); in particular a non-port internal vertex lies in `W` -/
lemma coreHost_support {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    {W Pv : Finset V} {B : SimpleGraph V} {x y : V} (q : (coreHost G lab F v W Pv B).Walk x y)
    (hq : ¬ q.Nil) : ∀ z ∈ q.support, z ∈ W ∪ Pv := by
  induction q with
  | nil => exact absurd SimpleGraph.Walk.Nil.nil hq
  | @cons a b c h p ih =>
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact h.2.1
    · by_cases hp : p.Nil
      · cases hp
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        rw [hz]; exact h.2.2.1
      · exact ih hp z hz

omit [Fintype V] in
/-- lifting a walk along consecutive adjacencies in another graph -/
lemma walk_lift {G H : SimpleGraph V} :
    ∀ {x y : V} (p : G.Walk x y),
      (∀ k < p.length, H.Adj (p.getVert k) (p.getVert (k + 1))) →
        ∃ q : H.Walk x y, q.support = p.support
  | _, _, .nil, _ => ⟨.nil, rfl⟩
  | _, _, .cons h p, hadj => by
    have h0 := hadj 0 (by simp)
    simp only [SimpleGraph.Walk.getVert_zero, zero_add,
      SimpleGraph.Walk.getVert_cons_succ] at h0
    obtain ⟨q, hq⟩ := walk_lift p fun k hk => by
      have := hadj (k + 1) (by simp; omega)
      simpa [SimpleGraph.Walk.getVert_cons_succ] using this
    exact ⟨.cons h0 q, by simp [hq]⟩

/-- **V25 core routes give the robust odd path input of the greedy selector embedding,
routed inside the core** -/
theorem routes_robustOddPaths {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {t : ℕ} (ht : Odd t) {ε : ℝ} {W : Finset V}
    (hroute : ∀ (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ),
      (Z.card : ℝ) ≤ ε * Fintype.card V → (∀ u, B.degree u ≤ d) →
      (d : ℝ) ≤ ε * Fintype.card V →
      ∀ v x y, AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C))
          (colG G lab F) v x y →
        ∃ p ∈ pathsLen (link G lab F v) t x y, intlSet (t - 1) p ⊆ W ∧
          (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z) ∧
          ∀ k < t, ¬ B.Adj (p.getVert k) (p.getVert (k + 1)))
    (v : V) (Pv : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ)
    (hBd : ∀ u, B.degree u ≤ d) (hd : (d : ℝ) ≤ ε * Fintype.card V) :
    SelEmbed.RobustOddPaths (coreHost G lab F v W Pv B)
      (fun x y => AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C))
        (colG G lab F) v x y ∧ x ∈ W ∪ Pv ∧ y ∈ W ∪ Pv) t ⌊ε * Fintype.card V⌋₊ := by
  intro Z hZ a b ⟨hadm, ha, hb⟩ haZ hbZ
  have hε0 : 0 ≤ ε * Fintype.card V := by
    by_contra hc; push_neg at hc
    have := (Nat.cast_nonneg (α := ℝ) d).trans hd; linarith
  have hZ' : (Z.card : ℝ) ≤ ε * Fintype.card V :=
    (Nat.cast_le.2 hZ).trans (Nat.floor_le hε0)
  obtain ⟨p, hp, hW, hZint, hB⟩ := hroute Z B d hZ' hBd hd v a b hadm
  have hlen : p.length = t := by
    simp only [pathsLen, mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hp; exact hp.1
  have hpath : p.IsPath := by
    simp only [pathsLen, mem_filter] at hp; exact hp.2
  have hsupp : ∀ z ∈ p.support, z ∈ W ∪ Pv := by
    intro z hz
    rcases support_of_pathsLen hp hz with rfl | rfl | hz
    · exact ha
    · exact hb
    · exact mem_union_left _ (hW hz)
  obtain ⟨q, hq⟩ := walk_lift (H := coreHost G lab F v W Pv B) p fun k hk =>
    ⟨p.adj_getVert_succ hk, hsupp _ (p.getVert_mem_support _),
      hsupp _ (p.getVert_mem_support _), hB k (hlen ▸ hk)⟩
  have hqlen : q.length = t := by
    have h1 := q.length_support; have h2 := p.length_support
    rw [hq] at h1; omega
  refine ⟨q, ?_, by rw [hqlen]; exact ht, by rw [hqlen], ?_⟩
  · rw [SimpleGraph.Walk.isPath_def, hq]; exact hpath.support_nodup
  · intro z hz
    rw [hq] at hz
    rcases support_of_pathsLen hp hz with rfl | rfl | hz
    · exact haZ
    · exact hbZ
    · obtain ⟨i, rfl⟩ := (mem_intlSet _ _ _).1 hz
      exact hZint i

end S07V26

end
