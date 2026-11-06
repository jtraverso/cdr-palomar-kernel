/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Konig.Basic

/-!
# Matchings covering the vertices of maximum degree

In a finite bipartite graph whose degrees are at most `k` (`0 < k`), some matching covers every
vertex of degree exactly `k` (`exists_matching_cover_of_degree_le`). It is a colour class of a
Kőnig colouring with `k` colours: a vertex of degree `k` sees all `k` colours.
-/

@[expose] public section

namespace CDR

open SimpleGraph Finset LeanPool.Vizing

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- In a finite bipartite graph with all degrees at most `k`, `0 < k`, there is a matching `M`
(a subgraph in which every vertex has at most one neighbour) covering every vertex of degree
`k`. -/
theorem exists_matching_cover_of_degree_le (G : SimpleGraph W) [DecidableRel G.Adj]
    (hbip : G.Colorable 2) {k : ℕ} (hk0 : 0 < k) (hk : ∀ w, G.degree w ≤ k) :
    ∃ M : SimpleGraph W, M ≤ G ∧ (∀ u v w, M.Adj u v → M.Adj u w → v = w) ∧
      ∀ w, G.degree w = k → ∃ u, M.Adj w u := by
  classical
  obtain ⟨s⟩ := hbip
  have hmax : G.maxDegree ≤ Fintype.card (Fin k) := by
    rw [Fintype.card_fin]
    exact G.maxDegree_le_of_forall_degree_le k hk
  obtain ⟨c, hc⟩ := Konig.exists_total_of_bipartite (C := Fin k) s hmax
  let γ₀ : Fin k := ⟨0, hk0⟩
  let M : SimpleGraph W :=
    { Adj := fun u v => c.col u v = some γ₀
      symm := ⟨fun u v h => by rwa [c.col_symm]⟩
      loopless := ⟨fun u h => G.loopless.irrefl u (c.col_adj h)⟩ }
  refine ⟨M, fun u v h => c.col_adj h, fun u v w hv hw => c.col_proper hv hw, ?_⟩
  intro w hw
  have hsome : ∀ u : G.neighborFinset w, ∃ γ, c.col w u = some γ := fun u =>
    Option.ne_none_iff_exists'.1 (hc w u ((G.mem_neighborFinset w u).1 u.2))
  choose f hf using hsome
  have hinj : Function.Injective f := by
    intro u u' h
    exact Subtype.ext (c.col_proper (hf u) (h ▸ hf u'))
  have hcard : Fintype.card (G.neighborFinset w) = Fintype.card (Fin k) := by
    rw [Fintype.card_coe, Fintype.card_fin, card_neighborFinset_eq_degree, hw]
  obtain ⟨u, hu⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩).2 γ₀
  exact ⟨u, show c.col w u = some γ₀ by rw [← hu]; exact hf u⟩

end CDR
