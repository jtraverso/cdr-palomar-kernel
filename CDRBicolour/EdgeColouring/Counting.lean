/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.EdgeColouring.Plantholt13
public import CDRBicolour.EdgeColouring.OverfullThree
public import CDRBicolour.EdgeColouring.Basic

/-!
# Edge counts inside vertex sets, and critical subgraphs

* `two_mul_edgesIn_le` : `2·e(S) ≤ |S|(|S|-1)`;
* `edgesIn_compl_identity` : `2e(S) + 2·Σ_{Sᶜ} deg = 2e(G) + 2e(Sᶜ)`;
* `edgesIn_erase_identity` : `e(V - x) + deg x = e(G)`;
* `exists_critical_subgraph` : a non-`k`-colourable graph contains a subgraph that is not
  `k`-colourable while all its proper subgraphs are.
-/

@[expose] public section

namespace CDRBicolour

open Finset

variable {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]

theorem two_mul_edgesIn_le (S : Finset W) :
    2 * (edgesIn G S).card ≤ S.card * S.card - S.card := by
  rw [← card_innerDarts]; exact card_innerDarts_le G S

theorem edgesIn_compl_identity (S : Finset W) :
    2 * (edgesIn G S).card + 2 * ∑ v ∈ Sᶜ, G.degree v =
      2 * G.edgeFinset.card + 2 * (edgesIn G Sᶜ).card := by
  have hS := sum_degree_eq_card_darts G S
  have hX := sum_degree_eq_card_darts G Sᶜ
  rw [card_fst_mem_eq] at hS hX
  have hcut := card_cutDarts_compl G S
  have hI := card_innerDarts G S
  have hJ := card_innerDarts G Sᶜ
  have htot : ∑ v ∈ S, G.degree v + ∑ v ∈ Sᶜ, G.degree v = 2 * G.edgeFinset.card := by
    rw [sum_add_sum_compl, G.sum_degrees_eq_twice_card_edges]
  omega

theorem edgesIn_erase_identity (x : W) :
    (edgesIn G (univ.erase x)).card + G.degree x = G.edgeFinset.card := by
  have h := edgesIn_compl_identity G (univ.erase x)
  have hc : (univ.erase x)ᶜ = {x} := by
    ext v; simp [mem_compl, mem_erase]
  have he : edgesIn G {x} = ∅ := edgesIn_eq_empty_of_card_le_one G (by rw [card_singleton])
  rw [hc, sum_singleton, he, card_empty] at h
  omega

/-- Minimal non-colourable subgraphs exist. -/
theorem exists_critical_subgraph {k : ℕ} (hG : ¬ EdgeColourable G k) :
    ∃ H : SimpleGraph W, H ≤ G ∧ ¬ EdgeColourable H k ∧
      ∀ H' : SimpleGraph W, H' < H → EdgeColourable H' k := by
  classical
  have hex : ∃ n, ∃ H : SimpleGraph W, H ≤ G ∧ ¬ EdgeColourable H k ∧ H.edgeSet.ncard = n :=
    ⟨_, G, le_rfl, hG, rfl⟩
  obtain ⟨H, hHG, hH, hn⟩ := Nat.find_spec hex
  refine ⟨H, hHG, hH, fun H' hH' => ?_⟩
  by_contra hcol
  have hlt : H'.edgeSet.ncard < H.edgeSet.ncard :=
    Set.ncard_lt_ncard (SimpleGraph.edgeSet_ssubset_edgeSet.2 hH') (Set.toFinite _)
  exact Nat.find_min hex (hn ▸ hlt) ⟨H', le_trans hH'.le hHG, hcol, rfl⟩

end CDRBicolour
