/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.EdgeColouring.Defs
public import LeanPool.Vizing.LineGraphColouring
public import LeanPool.Vizing.EquitableDefinitions
public import Mathlib.Tactic.Linarith

/-!
# Basic facts on edge colourings

* `edgeColourable_of_le` : colourability passes to subgraphs;
* `edgeColourable_of_maxDegree_lt` : Vizing (Lean Pool) in the form `Δ < k ⇒ k` colours;
* `exists_properOn_of_edgeColourable` : a line-graph colouring gives a literal `ProperOn`
  colour assignment (input format of L184);
* `two_mul_edgesIn_le_of_properOn`, `not_inducesOverfull_of_edgeColourable` : the overfull
  obstruction — an odd set spans at most `k(|S|-1)/2` edges in a `k`-edge-colourable graph.
-/

@[expose] public section

namespace CDRBicolour

open Finset LeanPool.Vizing.ColourClasses LeanPool.Vizing.LineGraphColouring
  LeanPool.Vizing.EquitableDefinitions

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edgeColourable_of_le {G H : SimpleGraph V} (hHG : H ≤ G) {k : ℕ}
    (h : EdgeColourable G k) : EdgeColourable H k := by
  obtain ⟨C⟩ := h
  let f : H.lineGraph →g G.lineGraph :=
    { toFun := fun e => ⟨e.1, SimpleGraph.edgeSet_mono hHG e.2⟩
      map_rel' := by
        intro e₁ e₂ hadj
        rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj ⊢
        obtain ⟨hne, v, h1, h2⟩ := hadj
        exact ⟨fun h => hne (Subtype.ext (Subtype.mk.inj h)), v, h1, h2⟩ }
  exact ⟨C.comap f⟩

theorem edgeColourable_of_maxDegree_lt (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (h : G.maxDegree < k) : EdgeColourable G k :=
  (LeanPool.Vizing.lineGraph_colorable G).mono (by omega)

theorem exists_properOn_of_edgeColourable (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hk : 0 < k) (h : EdgeColourable G k) :
    ∃ colour : Sym2 V → Fin k, ProperOn G.edgeFinset colour := by
  obtain ⟨C⟩ := h
  haveI : Inhabited (Fin k) := ⟨⟨0, hk⟩⟩
  exact ⟨edgeColourOfLineGraph C, properOn_of_lineGraph_colouring C⟩

/-- Inside `S`, a colour class is a matching on `S`. -/
theorem two_mul_card_colourClass_edgesIn_le {G : SimpleGraph V} [DecidableRel G.Adj]
    {β : Type*} [DecidableEq β] (colour : Sym2 V → β)
    (hproper : ProperOn G.edgeFinset colour) (S : Finset V) (b : β) :
    2 * (colourClass (edgesIn G S) colour b).card ≤ S.card := by
  have hsub : edgesIn G S ⊆ G.edgeFinset := filter_subset _ _
  have hprop' : ProperOn (edgesIn G S) colour := fun e he f hf => hproper e (hsub he) f (hsub hf)
  have hcard : ((colourClass (edgesIn G S) colour b).biUnion Sym2.toFinset).card =
      2 * (colourClass (edgesIn G S) colour b).card := by
    rw [card_biUnion (colourClass_pairwiseDisjoint_toFinset hprop' b)]
    calc ∑ e ∈ colourClass (edgesIn G S) colour b, e.toFinset.card
        = ∑ _e ∈ colourClass (edgesIn G S) colour b, 2 := by
          refine sum_congr rfl fun e he => ?_
          exact Sym2.card_toFinset_of_not_isDiag e
            (SimpleGraph.not_isDiag_of_mem_edgeFinset (hsub (colourClass_subset _ _ _ he)))
      _ = _ := by rw [sum_const, smul_eq_mul, mul_comm]
  rw [← hcard]
  refine card_le_card ?_
  intro v hv
  rw [mem_biUnion] at hv
  obtain ⟨e, he, hve⟩ := hv
  have he' := colourClass_subset _ _ _ he
  simp only [edgesIn, mem_filter] at he'
  exact he'.2 v (Sym2.mem_toFinset.1 hve)

/-- The overfull obstruction for a literal proper colouring. -/
theorem two_mul_edgesIn_le_of_properOn {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (colour : Sym2 V → Fin k) (hproper : ProperOn G.edgeFinset colour) (S : Finset V)
    (hodd : Odd S.card) : 2 * (edgesIn G S).card ≤ k * (S.card - 1) := by
  have hsum := sum_card_colourClass_univ (edgesIn G S) colour
  have hle : ∀ i, 2 * (colourClass (edgesIn G S) colour i).card ≤ S.card - 1 := by
    intro i
    have := two_mul_card_colourClass_edgesIn_le colour hproper S i
    obtain ⟨m, hm⟩ := hodd
    omega
  calc 2 * (edgesIn G S).card = ∑ i : Fin k, 2 * (colourClass (edgesIn G S) colour i).card := by
        rw [← mul_sum, hsum]
    _ ≤ ∑ _i : Fin k, (S.card - 1) := sum_le_sum fun i _ => hle i
    _ = k * (S.card - 1) := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- A `k`-edge-colourable graph has no `k`-overfull odd set. -/
theorem not_inducesOverfull_of_edgeColourable {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (h : EdgeColourable G k) (S : Finset V) : ¬ InducesOverfull G k S := by
  rintro ⟨hodd, -, hlt⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨C⟩ := h
    have hE : edgesIn G S = ∅ := by
      ext e
      simp only [notMem_empty, iff_false]
      intro he
      have he' : e ∈ G.edgeSet := (SimpleGraph.mem_edgeFinset).1 (filter_subset _ _ he)
      exact (C ⟨e, he'⟩).elim0
    rw [hE] at hlt; simp at hlt
  · obtain ⟨colour, hproper⟩ := exists_properOn_of_edgeColourable G hk h
    have := two_mul_edgesIn_le_of_properOn colour hproper S hodd
    omega

end CDRBicolour
