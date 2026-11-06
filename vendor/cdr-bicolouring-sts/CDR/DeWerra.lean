/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Konig.Basic
public import LeanPool.Vizing.Equitable

/-!
# Equalized edge colourings of bipartite graphs (de Werra)

A finite bipartite graph with `b · d` edges and maximum degree at most `b` has a proper edge
colouring with `b` colours in which every colour is used exactly `d` times (`deWerra`;
D. de Werra, *Balanced schedules*, INFOR 9 (1971); the form used by Colbourn–Dinitz–Rosa).

Proof: Kőnig's theorem gives a proper colouring with `Δ ≤ b` colours; the alternating-component
rebalancing of the registered Vizing entry (`exists_equitable_colouring`) makes the class sizes
differ by at most one on the same palette, and they then all equal the average `d`.
-/

@[expose] public section

namespace CDR

open Finset LeanPool.Vizing.ColourClasses LeanPool.Vizing.Equitable
  LeanPool.Vizing.EquitableDefinitions LeanPool.Vizing.LineGraphColouring

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Class sizes that differ by at most one and sum to `b · d` over `b` classes all equal `d`. -/
theorem eq_of_equitable_of_sum {b d : ℕ} (f : Fin b → ℕ) (hf : ∀ i j, f i ≤ f j + 1)
    (hsum : ∑ i, f i = b * d) (i : Fin b) : f i = d := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : ∀ j, f j ≤ d := fun j => by have := hf j i; omega
    have : ∑ j, f j < ∑ _j : Fin b, d :=
      Finset.sum_lt_sum (fun j _ => hle j) ⟨i, mem_univ _, hlt⟩
    simp at this
    omega
  · have hge : ∀ j, d ≤ f j := fun j => by have := hf i j; omega
    have : ∑ _j : Fin b, d < ∑ j, f j :=
      Finset.sum_lt_sum (fun j _ => hge j) ⟨i, mem_univ _, hgt⟩
    simp at this
    omega

/-- **de Werra.** A finite bipartite graph with maximum degree at most `b` (`0 < b`) and `b · d`
edges has a proper edge colouring with `b` colours, each used exactly `d` times. -/
theorem deWerra (G : SimpleGraph W) [DecidableRel G.Adj] (hbip : G.Colorable 2) {b d : ℕ}
    (hb : 0 < b) (hdeg : G.maxDegree ≤ b) (hE : #G.edgeFinset = b * d) :
    ∃ colour : Sym2 W → Fin b, ProperOn G.edgeFinset colour ∧
      ∀ a, #(colourClass G.edgeFinset colour a) = d := by
  classical
  haveI : Inhabited (Fin b) := ⟨⟨0, hb⟩⟩
  have hcol : G.lineGraph.Colorable b :=
    (Konig.lineGraph_colorable_of_colorable_two G hbip).mono hdeg
  obtain ⟨C⟩ := hcol
  obtain ⟨colour, hproper, heq⟩ :=
    exists_equitable_colouring (G := G) (edgeColourOfLineGraph C)
      (properOn_of_lineGraph_colouring C)
  refine ⟨colour, hproper, fun a => ?_⟩
  refine eq_of_equitable_of_sum (fun a => #(colourClass G.edgeFinset colour a))
    (fun i j => heq i j) ?_ a
  rw [← hE]
  exact sum_card_colourClass_univ _ _

end CDR
