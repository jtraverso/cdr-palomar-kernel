/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.EdgeColouring.Defs
public import CCJSSolution

/-!
# CCJS Theorem 1.2 from the Palomar formalization (CCJS v2)

`jtraverso/overfull-critical-graphs` @ `b85da9a` (Palomar) proves
`Overfull.overfull_of_critical_ccjs`: a `Δ`-critical graph (connected, of class two, every
`G - e` is `Δ`-edge-colourable) with `4Δ − 7δ ≥ 3n − 17` and `n + δ ≥ 27` is overfull.

Here:

* `connected_of_isCritical`: a critical graph in the literal CCJS sense of `Defs`
  (no isolated vertices, not `Δ`-edge-colourable, every proper subgraph is) is connected —
  otherwise colour the component of a vertex from `G - e₂` and the rest from `G - e₁`;
* `isDeltaCritical_of_isCritical`: hence it is `Δ`-critical in the sense of CCJS v2;
* `ccjs_large`: CCJS Theorem 1.2 (literal statement of `Defs`) with the extra hypothesis
  `n + δ ≥ 27`, proved — no external hypothesis.

The route only applies CCJS to critical graphs of maximum degree `a ≥ 26`, which have
`n ≥ a + 1 ≥ 27` vertices, so `ccjs_large` suffices there.
-/

@[expose] public section

namespace CDRBicolour

open Finset

universe u

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem deleteEdges_lt {e : Sym2 V} (he : e ∈ G.edgeSet) : G.deleteEdges {e} < G := by
  refine lt_of_le_of_ne ?_ fun h => ?_
  · intro u v huv
    rw [SimpleGraph.deleteEdges_adj] at huv
    exact huv.1
  · have : e ∈ (G.deleteEdges {e}).edgeSet := by rw [h]; exact he
    rw [SimpleGraph.edgeSet_deleteEdges] at this
    exact this.2 rfl

/-- **Critical graphs are connected.** -/
theorem connected_of_isCritical (h : IsCritical G) : G.Connected := by
  classical
  obtain ⟨hdeg, hnot, hcrit⟩ := h
  by_contra hc
  -- some vertex exists, since the empty graph is edge-colourable
  have hne : Nonempty V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    apply hnot
    haveI : IsEmpty G.edgeSet := ⟨fun e => by
      obtain ⟨e, -⟩ := e
      induction e using Sym2.ind with
      | _ a _ => exact hV.false a⟩
    exact ⟨SimpleGraph.Coloring.mk (fun e => isEmptyElim e) (fun {a} => isEmptyElim a)⟩
  haveI := hne
  have hpre : ¬ G.Preconnected := fun hp => hc ⟨hp⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hpre
  obtain ⟨x0, y, hxy⟩ := hpre
  -- inside: reachable from `x0`
  let ins : V → Prop := fun v => G.Reachable x0 v
  have hadj : ∀ {u v}, G.Adj u v → (ins u ↔ ins v) := fun huv =>
    ⟨fun h => h.trans huv.reachable, fun h => h.trans huv.reachable.symm⟩
  -- an edge inside and an edge outside
  obtain ⟨x1, hx1⟩ : ∃ w, G.Adj x0 w := by
    have := hdeg x0
    rw [← SimpleGraph.card_neighborFinset_eq_degree, card_pos] at this
    obtain ⟨w, hw⟩ := this
    exact ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).mp hw⟩
  obtain ⟨y1, hy1⟩ : ∃ w, G.Adj y w := by
    have := hdeg y
    rw [← SimpleGraph.card_neighborFinset_eq_degree, card_pos] at this
    obtain ⟨w, hw⟩ := this
    exact ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).mp hw⟩
  set e1 : Sym2 V := s(x0, x1)
  set e2 : Sym2 V := s(y, y1)
  have he1 : e1 ∈ G.edgeSet := hx1
  have he2 : e2 ∈ G.edgeSet := hy1
  obtain ⟨c1⟩ := hcrit _ (deleteEdges_lt he1)
  obtain ⟨c2⟩ := hcrit _ (deleteEdges_lt he2)
  -- the status of an edge
  let insE : Sym2 V → Prop := fun f => ∀ v ∈ f, ins v
  have hins_e2 : ¬ insE e2 := fun h => hxy (h y (Sym2.mem_mk_left _ _))
  have hins_e1 : insE e1 := by
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact hx1.reachable
  -- an edge is entirely inside or entirely outside
  have hdich : ∀ f ∈ G.edgeSet, insE f ∨ ∀ v ∈ f, ¬ ins v := by
    intro f hf
    induction f using Sym2.ind with
    | _ u v =>
    have huv : G.Adj u v := hf
    by_cases hu : ins u
    · left; intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hu
      · exact (hadj huv).mp hu
    · right; intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hu
      · exact fun h => hu ((hadj huv).mpr h)
  apply hnot
  refine ⟨SimpleGraph.Coloring.mk (fun f => if hf : insE f.1 then
      c2 ⟨f.1, by rw [SimpleGraph.edgeSet_deleteEdges]; exact ⟨f.2, fun h => hins_e2 (h ▸ hf)⟩⟩
    else c1 ⟨f.1, by
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨f.2, fun h => hf (by rw [Set.mem_singleton_iff.mp h]; exact hins_e1)⟩⟩) ?_⟩
  intro f g hfg
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hfg
  obtain ⟨hne, w, hwf, hwg⟩ := hfg
  have hsame : (insE f.1 ↔ insE g.1) := by
    rcases hdich f.1 f.2 with hf | hf <;> rcases hdich g.1 g.2 with hg | hg
    · exact ⟨fun _ => hg, fun _ => hf⟩
    · exact absurd (hf w hwf) (hg w hwg)
    · exact absurd (hg w hwg) (hf w hwf)
    · exact ⟨fun h => absurd (h w hwf) (hf w hwf), fun h => absurd (h w hwg) (hg w hwg)⟩
  by_cases hf : insE f.1
  · have hg : insE g.1 := hsame.mp hf
    simp only [dif_pos hf, dif_pos hg]
    apply c2.valid
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    exact ⟨fun h => hne (Subtype.ext (by simpa using congrArg Subtype.val h)), w, hwf, hwg⟩
  · have hg : ¬ insE g.1 := fun h => hf (hsame.mpr h)
    simp only [dif_neg hf, dif_neg hg]
    apply c1.valid
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    exact ⟨fun h => hne (Subtype.ext (by simpa using congrArg Subtype.val h)), w, hwf, hwg⟩

/-- A critical graph in the literal CCJS sense is `Δ`-critical in the sense of CCJS v2. -/
theorem isDeltaCritical_of_isCritical (h : IsCritical G) : Overfull.IsDeltaCritical G :=
  ⟨connected_of_isCritical h, h.2.1, fun _ he => h.2.2 _ (deleteEdges_lt he)⟩

/-- CCJS Theorem 1.2 (literal statement of `Defs`) restricted to `n + δ ≥ 27`. -/
def CCJS_Theorem_1_2_large : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
    IsCritical G →
      (3 * Fintype.card W : ℤ) - 17 ≤ 4 * G.maxDegree - 7 * G.minDegree →
        27 ≤ Fintype.card W + G.minDegree → IsOverfull G

/-- **CCJS Theorem 1.2 for `n + δ ≥ 27`, proved** (from CCJS v2, Palomar). -/
theorem ccjs_large : CCJS_Theorem_1_2_large.{u} := by
  intro W _ _ G _ hcrit hcond hn
  have hc : 3 * Fintype.card W + 7 * G.minDegree ≤ 4 * G.maxDegree + 17 := by
    have : (3 * Fintype.card W + 7 * G.minDegree : ℤ) ≤ 4 * G.maxDegree + 17 := by linarith
    exact_mod_cast this
  exact Overfull.overfull_of_critical_ccjs (isDeltaCritical_of_isCritical hcrit) hc hn

/-- The literal statement implies the restricted one. -/
theorem ccjs_large_of_literal (h : CCJS_Theorem_1_2.{u}) : CCJS_Theorem_1_2_large.{u} :=
  fun W _ _ G _ hcrit hcond _ => h W G hcrit hcond

end CDRBicolour
