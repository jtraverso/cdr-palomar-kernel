/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import Balanced.Bridge
public import Bkls.Cor12

/-!
# Solution

`Balanced.palette` and `Balanced.IsStrong` are in `Balanced.Bridge` of the pinned dependency
`plantholt_overfull` (jtraverso/plantholt-overfull-criterion). The four theorems pass between
line-graph colourings and total partial edge colourings (`Balanced.ofColoring`,
`PEC.lineGraphColoring`) and apply `Bkls.theorem1`, `Bkls.T6.thm6`, `Bkls.T10.thm10_2` and
`Bkls.C12.cor12` (directory `Bkls/` of this repository).
-/

@[expose] public section

namespace BklsPalomar

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Balanced

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

open Classical in
/-- `n_S`: the number of vertices with palette `S`. -/
noncomputable def numPal (C : G.lineGraph.Coloring (Fin k)) (S : Finset (Fin k)) : ℕ :=
  #(univ.filter fun v => palette C v = ↑S)

/-- `Σ_S n_S²`. -/
noncomputable def cost (C : G.lineGraph.Coloring (Fin k)) : ℕ :=
  ∑ S : Finset (Fin k), numPal C S ^ 2

theorem palette_ofColoring [DecidableRel G.Adj] (C : G.lineGraph.Coloring (Fin k)) (v : V) :
    palette C v = ↑(colSet (ofColoring C) v) := by
  ext θ; rw [mem_coe, mem_colSet_ofColoring]

theorem palette_lineGraphColoring [DecidableRel G.Adj] {c : PEC G (Fin k)} (htot : Total c) (v : V) :
    palette (c.lineGraphColoring htot) v = ↑(colSet c v) := by
  ext θ; rw [mem_coe, mem_palette_lineGraphColoring]

theorem numPal_eq_cnt {C : G.lineGraph.Coloring (Fin k)} {c : PEC G (Fin k)}
    (h : ∀ v, palette C v = ↑(colSet c v)) (S : Finset (Fin k)) : numPal C S = cnt c S := by
  classical
  unfold numPal cnt
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and, h v, coe_inj]

theorem cost_eq {C : G.lineGraph.Coloring (Fin k)} {c : PEC G (Fin k)}
    (h : ∀ v, palette C v = ↑(colSet c v)) : cost C = Balanced.cost c := by
  unfold cost Balanced.cost
  exact sum_congr rfl fun S _ => by rw [numPal_eq_cnt h]

theorem strong_lineGraphColoring [DecidableRel G.Adj] {c : PEC G (Fin k)} (h : Strong c) :
    IsStrong (c.lineGraphColoring h.1) := by
  intro u v e
  apply h.2
  rw [palette_lineGraphColoring, palette_lineGraphColoring] at e
  exact_mod_cast e

/-- **BKLS 2004, Theorem 1.** -/
theorem theorem1 (C : G.lineGraph.Coloring (Fin k))
    (hC : ∀ C' : G.lineGraph.Coloring (Fin k), cost C ≤ cost C') {P Q : Finset (Fin k)}
    (h : #P = #Q) : numPal C P ≤ numPal C Q + 2 := by
  classical
  set c := ofColoring C
  have hP := palette_ofColoring C
  have hopt : IsOptimal c := by
    refine ⟨total_ofColoring C, fun c' htot' => ?_⟩
    have := hC (c'.lineGraphColoring htot')
    rwa [cost_eq hP, cost_eq (palette_lineGraphColoring htot')] at this
  rw [numPal_eq_cnt hP, numPal_eq_cnt hP]
  exact Bkls.theorem1 c hopt h

/-- **BKLS 2004, Theorem 6.** -/
theorem theorem6 [DecidableRel G.Adj] {κ : Type*} (c : Sym2 V → Fin 3) (key : V → κ)
    (hc : ∀ v e e', e ∈ G.incidenceFinset v → e' ∈ G.incidenceFinset v → e ≠ e' → c e ≠ c e')
    (h1 : ∀ u v, key u = key v → u ≠ v → G.degree u = G.degree v →
      (G.incidenceFinset u).image c = (G.incidenceFinset v).image c → G.degree u = 3)
    (h2 : ∀ u v w, key u = key v → key v = key w → G.degree u = 3 → G.degree v = 3 →
      G.degree w = 3 → u = v ∨ v = w ∨ u = w) :
    ∃ col : Sym2 V → Fin 4,
      (∀ v e e', e ∈ G.incidenceFinset v → e' ∈ G.incidenceFinset v → e ≠ e' → col e ≠ col e') ∧
      ∀ u v, u ≠ v → key u = key v →
        (G.incidenceFinset u).image col ≠ (G.incidenceFinset v).image col :=
  Bkls.T6.thm6 (key := key) hc h1 h2

/-- **BKLS 2004, Theorem 10 (part 2).** -/
theorem theorem10 [DecidableRel G.Adj] (hk3 : 3 ≤ k) (hΔ : G.maxDegree ≤ k)
    (h012 : ∀ d, d ≤ 2 → #(univ.filter fun v => G.degree v = d) ≤ 1)
    (h3 : #(univ.filter fun v => G.degree v = 3) ≤ 2)
    (h4 : #(univ.filter fun v => G.degree v = 4) ≤ 2)
    (hkk : #(univ.filter fun v => G.degree v = k) ≤ 2)
    (hk1 : #(univ.filter fun v => G.degree v = k - 1) ≤ k + 1)
    (h6 : ∀ d, 5 ≤ d → d + 2 ≤ k → (#(univ.filter fun v => G.degree v = d) : ℚ) ≤
      ((d : ℚ) - 4) / ((d : ℚ) - 3) *
        min (2 * (((k - 3).choose (d - 3) : ℕ) : ℚ)) ((k.choose d : ℕ) : ℚ) - 2) :
    ∃ C : G.lineGraph.Coloring (Fin (k + 1)), IsStrong C := by
  obtain ⟨c, hc⟩ := Bkls.T10.thm10_2 hk3 hΔ h012 h3 h4 hkk hk1 h6
  exact ⟨c.lineGraphColoring hc.1, strong_lineGraphColoring hc⟩

/-- **BKLS 2004, Corollary 12.** -/
theorem corollary12 [DecidableRel G.Adj] (hn : Real.sqrt (2 * Fintype.card V) + 4 ≤ G.maxDegree)
    (hδ : 5 ≤ G.minDegree) {k : ℕ}
    (hk : ∀ d, #(univ.filter fun v => G.degree v = d) ≤ k.choose d)
    (hkmin : ∀ k' < k, ∃ d, k'.choose d < #(univ.filter fun v => G.degree v = d)) :
    (∃ C : G.lineGraph.Coloring (Fin (k + 1)), IsStrong C) ∧
      ∀ m (C : G.lineGraph.Coloring (Fin m)), IsStrong C → k ≤ m := by
  obtain ⟨⟨c, hc⟩, hlow⟩ := Bkls.C12.cor12 hn hδ hk hkmin
  exact ⟨⟨c.lineGraphColoring hc.1, strong_lineGraphColoring hc⟩,
    fun m C hC => hlow m (ofColoring C) (strong_ofColoring hC)⟩

end BklsPalomar
