/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Palomar.RudasovaSotak
public import BklsSolution

/-!
# Balister–Kostochka–Li–Schelp, Corollary 12

`BklsPalomar.corollary12` (`jtraverso/balanced-edge-colourings` @ `736c78e`, the compared statement
of the Palomar candidate entry for BKLS 2004 Theorems 1, 6, 10(2) and Corollary 12): if
`√(2n) + 4 ≤ Δ`, `5 ≤ δ` and `k` is least with `n_d ≤ C(k, d)` for every `d`, then `G` has a strong
line-graph colouring with `k + 1` colours (and none with fewer than `k`).

`bkls_corollary_12` derives our literal statement `Master.BKLS_Corollary_12`:
* `4 ≤ Δ` and `2n ≤ (Δ − 4)²` give `√(2n) + 4 ≤ Δ`;
* `5 ≤ deg v` for every `v` gives `5 ≤ δ` (the vertex set is nonempty since `Δ ≥ 4`);
* the strong line-graph colouring gives a map `Sym2 V → Fin (k + 1)` proper on `G.edgeFinset`
  with distinct palettes (`present`), `vdColourable_of_strong`.
-/

@[expose] public section

namespace CDRBicolour.Palomar

open Finset SimpleGraph LeanPool.Vizing LeanPool.Vizing.PEC LeanPool.Vizing.ColourClasses
  CDRBicolour.Prefix

/-- A strong line-graph colouring gives a vertex-distinguishing proper edge colouring. -/
theorem vdColourable_of_strong {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {k : ℕ} (C : G.lineGraph.Coloring (Fin (k + 1)))
    (hC : Balanced.IsStrong C) : Master.VDColourable G (k + 1) := by
  let χ : Sym2 V → Fin (k + 1) := fun e => if h : e ∈ G.edgeSet then C ⟨e, h⟩ else 0
  have hχ : ∀ e : G.edgeSet, C e = χ e.1 := fun e => by simp [χ, e.2]
  refine ⟨χ, ?_, ?_⟩
  · intro e he f hf hne hc
    rw [mem_edgeFinset] at he hf
    by_contra hd
    obtain ⟨v, hve, hvf⟩ := share_of_not_disjoint hd
    have hadj : G.lineGraph.Adj ⟨e, he⟩ ⟨f, hf⟩ := by
      rw [lineGraph_adj_iff_exists]
      exact ⟨fun h => hne (congrArg Subtype.val h), v, hve, hvf⟩
    exact C.valid hadj ((hχ ⟨e, he⟩).trans (hc.trans (hχ ⟨f, hf⟩).symm))
  · intro u v hne h
    apply hne
    apply hC
    ext θ
    rw [mem_palette_iff C χ hχ, mem_palette_iff C χ hχ, h]

/-- **Balister–Kostochka–Li–Schelp, Corollary 12**, in the literal form `Master.BKLS_Corollary_12`,
from the formalization `jtraverso/balanced-edge-colourings`. -/
theorem bkls_corollary_12 : Master.BKLS_Corollary_12.{0} := by
  intro V _ _ G _ k₀ hδ hΔ4 hΔ hk hkmin
  have hne : Nonempty V := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : G.maxDegree = 0 := by
      apply le_antisymm _ (Nat.zero_le _)
      exact G.maxDegree_le_of_forall_degree_le 0 fun v => isEmptyElim v
    omega
  have hmin : 5 ≤ G.minDegree := G.le_minDegree_of_forall_le_degree 5 hδ
  have hsqrt : Real.sqrt (2 * Fintype.card V) + 4 ≤ G.maxDegree := by
    have h1 : 2 * (Fintype.card V : ℝ) ≤ ((G.maxDegree - 4 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hΔ
    have h2 : Real.sqrt (2 * Fintype.card V) ≤ ((G.maxDegree - 4 : ℕ) : ℝ) := by
      calc Real.sqrt (2 * Fintype.card V) ≤ Real.sqrt (((G.maxDegree - 4 : ℕ) : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ = ((G.maxDegree - 4 : ℕ) : ℝ) := Real.sqrt_sq (by positivity)
    have h3 : ((G.maxDegree - 4 : ℕ) : ℝ) = (G.maxDegree : ℝ) - 4 := by
      rw [Nat.cast_sub hΔ4]; norm_num
    rw [h3] at h2
    linarith
  obtain ⟨⟨C, hC⟩, -⟩ := BklsPalomar.corollary12 hsqrt hmin hk hkmin
  exact vdColourable_of_strong C hC

end CDRBicolour.Palomar
