/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V27.CoreComponent
public import RequestProject.S07V27.SelectorWindow
public import RequestProject.S07V26.ForkNative
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)

@[expose] public section

/-!
# V27 — the simultaneous PAR/BAL selector layer for ALL roots on the SAME V25 core

* `selector_layer_host`: for a host with a core `W` satisfying the V25 route property, every
  root set `Z` disjoint from `W` (it may contain almost all vertices), every `X` with `X[Z]`
  empty whose edges at the roots lie in permitted triangles, and every forbidden graph `B0`,
  under the two explicit windows, ONE family of selectors (chosen before `L`) gives the exact
  positive partition and the charge identity for EVERY later admissible `L ⊆ E(X)`.
* `link_of_edgeCovered`: an edge `vu` in a permitted triangle makes `u` a link vertex of `v`.
* **`S07_selector_layer_native`**: constants `t, a, ε` (those of `S07_core_H3H4`),
  `A = 200t + 8`, `εS = selEps ε A`, `n₀`, all fixed before the host.  For every host with
  H3, H4 and `n ≥ n₀`, ONE `W` carries the V25 core properties verbatim and the layer above for
  all `X, B0, Z, r, b` with `X ≤ G`, `H1Load ∨ H2Phys` (V26 local shapes, only `EdgeCovered`
  is used), `Δ(X) ≤ r`, `Δ(B0) ≤ b`, `r, b ≤ εS·n`, counter `q = selQ ε A r`.
-/

namespace S07V27

open Finset SimpleGraph SelBridge SelTyped SelSimul SelEmbed
open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24 S07V25 S07V26

noncomputable section
open Classical

section host

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- **The simultaneous layer for all roots, routed in the core, for one host.** -/
theorem selector_layer_host {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {t : ℕ}
    (ht : Odd t) (ht3 : 3 ≤ t) {ε : ℝ} (hε : 0 < ε) {W : Finset V}
    (hroute : RouteProp G lab F t ε W) (X B0 : SimpleGraph V) [DecidableRel X.Adj]
    [DecidableRel B0.Adj] (Z : Finset V) (hZ : ∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v')
    (hZW : Disjoint Z W) (hXl : ∀ v ∈ Z, ∀ u, X.Adj v u → ∃ y, (link G lab F v).Adj u y)
    {A q r b : ℕ} (hA : 200 * (t - 1) + 8 ≤ A) (hq : 0 < q) (hX : ∀ x, X.degree x ≤ r)
    (hB : ∀ x, B0.degree x ≤ b)
    (hBud : r + b + A * r * Fintype.card V / q + (A + 1) * r + 10 * r + (t - 1) * (200 * r) ≤
      ⌊ε * Fintype.card V⌋₊)
    (hρ : ((b + 61 * r + 60 * q + 60 : ℕ) : ℝ) ≤ ε * Fintype.card V) :
    ∃ σ : V → LocalSel V,
      (∀ v ∈ Z, (σ v).W ⊆ W) ∧
      (∀ v ∈ Z, ∀ v' ∈ Z, v ≠ v' →
        Disjoint (fuel v (σ v).P (σ v).W) (fuel v' (σ v').P (σ v').W)) ∧
      Disjoint (fuelU Z σ) (X.edgeFinset ∪ B0.edgeFinset) ∧
      (∀ v ∈ Z, (∀ w ∈ (σ v).W, w ∉ Z) ∧ ∀ f ∈ (σ v).P, ∀ y ∈ f, y ∉ Z) ∧
      (∀ x, auxCount Z (fun v => (σ v).W) x ≤ q) ∧
      (∀ y, edeg (fuelU Z σ) y ≤ max (A * r) (60 * r + 61 * q)) ∧
      ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset → (∀ v ∈ Z, rootAdm G lab F X v (demand X L v)) →
        Disjoint (fuelU Z σ) L ∧
        fuelU Z σ ∪ L = packEdges (packing X Z σ L) ∪ residual X Z σ L ∧
        Disjoint (packEdges (packing X Z σ L)) (residual X Z σ L) ∧
        (packing X Z σ L : Set (V × Sym2 V)).PairwiseDisjoint (fun p => triE p.1 p.2) ∧
        (∀ p ∈ packing X Z σ L, p.1 ∈ Z ∧ ∃ x y, p.2 = s(x, y) ∧ x ≠ y ∧
          IsAllowed G lab F {p.1, x, y}) ∧
        (∀ f ∈ residual X Z σ L, ∀ v ∈ Z, v ∉ f) ∧
        (∀ y, edeg (residual X Z σ L) y ≤ 61 * r + 60 * q) ∧
        ∀ {M : Type} [AddCommGroup M] (c : Sym2 V → M),
          ∑ f ∈ residual X Z σ L, c f - ∑ f ∈ residual X Z σ ∅, c f =
            ∑ f ∈ L, c f - (∑ p ∈ packing X Z σ L, ∑ f ∈ triE p.1 p.2, c f -
              ∑ p ∈ packing X Z σ ∅, ∑ f ∈ triE p.1 p.2, c f) :=
  simultaneous_layer_core G lab F X B0 Z W (rootAdm G lab F X) hZ hZW
    (fun v hv => coreAvail_root ht ht3 hε hroute X v (hXl v hv) hA (hX v) hBud hρ)
    (fun v _ => rootAdm_empty G lab F X v) hq hX hB le_rfl le_rfl

omit [Fintype V] in
/-- An edge `vu` lying in a permitted triangle makes `u` a vertex of the link of `v`. -/
lemma link_of_allowed {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {T : Finset V} (hT : IsAllowed G lab F T) {v u : V} (hv : v ∈ T) (hu : u ∈ T)
    (hvu : v ≠ u) : ∃ y, (link G lab F v).Adj u y := by
  have h3 : T.card = 3 := hT.1
  have hc : ((T.erase v).erase u).card = 1 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨hvu.symm, hu⟩), card_erase_of_mem hv, h3]
  obtain ⟨y, hy⟩ := card_eq_one.1 hc
  have hyT : y ∈ (T.erase v).erase u := by rw [hy]; exact mem_singleton_self y
  rw [mem_erase, mem_erase] at hyT
  obtain ⟨hyu, hyv, hyT⟩ := hyT
  have hsub : ({v, u, y} : Finset V) ⊆ T := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have hcard : T.card ≤ ({v, u, y} : Finset V).card := by
    rw [h3, card_insert_of_notMem (by simp [hvu, Ne.symm hyv]),
      card_insert_of_notMem (by simp [Ne.symm hyu]), card_singleton]
  have heq := eq_of_subset_of_card_le hsub hcard
  refine ⟨y, Ne.symm hyu, ?_⟩
  convert hT using 1; convert heq

/-- Under `EdgeCovered`, every edge of `X ≤ G` at `v` makes its other end a link vertex. -/
lemma link_of_edgeCovered {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (hcov : EdgeCovered G lab F) {X : SimpleGraph V} (hXG : X ≤ G) {v u : V}
    (h : X.Adj v u) : ∃ y, (link G lab F v).Adj u y := by
  obtain ⟨T, hT, he⟩ := hcov s(v, u) (mem_edges.2 (hXG h))
  obtain ⟨hv, hu, hvu⟩ := mem_triEdges.1 he
  exact link_of_allowed hT hv hu hvu

/-- **All exterior roots at once**: `Z = V ∖ W` is admissible for the layer as soon as every edge
of `X` meets the core (e.g. `X1` of `S07V26.ForkSystem.fork_L`, item 5). -/
lemma allRoots_hyps (W : Finset V) (X : SimpleGraph V) (hXW : ∀ x y, X.Adj x y → x ∈ W ∨ y ∈ W) :
    Disjoint (univ \ W) W ∧ ∀ v ∈ univ \ W, ∀ v' ∈ univ \ W, ¬ X.Adj v v' := by
  refine ⟨sdiff_disjoint, fun v hv v' hv' h => ?_⟩
  rcases hXW v v' h with h1 | h1
  · exact (mem_sdiff.1 hv).2 h1
  · exact (mem_sdiff.1 hv').2 h1

end host

/-- **The simultaneous PAR/BAL selector layer for ALL roots on the SAME V25 core.**

Constants (`t`, `a`, `ε` from `S07_core_H3H4`; `A = 200t + 8`; `εS = selEps ε A`; `n₀`) are
fixed before the host.  For every host with H3, H4 (exactly as in `SparseEdgeDefs`) and
`n ≥ n₀` there is ONE `W` with all V25 core properties (verbatim), and for EVERY `X ≤ G`,
`B0`, root set `Z` disjoint from `W` with `X[Z]` empty, `r, b ≤ εS·n`, under `H1Load ∨ H2Phys`,
ONE family of selectors, chosen before `L`, with non-port vertices in `W`, auxiliary-use
counters `≤ q = selQ ε A r`, congestion `Δ(R) ≤ max(A r, 60 r + 61 q)`, and, for EVERY later
`L ⊆ E(X)` admissible at every root (`rootAdm`: even in PAR components, balanced in BAL
components), the exact positive partition and the charge identity. -/
theorem S07_selector_layer_native (α q0 : ℝ) (h : ℕ) (hα : 0 < α) (hq0 : 0 < q0)
    (hq1 : q0 ≤ 1) (hh : 6 ≤ h) :
    ∃ (t : ℕ) (a ε εS : ℝ) (n₀ A : ℕ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧ 0 < εS ∧
      A = selA t ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)) (_ : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h),
        n₀ ≤ Fintype.card V →
          ∃ W : Finset V,
            -- the V25 core, verbatim from `S07_core_H3H4`
            (q0 * Fintype.card V / 2 ≤ W.card ∧ (W.card : ℝ) < 2 * q0 * Fintype.card V ∧
            (∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
              q0 * α * Fintype.card V / 2 ≤ ((commonNbrs G lab k u v) ∩ W).card) ∧
            (∀ u v a' b' : V, HingeTest G lab F u v a' b' →
              α * q0 ^ (hOrd hH4 u v a' b' - 4) *
                  (Fintype.card V : ℝ) ^ (hOrd hH4 u v a' b' - 4) / 2 ≤
                ((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
                  freeV u v a' b' J ⊆ W).card) ∧
            RouteProp G lab F t ε W) ∧
            -- the simultaneous selector layer, on that same `W`
            ∀ (X B0 : SimpleGraph V) [DecidableRel X.Adj] [DecidableRel B0.Adj]
              (Z : Finset V) (r b : ℕ),
              Disjoint Z W → (∀ v ∈ Z, ∀ v' ∈ Z, ¬ X.Adj v v') → X ≤ G →
              H1Load G lab F ∨ H2Phys G lab F →
              (∀ x, X.degree x ≤ r) → (∀ x, B0.degree x ≤ b) →
              (r : ℝ) ≤ εS * Fintype.card V → (b : ℝ) ≤ εS * Fintype.card V →
              ∃ σ : V → LocalSel V,
                (∀ v ∈ Z, (σ v).W ⊆ W) ∧
                (∀ v ∈ Z, ∀ v' ∈ Z, v ≠ v' →
                  Disjoint (fuel v (σ v).P (σ v).W) (fuel v' (σ v').P (σ v').W)) ∧
                Disjoint (fuelU Z σ) (X.edgeFinset ∪ B0.edgeFinset) ∧
                (∀ v ∈ Z, (∀ w ∈ (σ v).W, w ∉ Z) ∧ ∀ f ∈ (σ v).P, ∀ y ∈ f, y ∉ Z) ∧
                (∀ x, auxCount Z (fun v => (σ v).W) x ≤ selQ ε A r) ∧
                (∀ y, edeg (fuelU Z σ) y ≤ max (A * r) (60 * r + 61 * selQ ε A r)) ∧
                ∀ L : Finset (Sym2 V), L ⊆ X.edgeFinset →
                  (∀ v ∈ Z, rootAdm G lab F X v (demand X L v)) →
                  Disjoint (fuelU Z σ) L ∧
                  fuelU Z σ ∪ L = packEdges (packing X Z σ L) ∪ residual X Z σ L ∧
                  Disjoint (packEdges (packing X Z σ L)) (residual X Z σ L) ∧
                  (packing X Z σ L : Set (V × Sym2 V)).PairwiseDisjoint
                    (fun p => triE p.1 p.2) ∧
                  (∀ p ∈ packing X Z σ L, p.1 ∈ Z ∧ ∃ x y, p.2 = s(x, y) ∧ x ≠ y ∧
                    IsAllowed G lab F {p.1, x, y}) ∧
                  (∀ f ∈ residual X Z σ L, ∀ v ∈ Z, v ∉ f) ∧
                  (∀ y, edeg (residual X Z σ L) y ≤ 61 * r + 60 * selQ ε A r) ∧
                  ∀ {M : Type} [AddCommGroup M] (c : Sym2 V → M),
                    ∑ f ∈ residual X Z σ L, c f - ∑ f ∈ residual X Z σ ∅, c f =
                      ∑ f ∈ L, c f - (∑ p ∈ packing X Z σ L, ∑ f ∈ triE p.1 p.2, c f -
                        ∑ p ∈ packing X Z σ ∅, ∑ f ∈ triE p.1 p.2, c f) := by
  obtain ⟨t, a, ε, n₀, ht, ht3, ha, hε, hmain⟩ := S07_core_H3H4 α q0 h hα hq0 hq1 hh
  set A := selA t with hAdef
  have hA0 : 0 < A := by rw [hAdef, selA]; omega
  have he0 : 0 < min ε 1 := lt_min hε one_pos
  refine ⟨t, a, ε, selEps ε A, max n₀ ⌈200 / min ε 1⌉₊, A, ht, ht3, ha, hε,
    selEps_pos hε hA0, rfl, ?_⟩
  intro V _ _ I G lab F hH3 hH4 hn
  obtain ⟨W, hW1, hW2, hpool, hhinge, hroute⟩ := hmain V I G lab F hH3 hH4
    (le_trans (le_max_left _ _) hn)
  refine ⟨W, ⟨hW1, hW2, hpool, hhinge, hroute⟩, ?_⟩
  intro X B0 _ _ Z r b hZW hZ hXG hH12 hX hB hr hb
  have hcov : EdgeCovered G lab F := hH12.elim H1Load.edgeCovered H2Phys.edgeCovered
  have hn200 : (200 : ℝ) ≤ min ε 1 * Fintype.card V := by
    have h1 : 200 / min ε 1 ≤ (⌈200 / min ε 1⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈200 / min ε 1⌉₊ : ℝ) ≤ Fintype.card V := by
      exact_mod_cast le_trans (le_max_right _ _) hn
    have := h1.trans h2
    rwa [div_le_iff₀ he0, mul_comm] at this
  obtain ⟨hBud, hρ⟩ := selector_window hε (t := t) (A := A) (by rw [hAdef, selA]) hr hb hn200
  exact selector_layer_host ht ht3 hε hroute X B0 Z hZ hZW
    (fun v _ u hvu => link_of_edgeCovered hcov hXG hvu) (by rw [hAdef, selA]; omega)
    (selQ_pos ε A r) hX hB hBud hρ

end

end S07V27
