/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V25.CompH3H4

@[expose] public section

/-!
# V25 — ONE random core from the ORIGINAL H3/H4 with native component/path inputs

`S07_core_H3H4` composes `compInterface_H3H4` with `S07V24.S07_layer12`. The family of
components is now NATIVE: for every root `v`, `activeComps G lab F v` is the set of components
`comp G lab F v x` of the typed link `L_v = ComponentRows.link G lab F v` through non-isolated
vertices `x` (every link edge lies in one, `link_edge_mem_activeComps`); the bipartite flag is
`IsBip G lab F (v, C)` and the colouring is the row colouring `colG G lab F v`. No
`CompInterface`, expansion or path-count hypothesis remains: the only hypotheses on the host are
`CommonNbrCond G lab F α` (H3) and `HingeCond G lab F α h` (H4), unchanged, and `n ≥ n₀`.

The constants `t` (odd, `≥ 3`), `a > 0`, `ε > 0`, `n₀` depend only on `(α, q, h)` and are fixed
BEFORE the host and before its label set `I`.
-/

open Finset

namespace S07V25

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24

variable {V I : Type*} [Fintype V]

open Classical in
/-- the active components of the typed link of `v` -/
noncomputable def activeComps (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V) :
    Finset (Finset V) :=
  (univ.filter (fun x => ∃ y, (link G lab F v).Adj x y)).image (comp G lab F v)

lemma mem_activeComps {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    {C : Finset V} :
    C ∈ activeComps G lab F v ↔ ∃ x, (∃ y, (link G lab F v).Adj x y) ∧ comp G lab F v x = C := by
  classical
  unfold activeComps
  simp only [mem_image, mem_filter, mem_univ, true_and]

/-- every edge of the typed link lies in an active component -/
theorem link_edge_mem_activeComps {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {v x y : V} (hxy : (link G lab F v).Adj x y) :
    ∃ C ∈ activeComps G lab F v, x ∈ C ∧ y ∈ C := by
  refine ⟨comp G lab F v x, mem_activeComps.2 ⟨x, ⟨y, hxy⟩, rfl⟩, ?_, ?_⟩
  · simp [comp]
  · simp only [comp, mem_filter, mem_univ, true_and]; exact hxy.reachable

/-- the native interface family from H3/H4 -/
theorem activeComps_interface {V I : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {lab : V → I} {F : Set (Multiset I)} {α : ℝ} {h : ℕ} (hα : 0 < α)
    (hH3 : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h)
    (hn : n1Of α ≤ Fintype.card V) [∀ v, DecidableRel (link G lab F v).Adj] :
    ∀ v, ∀ C ∈ activeComps G lab F v, CompInterface (link G lab F v) α (kappaOf α h)
      (Fintype.card V) C (IsBip G lab F (v, C)) (colG G lab F v) := by
  intro v C hC
  obtain ⟨x0, hx0, rfl⟩ := mem_activeComps.1 hC
  exact compInterface_H3H4 hα hH3 hH4 hn v x0 hx0

open Classical in
/-- **ONE robust random core from the ORIGINAL H3/H4, native components** -/
theorem S07_core_H3H4 (α q : ℝ) (h : ℕ) (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1) (hh : 6 ≤ h) :
    ∃ (t : ℕ) (a ε : ℝ) (n₀ : ℕ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)) (_ : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h),
        n₀ ≤ Fintype.card V →
          ∃ W : Finset V,
            q * Fintype.card V / 2 ≤ W.card ∧ (W.card : ℝ) < 2 * q * Fintype.card V ∧
            (∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
              q * α * Fintype.card V / 2 ≤ ((commonNbrs G lab k u v) ∩ W).card) ∧
            (∀ u v a' b' : V, HingeTest G lab F u v a' b' →
              α * q ^ (hOrd hH4 u v a' b' - 4) *
                  (Fintype.card V : ℝ) ^ (hOrd hH4 u v a' b' - 4) / 2 ≤
                ((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
                  freeV u v a' b' J ⊆ W).card) ∧
            ∀ (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ),
              (Z.card : ℝ) ≤ ε * Fintype.card V → (∀ u, B.degree u ≤ d) →
              (d : ℝ) ≤ ε * Fintype.card V →
              ∀ v x y, AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C))
                  (colG G lab F) v x y →
                ∃ p ∈ pathsLen (link G lab F v) t x y, intlSet (t - 1) p ⊆ W ∧
                  (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z) ∧
                  ∀ k < t, ¬ B.Adj (p.getVert k) (p.getVert (k + 1)) := by
  obtain ⟨t, a, ε, n₀, ht, ht3, ha, hε, hmain⟩ :=
    S07_layer12 α (kappaOf α h) α q h hα (kappaOf_pos hα h) hα hq hq1 hh
  refine ⟨t, a, ε, max n₀ (n1Of α), ht, ht3, ha, hε, ?_⟩
  intro V _ _ I G lab F hH3 hH4 hn
  exact hmain V I G lab F hH3 hH4 (le_trans (le_max_left _ _) hn) (link G lab F)
    (activeComps G lab F) (fun v C => IsBip G lab F (v, C)) (colG G lab F)
    (activeComps_interface hα hH3 hH4 (le_trans (le_max_right _ _) hn))

end S07V25
