/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V26.ForkModes
public import RequestProject.S07V26.ForkWindow

@[expose] public section

/-!
# V26 — the native uniform fork theorem on the SAME V25 core

`S07_forks_native`: the constants `t, a, ε` of `S07V25.S07_core_H3H4`, the fork sparsity
constant `εF = forkEps (qα/2)` and `n₀` are fixed from `(α, q, h)` BEFORE the host. For every
host with the ORIGINAL H3/H4 and `n ≥ n₀`, the core `W` is the one produced by
`S07_core_H3H4` (all its properties are restated verbatim in the conclusion), and for every
input edge set `X ⊆ E(G)`, every protected `P`, and degree bounds `r, b ≤ εF n`, there is ONE
fork system, fixed before any
`L ⊆ X` is chosen, with `Δ(⋃ F_e) ≤ 2r + Q + 4`, `Q = forkQ (qα/2) r ≤ 256 r/(qα) + 1`, all
auxiliaries in `W`, and for EVERY `L ⊆ X` the reduction `L ↦ L1` of `ForkSystem.fork_L`.

The existence of a permitted completion for every input edge (`EdgeCovered`) is NOT an added
hypothesis: the theorem assumes H1 or H2 of the host and derives it (`H1Load.edgeCovered`,
`H2Phys.edgeCovered`). The original H1/H2 definitions
are not present in this tree; `H1Load` and `H2Phys` are local definitions of the two shapes
named in the request (edge load `1` of a nonnegative triangle weighting; the edge indicator of
`G` in the physical lattice). Only the consequence `EdgeCovered` is used.
-/

open Finset

noncomputable section
open Classical

namespace S07V26

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24 S07V25

variable {V I : Type*} [Fintype V]

/-- every edge of `G` lies in a permitted triangle -/
def EdgeCovered (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) : Prop :=
  ∀ e ∈ edges G, ∃ T, IsAllowed G lab F T ∧ e ∈ triEdges T

/-- H1 shape: a nonnegative weighting of permitted triangles with load exactly `1` on every
edge of `G` -/
def H1Load (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) : Prop :=
  ∃ ψ : Finset V → ℝ, (∀ T, 0 ≤ ψ T) ∧ ∀ e ∈ edges G,
    ∑ T ∈ univ.filter (fun T => IsAllowed G lab F T ∧ e ∈ triEdges T), ψ T = 1

/-- H2 shape: the physical edge indicator of `G` lies in the triangle lattice -/
def H2Phys (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) : Prop :=
  TypedTriangle.SparseEdge.ind (edges G) ∈ lattice G lab F

lemma H1Load.edgeCovered {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (h : H1Load G lab F) : EdgeCovered G lab F := by
  obtain ⟨ψ, -, hψ⟩ := h
  intro e he
  by_contra hc
  push_neg at hc
  have : (univ.filter (fun T => IsAllowed G lab F T ∧ e ∈ triEdges T)) = ∅ := by
    ext T; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
    exact hc T
  have h1 := hψ e he
  rw [this, sum_empty] at h1
  exact zero_ne_one h1

omit [Fintype V] in
lemma lattice_support {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    {f : Sym2 V → ℤ} (hf : f ∈ lattice G lab F) {e : Sym2 V} (he : f e ≠ 0) :
    ∃ T, IsAllowed G lab F T ∧ e ∈ triEdges T := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    refine ⟨T, hT, ?_⟩
    by_contra hc; exact he (by simp [TypedTriangle.SparseEdge.ind, hc])
  | zero => exact absurd rfl he
  | add x y _ _ ihx ihy =>
    by_cases hx : x e = 0
    · exact ihy (by simpa [hx] using he)
    · exact ihx hx
  | smul c x _ ih =>
    exact ih (fun h => he (by simp [h]))

lemma H2Phys.edgeCovered {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}
    (h : H2Phys G lab F) : EdgeCovered G lab F := by
  intro e he
  exact lattice_support h (by simp [TypedTriangle.SparseEdge.ind, he])

/-- **native uniform fork theorem on the SAME V25 core** -/
theorem S07_forks_native (α q : ℝ) (h : ℕ) (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 6 ≤ h) :
    ∃ (t : ℕ) (a ε εF : ℝ) (n₀ : ℕ), Odd t ∧ 3 ≤ t ∧ 0 < a ∧ 0 < ε ∧ 0 < εF ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (I : Type) (G : SimpleGraph V) (lab : V → I)
        (F : Set (Multiset I)) (_ : CommonNbrCond G lab F α) (hH4 : HingeCond G lab F α h),
        n₀ ≤ Fintype.card V →
          ∃ W : Finset V,
            -- the V25 core, verbatim from `S07_core_H3H4`
            (q * Fintype.card V / 2 ≤ W.card ∧ (W.card : ℝ) < 2 * q * Fintype.card V ∧
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
                  ∀ k < t, ¬ B.Adj (p.getVert k) (p.getVert (k + 1))) ∧
            -- forks for all edges between roots, built on that same `W`
            ∀ (X P : Finset (Sym2 V)) (r b : ℕ), X ⊆ edges G → H1Load G lab F ∨ H2Phys G lab F →
              (∀ x, degIn X x ≤ r) → (∀ x, degIn P x ≤ b) →
              (r : ℝ) ≤ εF * Fintype.card V → (b : ℝ) ≤ εF * Fintype.card V →
              ∃ fk : Sym2 V → Fork V, ForkSystem G lab F W X P fk ∧
                (∀ x, x ∉ W → degIn (forkUnion (XZ X W) fk) x ≤ 2 * r) ∧
                (∀ x ∈ W, degIn (forkUnion (XZ X W) fk) x ≤ forkQ (q * α / 2) r + 3) ∧
                (∀ x, degIn (forkUnion (XZ X W) fk) x ≤ 2 * r + forkQ (q * α / 2) r + 4) ∧
                ((forkQ (q * α / 2) r : ℝ) ≤ 128 * r / (q * α / 2) + 1) ∧
                ∀ L ⊆ X,
                  (∀ D1, IsDecomposition G lab F ((L \ (L ∩ XZ X W)) ∪ QU fk (L ∩ XZ X W)) D1 →
                    IsDecomposition G lab F (L ∪ forkUnion (XZ X W) fk)
                      (D1 ∪ modeDec fk (XZ X W) (L ∩ XZ X W))) ∧
                  TypedTriangle.SparseEdge.ind L -
                    TypedTriangle.SparseEdge.ind ((L \ (L ∩ XZ X W)) ∪ QU fk (L ∩ XZ X W)) ∈
                      lattice G lab F ∧
                  (L \ (L ∩ XZ X W)) ∪ QU fk (L ∩ XZ X W) ⊆
                    (X \ XZ X W) ∪ QU fk (XZ X W) ∧
                  (∀ e ∈ (X \ XZ X W) ∪ QU fk (XZ X W), ∃ x ∈ e, x ∈ W) ∧
                  ∀ x, degIn ((X \ XZ X W) ∪ QU fk (XZ X W)) x ≤
                    r + (2 * r + forkQ (q * α / 2) r + 4) := by
  obtain ⟨t, a, ε, n₀, ht, ht3, ha, hε, hmain⟩ := S07_core_H3H4 α q h hα hq hq1 hh
  set β := q * α / 2 with hβdef
  have hβ : 0 < β := by positivity
  refine ⟨t, a, ε, forkEps β, max n₀ ⌈32 / β⌉₊, ht, ht3, ha, hε, forkEps_pos hβ, ?_⟩
  intro V _ inst I G lab F hH3 hH4 hn
  have hDec : inst = Classical.decEq V := Subsingleton.elim _ _
  cases hDec
  obtain ⟨W, hW1, hW2, hpool, hhinge, hroute⟩ := hmain V I G lab F hH3 hH4
    (le_trans (le_max_left _ _) hn)
  refine ⟨W, ⟨hW1, hW2, hpool, hhinge, hroute⟩, ?_⟩
  intro X P r b hXG hH12 hX hP hr hb
  have hcovG : EdgeCovered G lab F := hH12.elim H1Load.edgeCovered H2Phys.edgeCovered
  set n := Fintype.card V with hndef
  have hn32 : (32 : ℝ) ≤ β * n := by
    have h1 : 32 / β ≤ (⌈32 / β⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈32 / β⌉₊ : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
    have := h1.trans h2
    rwa [div_le_iff₀ hβ, mul_comm] at this
  set m := ⌈β * n⌉₊ with hmdef
  have hpool' : ∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
      m ≤ ((commonNbrs G lab k u v) ∩ W).card := by
    intro u v huv k hk
    refine Nat.ceil_le.2 ?_
    have := hpool u v huv k hk
    rw [hβdef]; linarith
  have hcov : ∀ e ∈ XZ X W, ∃ T, IsAllowed G lab F T ∧ e ∈ triEdges T :=
    fun e he => hcovG e (hXG (XZ_subset X W he))
  have hloop : ∀ e ∈ XZ X W, ¬ e.IsDiag := fun e he =>
    not_isDiag_of_mem_edges (hXG (XZ_subset X W he))
  have hdegXZ : ∀ x, degIn (XZ X W) x ≤ r := fun x =>
    (degIn_mono (XZ_subset X W) x).trans (hX x)
  have hI : 2 * ((XZ X W).card : ℝ) ≤ n * r := by
    exact_mod_cast two_card_le hloop hdegXZ
  have hwin := fork_window hβ (by positivity) hn32 hr hb hI (Nat.le_ceil _)
  obtain ⟨fk, hFS, hroot, haux, hmax, -⟩ :=
    fork_greedy (one_le_forkQ β r) (fun u v huv k hk => by convert hpool' u v huv k hk)
      hcov hX hP hwin
  refine ⟨fk, hFS, hroot, haux, hmax, forkQ_upper hβ r, fun L hL => ?_⟩
  obtain ⟨-, -, hext, hlat, hL1, hX1W, hX1deg⟩ := hFS.fork_L hL
  have hdeg := fun x => (hX1deg x).trans (Nat.add_le_add (hX x) (hmax x))
  exact ⟨hext, hlat, hL1, hX1W, hdeg⟩

end S07V26

end
