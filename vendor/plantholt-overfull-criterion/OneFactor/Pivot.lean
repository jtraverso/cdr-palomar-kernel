/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.VAL
public import Plantholt.Tools

/-!
# Pivots: adding edges at vertices without full neighbours

`colorable_of_pivot`: if all degrees are at most `k`, `G − xy` is `k`-edge-colourable, and no
neighbour of `x` other than `y` has degree `k`, then `G` is `k`-edge-colourable (Vizing's
adjacency lemma, or Vizing's theorem when `Δ(G) < k`).

Consequences:
* `colorable_of_full_indep` (**Fournier**): if the vertices of degree `k` are pairwise
  non-adjacent, then `G` is `k`-edge-colourable;
* `colorable_of_add_vertex` (Chetwynd–Hilton 1985, Lemma 1, in the form used here): if `G` minus
  the edges at `x` is `k`-edge-colourable and no neighbour of `x` has degree `k`, then so is `G`.
-/

@[expose] public section

namespace OneFactor

open SimpleGraph Finset LeanPool.Vizing Overfull

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem colorable_of_maxDegree_lt (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (h : G.maxDegree < k) : G.lineGraph.Colorable k :=
  (LeanPool.Vizing.lineGraph_colorable G).mono (by omega)

/-- **Pivot lemma.** -/
theorem colorable_of_pivot (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hmax : ∀ v, G.degree v ≤ k) {x y : V} (hxy : G.Adj x y)
    (hcol : (G.deleteEdges {s(x, y)}).lineGraph.Colorable k)
    (hpiv : ∀ z, G.Adj x z → z ≠ y → G.degree z < k) : G.lineGraph.Colorable k := by
  have hΔ : G.maxDegree ≤ k := maxDegree_le_of_forall_degree_le G k hmax
  rcases hΔ.lt_or_eq with hlt | heq
  · exact colorable_of_maxDegree_lt G hlt
  subst heq
  by_contra hnot
  obtain ⟨c, hc⟩ := exists_colMinus_of_colorable hxy hcol
  have hv := val hnot hc
  have hempty : (G.neighborFinset x).filter (fun z => z ≠ y ∧ G.degree z = G.maxDegree) = ∅ := by
    rw [filter_eq_empty_iff]
    rintro z hz ⟨hzy, hzd⟩
    have := hpiv z ((mem_neighborFinset _ _ _).1 hz) hzy
    omega
  rw [hempty, card_empty, add_zero] at hv
  have := hmax y
  omega

theorem degree_deleteEdges_le (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set (Sym2 V))
    [DecidableRel (G.deleteEdges s).Adj] (v : V) : (G.deleteEdges s).degree v ≤ G.degree v :=
  degree_le_of_le (deleteEdges_le s)

theorem card_edgeFinset_deleteEdges_lt (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    (hxy : G.Adj x y) [DecidableRel (G.deleteEdges {s(x, y)}).Adj] :
    #(G.deleteEdges {s(x, y)}).edgeFinset < #G.edgeFinset := by
  apply card_lt_card
  rw [edgeFinset_ssubset_edgeFinset]
  refine lt_of_le_of_ne (deleteEdges_le _) fun h => ?_
  have : (G.deleteEdges {s(x, y)}).Adj x y := by rw [h]; exact hxy
  rw [deleteEdges_adj] at this
  exact this.2 rfl

/-- **Fournier's theorem** (independent full vertices). -/
theorem colorable_of_full_indep {k : ℕ} :
    ∀ (m : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj], #G.edgeFinset ≤ m →
      (∀ v, G.degree v ≤ k) → (∀ u v, G.Adj u v → G.degree u = k → G.degree v < k) →
      G.lineGraph.Colorable k := by
  intro m
  induction m with
  | zero =>
    intro G _ hm _ _
    have h0 : G.edgeFinset = ∅ := card_eq_zero.1 (by omega)
    refine ⟨Coloring.mk (fun e => (?_ : False).elim) fun {e} _ => (?_ : False).elim⟩
    · have := e.2
      rw [← mem_edgeFinset, h0] at this
      exact notMem_empty _ this
    · have := e.2
      rw [← mem_edgeFinset, h0] at this
      exact notMem_empty _ this
  | succ m ih =>
    intro G _ hm hmax hind
    by_cases hfull : ∃ x, G.degree x = k ∧ 0 < k
    · obtain ⟨x, hx, hk⟩ := hfull
      obtain ⟨y, hy⟩ : ∃ y, G.Adj x y := by
        have : 0 < G.degree x := by omega
        obtain ⟨y, hy⟩ := card_pos.1
          (show 0 < #(G.neighborFinset x) by rwa [card_neighborFinset_eq_degree])
        exact ⟨y, (mem_neighborFinset _ _ _).1 hy⟩
      classical
      refine colorable_of_pivot G hmax hy ?_ fun z hz _ => hind x z hz hx
      apply ih (G.deleteEdges {s(x, y)})
      · have := card_edgeFinset_deleteEdges_lt G hy; omega
      · intro v; exact (degree_deleteEdges_le G _ v).trans (hmax v)
      · intro u v huv hu
        have hu' : G.degree u = k :=
          le_antisymm (hmax u) (hu ▸ degree_deleteEdges_le G _ u)
        exact (degree_deleteEdges_le G _ v).trans_lt
          (hind u v (deleteEdges_le _ huv) hu')
    · push_neg at hfull
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · -- `k = 0`: no edges
        refine ⟨Coloring.mk (fun e => (?_ : False).elim) fun {e} _ => (?_ : False).elim⟩ <;>
        · obtain ⟨e, he⟩ := e
          induction e using Sym2.inductionOn with
          | hf u v =>
            have h1 := hmax u
            have : 0 < G.degree u := by
              rw [← card_neighborFinset_eq_degree]
              exact card_pos.2 ⟨v, (mem_neighborFinset _ _ _).2 he⟩
            omega
      · apply colorable_of_maxDegree_lt
        have := maxDegree_le_of_forall_degree_le G (k - 1) fun v => by
          have := hmax v
          have h' : G.degree v ≠ k := fun h => by have := hfull v h; omega
          omega
        omega

/-- The graph `G` with the edges from `x` to vertices outside `T` removed. -/
def keepAt (G : SimpleGraph V) (x : V) (T : Finset V) : SimpleGraph V :=
  G.deleteEdges {e | x ∈ e ∧ ∀ z ∈ T, e ≠ s(x, z)}

theorem keepAt_le (G : SimpleGraph V) (x : V) (T : Finset V) : keepAt G x T ≤ G :=
  deleteEdges_le _

theorem keepAt_insert (G : SimpleGraph V) (x : V) {T : Finset V} {y : V} (hy : y ∉ T)
    (hxy : x ≠ y) :
    (keepAt G x (insert y T)).deleteEdges {s(x, y)} = keepAt G x T := by
  ext a b
  simp only [keepAt, deleteEdges_adj, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hab, h1⟩, h2⟩
    refine ⟨hab, fun ⟨hx, hall⟩ => h1 ⟨hx, fun z hz => ?_⟩⟩
    rcases mem_insert.1 hz with rfl | hz
    · exact h2
    · exact hall z hz
  · rintro ⟨hab, h1⟩
    refine ⟨⟨hab, fun ⟨hx, hall⟩ => h1 ⟨hx, fun z hz => hall z (mem_insert_of_mem hz)⟩⟩,
      fun he => ?_⟩
    apply h1
    refine ⟨by rw [he]; exact Sym2.mem_mk_left _ _, fun z hz hez => ?_⟩
    rw [he] at hez
    rcases Sym2.eq_iff.1 hez with ⟨-, h⟩ | ⟨-, h⟩
    · exact hy (h ▸ hz)
    · exact hxy h.symm

/-- **Adding a vertex.** If `G` minus the edges at `x` is `k`-edge-colourable, all degrees are at
most `k`, and no neighbour of `x` has degree `k`, then `G` is `k`-edge-colourable. -/
theorem colorable_of_add_vertex (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (hmax : ∀ v, G.degree v ≤ k) (x : V) (hx : ∀ z, G.Adj x z → G.degree z < k)
    (hcol : (keepAt G x ∅).lineGraph.Colorable k) : G.lineGraph.Colorable k := by
  classical
  have key : ∀ T : Finset V, T ⊆ G.neighborFinset x → (keepAt G x T).lineGraph.Colorable k := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact hcol
    | insert y T hyT ih =>
      intro hsub
      have hxy : G.Adj x y := (mem_neighborFinset _ _ _).1 (hsub (mem_insert_self _ _))
      have hadj : (keepAt G x (insert y T)).Adj x y := by
        simp only [keepAt, deleteEdges_adj, Set.mem_setOf_eq]
        exact ⟨hxy, fun ⟨_, h⟩ => h y (mem_insert_self _ _) rfl⟩
      refine colorable_of_pivot _ (fun v => (degree_le_of_le (keepAt_le G x _)).trans (hmax v))
        hadj ?_ fun z hz _ => (degree_le_of_le (keepAt_le G x _)).trans_lt
          (hx z (keepAt_le G x _ hz))
      rw [keepAt_insert G x hyT hxy.ne]
      exact ih (fun z hz => hsub (mem_insert_of_mem hz))
  have hall : keepAt G x (G.neighborFinset x) = G := by
    ext a b
    simp only [keepAt, deleteEdges_adj, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.1
    · intro hab
      refine ⟨hab, fun ⟨hx, hall⟩ => ?_⟩
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · exact hall b ((mem_neighborFinset _ _ _).2 hab) rfl
      · exact hall a ((mem_neighborFinset _ _ _).2 hab.symm) Sym2.eq_swap
  rw [← hall]
  exact key _ subset_rfl

end OneFactor
