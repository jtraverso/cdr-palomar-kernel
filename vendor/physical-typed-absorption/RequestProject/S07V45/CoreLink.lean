/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V42.Setting
public import RequestProject.S07V25.CoreH3H4
public import RequestProject.TypedTriangle.ComponentRowsConverse
public import RequestProject.TypedTriangle.ActiveCover
@[expose] public section

/-!
# V45 §1 — the core link of `indG H W` and parity along walks

* `allowed_indG_iff` — allowed triangles of the core host `indG H W` (= `H[W]` zero-extended) are
  the allowed triangles of `H` inside `W`;
* `link_indG_adj` — the link of the core host at `v` is the link of `H` at `v` restricted to `W`,
  and empty when `v ∉ W`;
* `walk_to_core` — a walk of the original link whose vertices all lie in `W` (root in `W`) is a
  walk of the core link of the same length;
* `walk_starIm` — along a walk of length `ℓ` of a link from `a` to `b`, `δ_a - (-1)^ℓ δ_b` lies in
  the integer image `starIm` of the unoriented incidence of that link (integral, no real span);
* `walk_col_parity` — along a walk inside `K`, any proper colouring of the link on `K` changes
  exactly according to the parity of the length.
-/

open Finset Classical

noncomputable section

namespace S07V45

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.ActiveCover S07V42

variable {V I : Type*}

section core

variable {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {W : Finset V}

/-- allowed triangles of the core host are the allowed triangles of `H` inside `W` -/
theorem allowed_indG_iff {T : Finset V} :
    IsAllowed (indG H W) lab F T ↔ IsAllowed H lab F T ∧ ∀ x ∈ T, x ∈ W := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, fun x hx y hy hxy => (h2 x hx y hy hxy).1, h3⟩, fun x hx => ?_⟩
    obtain ⟨y, hy, hxy⟩ : ∃ y ∈ T, x ≠ y := by
      by_contra hc
      push_neg at hc
      have hsub : T ⊆ {x} := fun y hy => by rw [Finset.mem_singleton]; exact (hc y hy).symm
      have := card_le_card hsub
      rw [Finset.card_singleton] at this
      omega
    exact (h2 x hx y hy hxy).2.1
  · rintro ⟨⟨h1, h2, h3⟩, hW⟩
    exact ⟨h1, fun x hx y hy hxy => ⟨h2 x hx y hy hxy, hW x hx, hW y hy⟩, h3⟩

/-- **the core link**: adjacency in the link of `indG H W` at `v` -/
theorem link_indG_adj {v u w : V} :
    (link (indG H W) lab F v).Adj u w ↔
      (link H lab F v).Adj u w ∧ v ∈ W ∧ u ∈ W ∧ w ∈ W := by
  show (u ≠ w ∧ IsAllowed (indG H W) lab F {v, u, w}) ↔
    (u ≠ w ∧ IsAllowed H lab F {v, u, w}) ∧ v ∈ W ∧ u ∈ W ∧ w ∈ W
  rw [allowed_indG_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  tauto

lemma link_indG_le (v : V) : link (indG H W) lab F v ≤ link H lab F v :=
  fun _ _ h => (link_indG_adj.1 h).1

/-- a walk of the original link with all vertices in `W` (root in `W`) is a core-link walk of the
same length -/
theorem walk_to_core {v a b : V} (hv : v ∈ W) (p : (link H lab F v).Walk a b)
    (hp : ∀ u ∈ p.support, u ∈ W) :
    ∃ q : (link (indG H W) lab F v).Walk a b, q.length = p.length ∧
      q.support = p.support := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl, rfl⟩
  | @cons a c b hac p ih =>
    have ha : a ∈ W := hp a (by simp)
    have hc : c ∈ W := hp c (by simp)
    obtain ⟨q, hq, hqs⟩ := ih (fun u hu => hp u (by simp [hu]))
    exact ⟨SimpleGraph.Walk.cons (link_indG_adj.2 ⟨hac, hv, ha, hc⟩) q, by simp [hq],
      by simp [hqs]⟩

/-- core-link reachability from a vertex of `W` stays in `W` -/
lemma reach_core_mem {v u w : V} (h : (link (indG H W) lab F v).Reachable u w) (hu : u ∈ W) :
    w ∈ W := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (link_indG_adj.1 hadj).2.2.2

end core

section parity

variable [Fintype V] (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))

/-- **integral parity transport along a walk**: `δ_a - (-1)^ℓ δ_b ∈ starIm` -/
theorem walk_starIm {v a b : V} (p : (link G lab F v).Walk a b) :
    (Even p.length → dl a - dl b ∈ starIm G lab F v) ∧
      (Odd p.length → dl a + dl b ∈ starIm G lab F v) := by
  induction p with
  | nil => exact ⟨fun _ => by simp, fun h => absurd h (by simp)⟩
  | @cons a c b hac p ih =>
    have h1 := adj_mem_starIm G lab F hac
    rw [SimpleGraph.Walk.length_cons]
    refine ⟨fun he => ?_, fun ho => ?_⟩
    · have hpo : Odd p.length := by
        rcases Nat.even_or_odd p.length with h | h
        · exact absurd he (by rw [Nat.even_add_one]; exact not_not.2 h)
        · exact h
      have := Submodule.sub_mem _ h1 (ih.2 hpo)
      have e : dl a + dl c - (dl c + dl b) = dl a - dl b := by abel
      rwa [e] at this
    · have hpe : Even p.length := by
        rcases Nat.even_or_odd p.length with h | h
        · exact h
        · exact absurd ho (by rw [Nat.odd_add_one]; exact not_not.2 h)
      have := Submodule.sub_mem _ h1 (ih.1 hpe)
      have e : dl a + dl c - (dl c - dl b) = dl a + dl b := by abel
      rwa [e] at this

omit [Fintype V] in
/-- **colour parity along a walk** inside `K` for a proper colouring of the link on `K` -/
theorem walk_col_parity {v a b : V} {K : Finset V} {c : V → Bool}
    (hc : ∀ u ∈ K, ∀ w ∈ K, (link G lab F v).Adj u w → c u ≠ c w)
    (p : (link G lab F v).Walk a b) (hp : ∀ u ∈ p.support, u ∈ K) :
    xor (c a) (c b) = decide (Odd p.length) := by
  induction p with
  | nil => simp
  | @cons a m b ham p ih =>
    have hne := hc a (hp a (by simp)) m (hp m (by simp)) ham
    have ih' := ih (fun u hu => hp u (by simp [hu]))
    rw [SimpleGraph.Walk.length_cons]
    have : decide (Odd (p.length + 1)) = !decide (Odd p.length) := by
      simp [Nat.odd_add_one, -Nat.not_odd_iff_even]
    rw [this, ← ih']
    revert hne
    cases c a <;> cases c m <;> cases c b <;> simp

end parity

end S07V45
