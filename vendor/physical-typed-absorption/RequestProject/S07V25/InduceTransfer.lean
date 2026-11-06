/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V25.RobustAbstract

@[expose] public section

/-!
# V25 — transfer to the induced component graph `L.induce C`

For a neighbour-closed vertex set `C` of a graph `L` (e.g. a component of the link):

* `lift_induce` — every walk of `L` starting in `C` is the image of a walk of `L.induce C`
  (same length, supports and edges map exactly);
* `induce_evenRobust` — `EvenRobustLocal L s d ⇒ EvenRobustLocal (L.induce C) s d`;
* `induce_preconnected` — if all of `C` is reachable from one vertex, `L.induce C` is
  preconnected;
* `induce_degree_ge` — the induced degree equals the ambient degree (lower bound direction).
-/

open Finset

namespace S07V25

variable {V : Type*} [DecidableEq V]

/-- neighbour-closed vertex set -/
def NbrClosed (L : SimpleGraph V) (C : Set V) : Prop := ∀ x y, x ∈ C → L.Adj x y → y ∈ C

omit [DecidableEq V] in
lemma induce_adj_iff {L : SimpleGraph V} {C : Set V} {x y : C} :
    (L.induce C).Adj x y ↔ L.Adj x.1 y.1 := Iff.rfl

omit [DecidableEq V] in
/-- **walks of a closed set lift to the induced graph** -/
theorem lift_induce {L : SimpleGraph V} {C : Set V} (hC : NbrClosed L C) :
    ∀ {a b : V} (p : L.Walk a b) (ha : a ∈ C), ∃ hb : b ∈ C,
      ∃ q : (L.induce C).Walk ⟨a, ha⟩ ⟨b, hb⟩, q.length = p.length ∧
        q.support.map Subtype.val = p.support ∧ q.edges.map (Sym2.map Subtype.val) = p.edges := by
  intro a b p
  induction p with
  | nil => intro ha; exact ⟨ha, .nil, rfl, by simp, by simp⟩
  | @cons a c b h p ih =>
    intro ha
    have hc : c ∈ C := hC a c ha h
    obtain ⟨hb, q, hl, hs, he⟩ := ih hc
    refine ⟨hb, .cons (show (L.induce C).Adj ⟨a, ha⟩ ⟨c, hc⟩ from h) q, by simp [hl],
      by simp [hs], by simp [he]⟩

/-- **local robustness passes to the induced graph** -/
theorem induce_evenRobust [Fintype V] {L : SimpleGraph V} {C : Set V} (hC : NbrClosed L C)
    {s d : ℕ} (h : EvenRobustLocal L s d) : EvenRobustLocal (L.induce C) s d := by
  intro u a b hua hub hab S hS B hB
  set S' : Finset V := S.map (Function.Embedding.subtype _)
  set B' : Finset (Sym2 V) := B.image (Sym2.map Subtype.val)
  have hS' : S'.card ≤ s := by rw [card_map]; exact hS
  have hB' : ∀ x, degB B' x ≤ d := by
    intro x
    unfold degB
    by_cases hx : x ∈ C
    · refine le_trans ?_ (hB ⟨x, hx⟩)
      unfold degB
      have hsub : B'.filter (fun e => x ∈ e) ⊆
          (B.filter (fun e => (⟨x, hx⟩ : C) ∈ e)).image (Sym2.map Subtype.val) := by
        intro e he
        simp only [B', mem_filter, mem_image] at he
        obtain ⟨⟨e', he', rfl⟩, hxe⟩ := he
        obtain ⟨y, hy, hyx⟩ := Sym2.mem_map.1 hxe
        refine mem_image.2 ⟨e', mem_filter.2 ⟨he', ?_⟩, rfl⟩
        have : y = ⟨x, hx⟩ := Subtype.ext hyx
        rwa [← this]
      exact (card_le_card hsub).trans card_image_le
    · have : B'.filter (fun e => x ∈ e) = ∅ := by
        apply filter_false_of_mem
        intro e he hxe
        simp only [B', mem_image] at he
        obtain ⟨e', -, rfl⟩ := he
        obtain ⟨y, -, hyx⟩ := Sym2.mem_map.1 hxe
        exact hx (hyx ▸ y.2)
      rw [this]; simp
  have hab' : a.1 ≠ b.1 := fun h' => hab (Subtype.ext h')
  obtain ⟨p, hp, hpe, hpS, hpB⟩ := h u.1 a.1 b.1 hua hub hab' S' hS' B' hB'
  obtain ⟨hb, q, hl, hs, he⟩ := lift_induce hC p a.2
  have hnd : (q.support.map Subtype.val).Nodup := by rw [hs]; exact hp.support_nodup
  refine ⟨q, ?_, by rw [hl]; exact hpe, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]; exact hnd.of_map _
  · intro z hz hzS
    have h1 : z.1 ∈ S' := by simp [S', hzS]
    have h2 : z.1 ∈ p.support := by rw [← hs]; exact List.mem_map_of_mem hz
    rcases hpS z.1 h2 h1 with h' | h'
    · left; exact Subtype.ext h'
    · right; exact Subtype.ext h'
  · intro e heq heB
    have h1 : Sym2.map Subtype.val e ∈ p.edges := by rw [← he]; exact List.mem_map_of_mem heq
    exact hpB _ h1 (mem_image_of_mem _ heB)

omit [DecidableEq V] in
/-- **a reachability class induces a preconnected graph** -/
theorem induce_preconnected {L : SimpleGraph V} {C : Set V} (hC : NbrClosed L C) (x0 : V)
    (hreach : ∀ x ∈ C, L.Reachable x0 x) : (L.induce C).Preconnected := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨p⟩ := (hreach x hx).symm.trans (hreach y hy)
  obtain ⟨hb, q, -⟩ := lift_induce hC p hx
  exact ⟨q⟩

omit [DecidableEq V] in
/-- **induced degree** -/
theorem induce_degree_ge [Fintype V] {L : SimpleGraph V} [DecidableRel L.Adj] {C : Set V}
    [Fintype C] [DecidableRel (L.induce C).Adj] (hC : NbrClosed L C) (w : C) :
    L.degree w.1 ≤ (L.induce C).degree w := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  have : L.neighborFinset w.1 ⊆ ((L.induce C).neighborFinset w).map
      (Function.Embedding.subtype _) := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    have hyC : y ∈ C := hC w.1 y w.2 hy
    refine mem_map.2 ⟨⟨y, hyC⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset]; exact hy
  exact (card_le_card this).trans (by rw [card_map])

end S07V25
