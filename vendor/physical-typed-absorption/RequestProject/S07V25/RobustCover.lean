/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V25.RobustAbstract

@[expose] public section

/-!
# V25 — the double cover `S07V24.dcover`: lifting walks, robustness, connectivity

* `lift_walk` — a walk of `K` from `a` to `b` lifts to `dcover K` from `(a, s)` to `(b, t)` with
  `t = s ↔` the length is even; supports and edges project back exactly.
* `cover_local` — `EvenRobustLocal K s (2d) ⇒ RobustLocal (dcover K) s d` (the factor `2` in the
  degree budget is paid explicitly: a cover edge set of maximum degree `d` projects to one of
  maximum degree `≤ 2d`).
* `cover_preconnected` — `K` preconnected without proper `Bool` colouring ⇒ `dcover K`
  preconnected.
-/

open Finset

namespace S07V25

open S07V24

variable {β : Type*} [DecidableEq β]

omit [DecidableEq β] in
/-- **lifting walks to the double cover** -/
theorem lift_walk (K : SimpleGraph β) : ∀ {a b : β} (p : K.Walk a b) (s : Bool),
    ∃ t : Bool, ∃ q : (dcover K).Walk (a, s) (b, t), (t = s ↔ Even p.length) ∧
      q.support.map Prod.fst = p.support ∧ q.edges.map (Sym2.map Prod.fst) = p.edges := by
  intro a b p
  induction p with
  | nil => intro s; exact ⟨s, .nil, by simp, by simp, by simp⟩
  | @cons a c b h p ih =>
    intro s
    obtain ⟨t, q, ht, hs, he⟩ := ih (!s)
    have hadj : (dcover K).Adj (a, s) (c, !s) := ⟨h, by cases s <;> simp⟩
    refine ⟨t, .cons hadj q, ?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ← ht]
      cases t <;> cases s <;> simp
    · simp [hs]
    · simp [he]

omit [DecidableEq β] in
/-- reachability lifts -/
lemma lift_reach (K : SimpleGraph β) {a b : β} (h : K.Reachable a b) (s : Bool) :
    ∃ t, (dcover K).Reachable (a, s) (b, t) := by
  obtain ⟨p⟩ := h
  obtain ⟨t, q, -⟩ := lift_walk K p s
  exact ⟨t, ⟨q⟩⟩

/-- **even local robustness lifts to the cover** -/
theorem cover_local (K : SimpleGraph β) (s d : ℕ) (h : EvenRobustLocal K s (2 * d)) :
    RobustLocal (dcover K) s d := by
  rintro ⟨u, t⟩ ⟨a, ta⟩ ⟨b, tb⟩ ⟨hua, htua⟩ ⟨hub, htub⟩ hab S' hS' B' hB'
  simp only at hua hub htua htub
  have htab : ta = tb := by cases t <;> cases ta <;> cases tb <;> simp_all
  subst htab
  have hab' : a ≠ b := fun h' => hab (by rw [h'])
  set S := S'.image Prod.fst
  set B := B'.image (Sym2.map Prod.fst)
  have hS : S.card ≤ s := (card_image_le).trans hS'
  have hB : ∀ x, degB B x ≤ 2 * d := by
    intro x
    unfold degB
    have hsub : B.filter (fun e => x ∈ e) ⊆
        ((B'.filter (fun e => (x, false) ∈ e)) ∪ (B'.filter (fun e => (x, true) ∈ e))).image
          (Sym2.map Prod.fst) := by
      intro e he
      simp only [B, mem_filter, mem_image] at he
      obtain ⟨⟨e', he', rfl⟩, hx⟩ := he
      obtain ⟨⟨y, c⟩, hyc, hy⟩ := Sym2.mem_map.1 hx
      simp only at hy; subst hy
      refine mem_image.2 ⟨e', ?_, rfl⟩
      cases c
      · exact mem_union_left _ (mem_filter.2 ⟨he', hyc⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨he', hyc⟩)
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_image_le
      _ ≤ _ := card_union_le _ _
      _ ≤ d + d := Nat.add_le_add (hB' (x, false)) (hB' (x, true))
      _ = 2 * d := by ring
  obtain ⟨p, hpath, heven, hpS, hpB⟩ := h u a b hua hub hab' S hS B hB
  obtain ⟨t', q, ht', hqs, hqe⟩ := lift_walk K p ta
  have : t' = ta := ht'.2 heven
  subst this
  have hnd : (q.support.map Prod.fst).Nodup := by rw [hqs]; exact hpath.support_nodup
  refine ⟨q, ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]; exact hnd.of_map _
  · intro z hz hzS
    have hz1 : z.1 ∈ S := mem_image_of_mem _ hzS
    have hz2 : z.1 ∈ p.support := by rw [← hqs]; exact List.mem_map_of_mem hz
    rcases hpS z.1 hz2 hz1 with h1 | h1
    · left; exact List.inj_on_of_nodup_map hnd hz q.start_mem_support h1
    · right; exact List.inj_on_of_nodup_map hnd hz q.end_mem_support h1
  · intro e he heB
    have h1 : Sym2.map Prod.fst e ∈ p.edges := by rw [← hqe]; exact List.mem_map_of_mem he
    exact hpB _ h1 (mem_image_of_mem _ heB)

omit [DecidableEq β] in
/-- **the cover of a connected non-bipartite graph is connected** -/
theorem cover_preconnected (K : SimpleGraph β) (hK : K.Preconnected)
    (hnb : ¬ ∃ col : β → Bool, ∀ x y, K.Adj x y → col x ≠ col y) :
    (dcover K).Preconnected := by
  rintro ⟨x0, s0⟩ w
  set U : β × Bool := (x0, s0)
  -- if some vertex has both sheets reachable, everything is reachable
  have hall : (∃ y, (dcover K).Reachable U (y, s0) ∧ (dcover K).Reachable U (y, !s0)) →
      ∀ z, (dcover K).Reachable U z := by
    rintro ⟨y, h1, h2⟩ ⟨z, c⟩
    obtain ⟨p⟩ := hK y z
    obtain ⟨t1, q1, ht1, -⟩ := lift_walk K p s0
    obtain ⟨t2, q2, ht2, -⟩ := lift_walk K p (!s0)
    have r1 := h1.trans ⟨q1⟩
    have r2 := h2.trans ⟨q2⟩
    by_cases hc1 : c = t1
    · subst hc1; exact r1
    · have : c = t2 := by
        by_cases he : Even p.length
        · have e1 : t1 = s0 := ht1.2 he
          have e2 : t2 = !s0 := ht2.2 he
          rw [e2]; rw [e1] at hc1
          revert hc1; cases s0 <;> cases c <;> decide
        · have h1' : t1 ≠ s0 := fun h => he (ht1.1 h)
          have h2' : t2 ≠ !s0 := fun h => he (ht2.1 h)
          revert hc1 h1' h2'; cases s0 <;> cases c <;> cases t1 <;> cases t2 <;> decide
      subst this; exact r2
  by_cases hb : ∃ y, (dcover K).Reachable U (y, s0) ∧ (dcover K).Reachable U (y, !s0)
  · exact hall hb w
  exfalso
  push_neg at hb
  apply hnb
  classical
  refine ⟨fun y => decide ((dcover K).Reachable U (y, s0)), fun x y hxy => ?_⟩
  have some_sheet : ∀ y, (dcover K).Reachable U (y, s0) ∨ (dcover K).Reachable U (y, !s0) := by
    intro y
    obtain ⟨t, ht⟩ := lift_reach K (hK x0 y) s0
    by_cases h : t = s0
    · left; rw [← h]; exact ht
    · right
      have : t = !s0 := by revert h; cases t <;> cases s0 <;> decide
      rw [← this]; exact ht
  have adj_flip : ∀ c, (dcover K).Adj (x, c) (y, !c) := fun c => ⟨hxy, by cases c <;> simp⟩
  by_cases hx : (dcover K).Reachable U (x, s0)
  · by_cases hy : (dcover K).Reachable U (y, s0)
    · exact absurd (hx.trans (adj_flip s0).reachable) (hb y hy)
    · simp [hx, hy]
  · by_cases hy : (dcover K).Reachable U (y, s0)
    · simp [hx, hy]
    · have hx' : (dcover K).Reachable U (x, !s0) := (some_sheet x).resolve_left hx
      have := hx'.trans (adj_flip (!s0)).reachable
      simp only [Bool.not_not] at this
      exact absurd this hy

end S07V25
