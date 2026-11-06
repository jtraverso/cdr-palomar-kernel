/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V48.SeedPackage
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# V49 §1 — the typed link of the edge-deleted host `G \ B`

For a sparse graph `B` of forbidden edges, the link of the edge-deleted host is

  `(link (G \ B) v).Adj x y ↔ (link G v).Adj x y ∧ ¬B v x ∧ ¬B v y ∧ ¬B x y`

(`link_sdiff_adj`): a link edge survives iff its path edge AND both of its spokes survive.

This file proves the original/residual relation of components and colourings WITHOUT assuming
that residual admissible pairs are original admissible pairs:

* `resid_comp_orig` — every residual active component `C'` lies inside one original active
  component `C`, all its vertices have intact spokes, and if `C` is bipartite then `C'` is
  bipartite and the CHOSEN residual colouring equals the restricted original colouring up to one
  flip (uniqueness of proper 2-colourings on the connected residual component);
* `resid_adm_orig` — consequently a residual admissible pair (residual components, residual
  bipartiteness, residual chosen colouring) is an original admissible pair, and both endpoints
  have intact spokes;
* `residual_walk` — an original link walk whose vertices have intact spokes and whose path edges
  avoid `B` is a residual link walk with the same vertices.
-/

open Finset

noncomputable section
open Classical

namespace S07V49

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24 S07V25 S07V45 S07V42

variable {V I : Type*} [Fintype V] [DecidableEq V] {G B : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)}

omit [Fintype V] [DecidableEq V] in
/-- vertices of a transferred walk -/
theorem walk_getVert_transfer {H : SimpleGraph V} : ∀ {u w : V} (p : G.Walk u w)
    (hp : ∀ e ∈ p.edges, e ∈ H.edgeSet) (i : ℕ), (p.transfer H hp).getVert i = p.getVert i
  | _, _, .nil, hp, i => by simp [SimpleGraph.Walk.transfer]
  | _, _, .cons h p, hp, i => by
    cases i with
    | zero => simp [SimpleGraph.Walk.transfer]
    | succ i =>
      simp only [SimpleGraph.Walk.transfer, SimpleGraph.Walk.getVert_cons_succ]
      exact walk_getVert_transfer p _ i

omit [Fintype V] [DecidableEq V] in
/-- allowed triangles of `G \ B` -/
theorem allowed_sdiff_iff {T : Finset V} :
    IsAllowed (G \ B) lab F T ↔ IsAllowed G lab F T ∧ ∀ x ∈ T, ∀ y ∈ T, ¬ B.Adj x y := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, fun x hx y hy hxy => ((SimpleGraph.sdiff_adj _ _ _ _).1
      (h2 x hx y hy hxy)).1, h3⟩, fun x hx y hy hB => ?_⟩
    by_cases hxy : x = y
    · subst hxy; exact B.irrefl hB
    · exact ((SimpleGraph.sdiff_adj _ _ _ _).1 (h2 x hx y hy hxy)).2 hB
  · rintro ⟨⟨h1, h2, h3⟩, hB⟩
    exact ⟨h1, fun x hx y hy hxy =>
      (SimpleGraph.sdiff_adj _ _ _ _).2 ⟨h2 x hx y hy hxy, hB x hx y hy⟩, h3⟩

omit [Fintype V] [DecidableEq V] in
/-- **the residual link**: path edge and both spokes must survive -/
theorem link_sdiff_adj {v x y : V} :
    (link (G \ B) lab F v).Adj x y ↔
      (link G lab F v).Adj x y ∧ ¬ B.Adj v x ∧ ¬ B.Adj v y ∧ ¬ B.Adj x y := by
  show (x ≠ y ∧ IsAllowed (G \ B) lab F {v, x, y}) ↔
    (x ≠ y ∧ IsAllowed G lab F {v, x, y}) ∧ _
  rw [allowed_sdiff_iff]
  constructor
  · rintro ⟨hxy, hA, hB⟩
    exact ⟨⟨hxy, hA⟩, hB v (by simp) x (by simp), hB v (by simp) y (by simp),
      hB x (by simp) y (by simp)⟩
  · rintro ⟨⟨hxy, hA⟩, h1, h2, h3⟩
    refine ⟨hxy, hA, ?_⟩
    intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact B.irrefl
      | exact h1 | exact h2 | exact h3
      | exact fun h => h1 (h.symm)
      | exact fun h => h2 (h.symm)
      | exact fun h => h3 (h.symm)

omit [Fintype V] [DecidableEq V] in
theorem link_sdiff_le (v : V) : link (G \ B) lab F v ≤ link G lab F v :=
  fun _ _ h => (link_sdiff_adj.1 h).1

omit [Fintype V] [DecidableEq V] in
/-- two proper 2-colourings differ by a constant along any walk inside the coloured set -/
theorem xor_walk_const {L : SimpleGraph V} {S : Set V} {c1 c2 : V → Bool}
    (h1 : ∀ u ∈ S, ∀ w ∈ S, L.Adj u w → c1 u ≠ c1 w)
    (h2 : ∀ u ∈ S, ∀ w ∈ S, L.Adj u w → c2 u ≠ c2 w) :
    ∀ {a b : V} (p : L.Walk a b), (∀ z ∈ p.support, z ∈ S) →
      xor (c1 a) (c2 a) = xor (c1 b) (c2 b)
  | _, _, .nil, _ => rfl
  | _, _, @SimpleGraph.Walk.cons _ _ a m b h p, hs => by
    have ha : a ∈ S := hs a (by simp)
    have hm : m ∈ S := hs m (by simp)
    rw [← xor_walk_const h1 h2 p (fun z hz => hs z (by simp [hz]))]
    have e1 := h1 a ha m hm h
    have e2 := h2 a ha m hm h
    revert e1 e2
    generalize c1 a = p1
    generalize c1 m = p2
    generalize c2 a = p3
    generalize c2 m = p4
    revert p1 p2 p3 p4
    decide

omit [DecidableEq V] in
/-- **original/residual relation of components and chosen colourings** -/
theorem resid_comp_orig {v : V} {C' : Finset V} (hC' : C' ∈ activeComps (G \ B) lab F v)
    {x : V} (hx : x ∈ C') :
    comp G lab F v x ∈ activeComps G lab F v ∧ C' ⊆ comp G lab F v x ∧
    (∀ z ∈ C', ¬ B.Adj v z ∧ ∃ y, (link (G \ B) lab F v).Adj z y) ∧
    (IsBip G lab F (v, comp G lab F v x) →
      IsBip (G \ B) lab F (v, C') ∧ ∃ s : Bool, ∀ u ∈ C',
        col (G \ B) lab F (v, C') u = xor s (col G lab F (v, comp G lab F v x) u)) := by
  have hact : ∀ z ∈ C', ¬ B.Adj v z ∧ ∃ y, (link (G \ B) lab F v).Adj z y := by
    intro z hz
    obtain ⟨y, hy⟩ := link_nbr hC' hz
    exact ⟨(link_sdiff_adj.1 hy).2.1, y, hy⟩
  obtain ⟨y, hy⟩ := (hact x hx).2
  have hC : comp G lab F v x ∈ activeComps G lab F v :=
    mem_activeComps_of_active (link_sdiff_le v hy)
  have hCeq : comp (G \ B) lab F v x = C' := activeComps_eq hC' hx
  have hreach : ∀ z ∈ C', (link (G \ B) lab F v).Reachable x z := by
    intro z hz
    rw [← hCeq, S07V25.mem_comp_iff] at hz
    exact hz
  have hsub : C' ⊆ comp G lab F v x := by
    intro z hz
    rw [S07V25.mem_comp_iff]
    exact (hreach z hz).mono (link_sdiff_le v)
  refine ⟨hC, hsub, hact, fun hb => ?_⟩
  set c := col G lab F (v, comp G lab F v x) with hc
  have hprop : ∀ u ∈ (C' : Set V), ∀ w ∈ (C' : Set V), (link (G \ B) lab F v).Adj u w →
      c u ≠ c w := fun u hu w hw huw =>
    col_proper hb (hsub hu) (hsub hw) (link_sdiff_le v huw)
  have hb' : IsBip (G \ B) lab F (v, C') := ⟨c, fun u hu w hw huw => hprop u hu w hw huw⟩
  refine ⟨hb', xor (col (G \ B) lab F (v, C') x) (c x), fun u hu => ?_⟩
  obtain ⟨p⟩ := hreach u hu
  have hsupp : ∀ z ∈ p.support, z ∈ (C' : Set V) := by
    intro z hz
    have := support_reach p z hz
    rw [Finset.mem_coe, ← hCeq, S07V25.mem_comp_iff]
    exact this
  have key := xor_walk_const (S := (C' : Set V)) (c1 := col (G \ B) lab F (v, C')) (c2 := c)
    (fun u hu w hw huw => col_proper hb' hu hw huw) hprop p hsupp
  rw [key]
  generalize col (G \ B) lab F (v, C') u = p1
  generalize c u = p2
  revert p1 p2; decide

omit [DecidableEq V] in
/-- **a residual admissible pair is an original admissible pair, with intact spokes** -/
theorem resid_adm_orig {v x y : V} (h : OrigAdm (G \ B) lab F v x y) :
    OrigAdm G lab F v x y ∧ ¬ B.Adj v x ∧ ¬ B.Adj v y := by
  obtain ⟨C', hC', hx, hy, hxy, hcol⟩ := h
  obtain ⟨hC, hsub, hact, hbip⟩ := resid_comp_orig hC' hx
  refine ⟨⟨comp G lab F v x, hC, self_mem_comp (H := G) v x, hsub hy, hxy, fun hb => ?_⟩,
    (hact x hx).1, (hact y hy).1⟩
  obtain ⟨hb', s, hs⟩ := hbip hb
  have hne := hcol hb'
  rw [colG_eq hC' hx, colG_eq hC' hy, hs x hx, hs y hy] at hne
  rw [colG_eq hC (self_mem_comp (H := G) v x), colG_eq hC (hsub hy)]
  intro heq; apply hne; rw [heq]

omit [Fintype V] [DecidableEq V] in
/-- **transfer of a link walk with intact spokes and `B`-free path edges** -/
theorem residual_walk {v : V} : ∀ {x y : V} (p : (link G lab F v).Walk x y),
    (∀ z ∈ p.support, ¬ B.Adj v z) →
    (∀ k < p.length, ¬ B.Adj (p.getVert k) (p.getVert (k + 1))) →
    ∃ p' : (link (G \ B) lab F v).Walk x y, p'.length = p.length ∧ p'.support = p.support ∧
      ∀ i, p'.getVert i = p.getVert i
  | _, _, .nil, _, _ => ⟨.nil, rfl, rfl, fun i => by simp⟩
  | _, _, .cons h p, hsp, hed => by
    obtain ⟨p', h1, h2, h3⟩ := residual_walk p (fun z hz => hsp z (by simp [hz]))
      (fun k hk => by
        have := hed (k + 1) (by simp; omega)
        simpa using this)
    have hadj : (link (G \ B) lab F v).Adj _ _ :=
      link_sdiff_adj.2 ⟨h, hsp _ (by simp), hsp _ (by simp [SimpleGraph.Walk.start_mem_support]),
        by simpa using hed 0 (by simp)⟩
    refine ⟨.cons hadj p', by simp [h1], by simp [h2], fun i => ?_⟩
    cases i with
    | zero => simp
    | succ i => simp [h3]

end S07V49
