/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V49.EdgeLink
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# V49 §2 — surviving link routes with all spokes intact; edge-deleted contract and items

`RobustRoutes G lab F U t εZ εB` is, verbatim, the robust odd-route conclusion that V25/V48
prove for the core (`U = W`, budgets `ε, ε`) and for the surviving core (`U = W ∖ Z`, budgets
`ε/2, ε`): routes in the ORIGINAL link avoiding any later forbidden vertex set and whose path
edges avoid any later sparse graph.

* `route_intact` — for an ORIGINAL admissible pair whose endpoints have intact spokes, the route
  obtained by adding `N_B(v)` (size `≤ Δ(B) ≤ d`) to the forbidden set is a route of the residual
  link `L_v(G \ B)`: path edges avoid `B` (route theorem) and every spoke avoids `B`
  (endpoints by hypothesis, internal vertices because they avoid `N_B(v)`). Budget paid:
  `|Z'| + d ≤ εZ n`, and `d ≤ εB n`.
* `residual_route` — the same for a RESIDUAL admissible pair (residual components, residual
  chosen colouring), using `resid_adm_orig` (no identification is assumed).
* `contract_sdiff`, `coreItems_sdiff` — the actual V45 `CorePathContract (G \ B) lab F U t` and
  `CoreItems (G \ B) lab F U` for the edge-deleted host.
* `resid_survival`, `resid_activeComps` — survival of components: for each original active
  component `C`, the intact part `C.filter (¬ B v ·)` is ONE residual component (when nonempty),
  bipartite in `G \ B` iff `C` is bipartite in `G` (non-bipartite components survive); the
  residual active components are exactly these intact parts.
-/

open Finset

noncomputable section
open Classical

namespace S07V49

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24 S07V25 S07V45 S07V42 S07V48

variable {V I : Type*} [Fintype V] [DecidableEq V] {G B : SimpleGraph V} {lab : V → I}
  {F : Set (Multiset I)}

/-- the robust odd-route conclusion of V25/V48 for a vertex set `U` (verbatim) -/
def RobustRoutes (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (U : Finset V)
    (t : ℕ) (εZ εB : ℝ) : Prop :=
  ∀ (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ),
    (Z.card : ℝ) ≤ εZ * Fintype.card V → (∀ u, B.degree u ≤ d) →
    (d : ℝ) ≤ εB * Fintype.card V →
    ∀ v x y, AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C))
        (colG G lab F) v x y →
      ∃ p ∈ pathsLen (link G lab F v) t x y, intlSet (t - 1) p ⊆ U ∧
        (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z) ∧
        ∀ k < t, ¬ B.Adj (p.getVert k) (p.getVert (k + 1))

/-- **routes with all spokes intact** (original admissible pair, intact endpoint spokes) -/
theorem route_intact {U : Finset V} {t : ℕ} {εZ εB : ℝ} (hR : RobustRoutes G lab F U t εZ εB)
    [DecidableRel B.Adj] {d : ℕ} (hB : ∀ u, B.degree u ≤ d)
    (hd : (d : ℝ) ≤ εB * Fintype.card V) (Z' : Finset V)
    (hZ' : (Z'.card : ℝ) + d ≤ εZ * Fintype.card V) {v x y : V}
    (hxy : OrigAdm G lab F v x y) (hx : ¬ B.Adj v x) (hy : ¬ B.Adj v y) :
    ∃ p ∈ pathsLen (link (G \ B) lab F v) t x y, intlSet (t - 1) p ⊆ U ∧
      (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z') := by
  set N := B.neighborFinset v with hNdef
  have hN : ((Z' ∪ N).card : ℝ) ≤ εZ * Fintype.card V := by
    have h1 : (Z' ∪ N).card ≤ Z'.card + N.card := card_union_le _ _
    have h2 : N.card ≤ d := by rw [hNdef, SimpleGraph.card_neighborFinset_eq_degree]; exact hB v
    have : ((Z' ∪ N).card : ℝ) ≤ Z'.card + d := by exact_mod_cast (h1.trans (by omega))
    linarith
  obtain ⟨p, hp, hpU, hpZ, hpB⟩ := hR (Z' ∪ N) B d hN hB hd v x y hxy
  have hlen : p.length = t := by
    simp only [pathsLen, mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hp; exact hp.1
  have hpath : p.IsPath := (mem_filter.1 hp).2
  have hsp : ∀ z ∈ p.support, ¬ B.Adj v z := by
    intro z hz
    rcases support_of_pathsLen hp hz with rfl | rfl | h'
    · exact hx
    · exact hy
    · rw [mem_intlSet] at h'
      obtain ⟨i, rfl⟩ := h'
      intro hB'
      exact hpZ i (mem_union_right _ (by rw [hNdef, SimpleGraph.mem_neighborFinset]; exact hB'))
  obtain ⟨p', h1, h2, h3⟩ := residual_walk p hsp (fun k hk => hpB k (hlen ▸ hk))
  have hint : intlSet (t - 1) p' = intlSet (t - 1) p := by
    unfold intlSet intl; simp [h3]
  refine ⟨p', ?_, hint ▸ hpU, fun i => ?_⟩
  · simp only [pathsLen, mem_filter, SimpleGraph.mem_finsetWalkLength_iff]
    refine ⟨h1.trans hlen, ?_⟩
    rw [SimpleGraph.Walk.isPath_def, h2]; exact hpath.support_nodup
  · have : intl (t - 1) p' i = intl (t - 1) p i := h3 _
    rw [this]; exact fun h => hpZ i (mem_union_left _ h)

/-- **residual routes**: a RESIDUAL admissible pair has a route of the residual link -/
theorem residual_route {U : Finset V} {t : ℕ} {εZ εB : ℝ} (hR : RobustRoutes G lab F U t εZ εB)
    [DecidableRel B.Adj] {d : ℕ} (hB : ∀ u, B.degree u ≤ d)
    (hd : (d : ℝ) ≤ εB * Fintype.card V) (Z' : Finset V)
    (hZ' : (Z'.card : ℝ) + d ≤ εZ * Fintype.card V) {v x y : V}
    (hxy : OrigAdm (G \ B) lab F v x y) :
    ∃ p ∈ pathsLen (link (G \ B) lab F v) t x y, intlSet (t - 1) p ⊆ U ∧
      (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z') := by
  obtain ⟨h0, hx, hy⟩ := resid_adm_orig hxy
  exact route_intact hR hB hd Z' hZ' h0 hx hy

/-- **the actual V45 contract for the edge-deleted host** -/
theorem contract_sdiff {U : Finset V} {t : ℕ} {εZ εB : ℝ} (ht1 : 1 ≤ t)
    (hR : RobustRoutes G lab F U t εZ εB) [DecidableRel B.Adj] {d : ℕ}
    (hB : ∀ u, B.degree u ≤ d) (hd : (d : ℝ) ≤ εB * Fintype.card V)
    (hdZ : (d : ℝ) ≤ εZ * Fintype.card V) :
    CorePathContract (G \ B) lab F U t := by
  apply contract_of_route ht1
  intro v x y hxy
  obtain ⟨p, hp, hU, -⟩ := residual_route hR hB hd ∅ (by simpa using hdZ) (by convert hxy)
  exact ⟨p, by convert hp, by convert hU⟩

/-- **the actual V45 items 1–3 for the edge-deleted host** -/
theorem coreItems_sdiff {U : Finset V} {t : ℕ} {εZ εB : ℝ} (ht : Odd t) (ht3 : 3 ≤ t)
    (hR : RobustRoutes G lab F U t εZ εB) [DecidableRel B.Adj] {d : ℕ}
    (hB : ∀ u, B.degree u ≤ d) (hd : (d : ℝ) ≤ εB * Fintype.card V)
    (hdZ : (d : ℝ) ≤ εZ * Fintype.card V) :
    CoreItems (G \ B) lab F U :=
  coreItems_of_contract (contract_sdiff (by omega) hR hB hd hdZ) ht ht3

/-- **residual neighbours inside the original component** from the core neighbour count -/
theorem resid_nbr {v : V} {C U : Finset V} {K : ℝ}
    (hcnt : ∀ x ∈ C, K ≤ ((univ.filter fun y => (link G lab F v).Adj x y ∧ y ∈ C ∩ U).card : ℝ))
    [DecidableRel B.Adj] {d : ℕ} (hB : ∀ u, B.degree u ≤ d) (hK : 2 * (d : ℝ) + 2 ≤ K) :
    ∀ x ∈ C, ¬ B.Adj v x → ∀ w, ∃ y, (link (G \ B) lab F v).Adj x y ∧ y ∈ C ∩ U ∧ y ≠ w := by
  intro x hx hBx w
  set S := univ.filter fun y => (link G lab F v).Adj x y ∧ y ∈ C ∩ U
  set S' := S \ (B.neighborFinset v ∪ B.neighborFinset x)
  have h1 : S.card ≤ S'.card + (B.neighborFinset v ∪ B.neighborFinset x).card := by
    have := card_le_card_sdiff_add_card (s := S) (t := B.neighborFinset v ∪ B.neighborFinset x)
    omega
  have h2 : (B.neighborFinset v ∪ B.neighborFinset x).card ≤ 2 * d := by
    have := card_union_le (B.neighborFinset v) (B.neighborFinset x)
    rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree]
      at this
    have := hB v; have := hB x; omega
  have h3 : 1 < S'.card := by
    have hS := hcnt x hx
    have : (S.card : ℝ) ≤ S'.card + 2 * d := by exact_mod_cast (h1.trans (by omega))
    have : (1 : ℝ) < S'.card := by linarith
    exact_mod_cast this
  obtain ⟨y, hy, hyw⟩ := exists_mem_ne h3 w
  simp only [S', S, mem_sdiff, mem_filter, mem_univ, true_and, mem_union,
    SimpleGraph.mem_neighborFinset, not_or] at hy
  exact ⟨y, link_sdiff_adj.2 ⟨hy.1.1, hBx, hy.2.1, hy.2.2⟩, hy.1.2, hyw⟩

omit [DecidableEq V] in
/-- **survival of components after sparse edge deletion** -/
theorem resid_survival [DecidableRel B.Adj] {t : ℕ} (ht : Odd t) {v : V} {C : Finset V}
    (hC : C ∈ activeComps G lab F v)
    (hR : ∀ x y, OrigAdm G lab F v x y → ¬ B.Adj v x → ¬ B.Adj v y →
      ∃ p : (link (G \ B) lab F v).Walk x y, p.length = t)
    (hN : ∀ x ∈ C, ¬ B.Adj v x → ∀ w, ∃ y, (link (G \ B) lab F v).Adj x y ∧ y ≠ w)
    {x : V} (hx : x ∈ C) (hBx : ¬ B.Adj v x) :
    comp (G \ B) lab F v x ∈ activeComps (G \ B) lab F v ∧
    comp (G \ B) lab F v x = C.filter (fun z => ¬ B.Adj v z) ∧
    (IsBip (G \ B) lab F (v, comp (G \ B) lab F v x) ↔ IsBip G lab F (v, C)) := by
  have hCx : comp G lab F v x = C := activeComps_eq hC hx
  have hinC : ∀ {a b : V}, a ∈ C → (link (G \ B) lab F v).Reachable a b → b ∈ C :=
    fun ha hab => mem_of_adj hC ha (hab.mono (link_sdiff_le v))
  obtain ⟨y0, hy0, -⟩ := hN x hx hBx x
  have hact : comp (G \ B) lab F v x ∈ activeComps (G \ B) lab F v :=
    mem_activeComps_of_active hy0
  have hreach : ∀ z ∈ C, ¬ B.Adj v z → (link (G \ B) lab F v).Reachable x z := by
    intro z hz hBz
    by_cases hxz : x = z
    · subst hxz; rfl
    by_cases hcol : IsBip G lab F (v, C) → colG G lab F v x ≠ colG G lab F v z
    · obtain ⟨p, -⟩ := hR x z ⟨C, hC, hx, hz, hxz, hcol⟩ hBx hBz
      exact ⟨p⟩
    · push_neg at hcol
      obtain ⟨hb, hceq⟩ := hcol
      obtain ⟨y, hxy, hyz⟩ := hN x hx hBx z
      have hy : y ∈ C := hinC hx hxy.reachable
      have hBy : ¬ B.Adj v y := (link_sdiff_adj.1 hxy).2.2.1
      have hcxy : colG G lab F v x ≠ colG G lab F v y := by
        rw [colG_eq hC hx, colG_eq hC hy]; exact col_proper hb hx hy (link_sdiff_le v hxy)
      obtain ⟨p, -⟩ := hR y z ⟨C, hC, hy, hz, hyz, fun _ => by rw [← hceq]; exact hcxy.symm⟩
        hBy hBz
      exact hxy.reachable.trans ⟨p⟩
  have hcompeq : comp (G \ B) lab F v x = C.filter (fun z => ¬ B.Adj v z) := by
    ext z
    rw [S07V25.mem_comp_iff, mem_filter]
    constructor
    · intro h
      refine ⟨hinC hx h, ?_⟩
      have hz : z ∈ comp (G \ B) lab F v x := by rw [S07V25.mem_comp_iff]; exact h
      exact ((resid_comp_orig hact (self_mem_comp (H := G \ B) v x)).2.2.1 z hz).1
    · rintro ⟨hz, hBz⟩; exact hreach z hz hBz
  refine ⟨hact, hcompeq, ⟨fun hb' => ?_, fun hb => ?_⟩⟩
  · by_contra hnb
    obtain ⟨c, hc⟩ := hb'
    obtain ⟨y, hxy, -⟩ := hN x hx hBx x
    have hy : y ∈ C := hinC hx hxy.reachable
    have hBy := (link_sdiff_adj.1 hxy).2.2.1
    obtain ⟨z, hyz, hzx⟩ := hN y hy hBy x
    have hz : z ∈ C := hinC hy hyz.reachable
    have hBz := (link_sdiff_adj.1 hyz).2.2.1
    obtain ⟨p, hp⟩ := hR x z ⟨C, hC, hx, hz, Ne.symm hzx, fun h => absurd h hnb⟩ hBx hBz
    have hD : ∀ u ∈ ((comp (G \ B) lab F v x : Finset V) : Set V),
        ∀ w ∈ ((comp (G \ B) lab F v x : Finset V) : Set V),
        (link (G \ B) lab F v).Adj u w → c u ≠ c w := fun u hu w hw h => hc u hu w hw h
    have hpD : ∀ w ∈ p.support, w ∈ ((comp (G \ B) lab F v x : Finset V) : Set V) :=
      fun w hw => by rw [Finset.mem_coe, S07V25.mem_comp_iff]; exact support_reach p w hw
    have e1 := col_parity hD p hpD
    have hq : ∀ w ∈ (SimpleGraph.Walk.cons hxy (.cons hyz .nil) :
        (link (G \ B) lab F v).Walk x z).support,
        w ∈ ((comp (G \ B) lab F v x : Finset V) : Set V) := fun w hw => by
      rw [Finset.mem_coe, S07V25.mem_comp_iff]
      exact support_reach _ w hw
    have e2 := col_parity hD (SimpleGraph.Walk.cons hxy (.cons hyz .nil) :
      (link (G \ B) lab F v).Walk x z) hq
    rw [hp] at e1
    exact (Nat.not_even_iff_odd.2 ht) (e1.1 (e2.2 ⟨1, rfl⟩))
  · have := (resid_comp_orig hact (self_mem_comp (H := G \ B) v x)).2.2.2
    rw [hCx] at this
    exact (this hb).1

/-- **the residual active components are exactly the intact parts of the original ones** -/
theorem resid_activeComps [DecidableRel B.Adj] {t : ℕ} (ht : Odd t) {v : V}
    (hR : ∀ x y, OrigAdm G lab F v x y → ¬ B.Adj v x → ¬ B.Adj v y →
      ∃ p : (link (G \ B) lab F v).Walk x y, p.length = t)
    (hN : ∀ C ∈ activeComps G lab F v, ∀ x ∈ C, ¬ B.Adj v x → ∀ w,
      ∃ y, (link (G \ B) lab F v).Adj x y ∧ y ≠ w) :
    activeComps (G \ B) lab F v =
      ((activeComps G lab F v).filter (fun C => ∃ z ∈ C, ¬ B.Adj v z)).image
        (fun C => C.filter (fun z => ¬ B.Adj v z)) := by
  ext C'
  rw [mem_image]
  constructor
  · intro hC'
    obtain ⟨x0, -, rfl⟩ := S07V25.mem_activeComps.1 hC'
    have hx0 := self_mem_comp (H := G \ B) (lab := lab) (F := F) v x0
    obtain ⟨hC, -, hact, -⟩ := resid_comp_orig hC' hx0
    have hBx := (hact x0 hx0).1
    have hsurv := resid_survival ht hC hR (hN _ hC) (self_mem_comp (H := G) v x0) hBx
    exact ⟨comp G lab F v x0, mem_filter.2 ⟨hC, x0, self_mem_comp (H := G) v x0, hBx⟩,
      hsurv.2.1.symm⟩
  · rintro ⟨C, hCf, rfl⟩
    obtain ⟨hC, z, hz, hBz⟩ := mem_filter.1 hCf
    have hsurv := resid_survival ht hC hR (hN _ hC) hz hBz
    rw [← hsurv.2.1]; exact hsurv.1

end S07V49
