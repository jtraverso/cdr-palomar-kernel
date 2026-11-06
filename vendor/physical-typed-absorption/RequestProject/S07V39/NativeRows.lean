/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V37.NativeDeletion
public import RequestProject.S07V38.MatchingPotential
@[expose] public section

/-!
# V39 §1 — native rows under small vertex deletion (from the ORIGINAL H3/H4)

For a host `(G, lab, F)` and a finite vertex set `Z`, `delG G Z` is the ACTUAL induced
surviving-edge host on the SAME vertex type `V`: an edge survives iff both ends avoid `Z`; the
deleted vertices stay in `V` as isolated vertices. Labels and the family `F` are unchanged.

Only the original H3 (`CommonNbrCond G lab F α`) and H4 (`HingeCond G lab F α h`) are used, with
`n ≥ n1Of α` and `|Z| ≤ delOf α h · n` (both constants fixed from `(α, h)` before the host):

* `allowed_delG_iff` — allowed triangles of `G − Z` are the allowed triangles of `G` avoiding `Z`;
* `link_delG_adj` — the link of `G − Z` at `v` is empty if `v ∈ Z`, and is `linkA G v Z`
  (the link of `G` with `Z` deleted) if `v ∉ Z`;
* `no_active_of_no_allowed` — a host with no allowed triangle has no active rows, before or
  after deletion (unconditional);
* `not_active_of_mem` — every row rooted in `Z` is inactive in `G − Z` (deleted vertices are
  isolated; this is unconditional);
* `linkActive_delG_iff` — `u` is active in the link of `G − Z` at `v` iff `v, u ∉ Z` and `u` is
  active in the link of `G` at `v`;
* `row_survives` — for every surviving root `v` and every active row `(v, K)` of `G`, the row
  `(v, K \ Z)` is active in `G − Z`, and it is the `G − Z` component of each of its members;
* `row_reflects`, `row_unique` — every active row of `G − Z` is `(v, K \ Z)` for a unique active
  row `(v, K)` of `G` (so `K ↦ K \ Z` is a bijection of active rows at each surviving root);
* `bip_iff` — bipartiteness is preserved and reflected;
* `col_flip`, `sgn_col_delG` — the chosen colourings agree up to ONE sign per component:
  `col_{G−Z}(v, K \ Z) u = flip ⊕ col_G(v, K) u` for every `u ∈ K \ Z`.

No row correspondence, sign matcher, minimum link density, class bound or new pseudorandomness
assumption is used: everything is derived from H3/H4 through V25 `link_evenRobust`,
`link_degree_ge` and V37 `comp_robust` (robust connectivity of components and of their double
covers, i.e. the odd-walk argument).
-/

open Finset Classical

noncomputable section

namespace S07V39

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.ActiveCover
open S07V24 S07V25 S07V37

variable {V I : Type*} {lab : V → I} {F : Set (Multiset I)}

/-- **The surviving-edge host `G − Z`** on the same vertex type: an edge survives iff both
ends avoid `Z`; deleted vertices become isolated. -/
def delG (G : SimpleGraph V) (Z : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ Z ∧ y ∉ Z
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

lemma delG_le (G : SimpleGraph V) (Z : Finset V) : delG G Z ≤ G := fun _ _ h => h.1

lemma delG_mono {G H : SimpleGraph V} (hle : H ≤ G) (Z : Finset V) : delG H Z ≤ delG G Z :=
  fun _ _ h => ⟨hle h.1, h.2⟩

/-- Allowed triangles are monotone in the graph (same labels and family). -/
lemma allowed_mono {G H : SimpleGraph V} (hle : H ≤ G) {T : Finset V}
    (hT : IsAllowed H lab F T) : IsAllowed G lab F T :=
  ⟨hT.1, fun x hx y hy hxy => hle (hT.2.1 x hx y hy hxy), hT.2.2⟩

/-- Links are monotone in the graph. -/
lemma link_mono {G H : SimpleGraph V} (hle : H ≤ G) (v : V) : link H lab F v ≤ link G lab F v :=
  fun _ _ h => ⟨h.1, allowed_mono hle h.2⟩

/-- **Allowed triangles of `G − Z`** are exactly the allowed triangles of `G` avoiding `Z`. -/
theorem allowed_delG_iff {G : SimpleGraph V} {Z T : Finset V} :
    IsAllowed (delG G Z) lab F T ↔ IsAllowed G lab F T ∧ ∀ x ∈ T, x ∉ Z := by
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
  · rintro ⟨⟨h1, h2, h3⟩, hZ⟩
    exact ⟨h1, fun x hx y hy hxy => ⟨h2 x hx y hy hxy, hZ x hx, hZ y hy⟩, h3⟩

/-- **The link of `G − Z`**: empty at roots in `Z`, and `linkA G v Z` at surviving roots. -/
theorem link_delG_adj {G : SimpleGraph V} {Z : Finset V} {v u w : V} :
    (link (delG G Z) lab F v).Adj u w ↔ v ∉ Z ∧ (linkA G lab F v Z).Adj u w := by
  show (u ≠ w ∧ IsAllowed (delG G Z) lab F {v, u, w}) ↔
    v ∉ Z ∧ ((u ≠ w ∧ IsAllowed G lab F {v, u, w}) ∧ u ∉ Z ∧ w ∉ Z)
  rw [allowed_delG_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  tauto

/-- **Rows rooted in `Z` are inactive in `G − Z`** (unconditional). -/
theorem not_active_of_mem {G : SimpleGraph V} {Z : Finset V} {v : V} (hv : v ∈ Z)
    (K : Finset V) [Fintype V] : ¬ IsActiveRow (delG G Z) lab F (v, K) := by
  rintro ⟨u, ⟨w, huw⟩, -⟩
  exact (link_delG_adj.1 huw).1 hv

/-- **Empty hosts** (no allowed triangle): there are no active rows, neither in `G` nor in
`G − Z` (unconditional). -/
theorem no_active_of_no_allowed {G : SimpleGraph V} {Z : Finset V}
    (h0 : ∀ T, ¬ IsAllowed G lab F T) (j : Row V) [Fintype V] :
    ¬ IsActiveRow G lab F j ∧ ¬ IsActiveRow (delG G Z) lab F j := by
  refine ⟨?_, ?_⟩
  · rintro ⟨u, ⟨w, huw⟩, -⟩
    exact h0 _ huw.2
  · rintro ⟨u, ⟨w, huw⟩, -⟩
    exact h0 _ (allowed_delG_iff.1 huw.2).1

/-- `G − Z` link reachability implies `G` link reachability. -/
lemma reach_delG_mono {G : SimpleGraph V} {Z : Finset V} {v u w : V}
    (h : (link (delG G Z) lab F v).Reachable u w) : (link G lab F v).Reachable u w :=
  h.mono (link_mono (delG_le G Z) v)

/-- `G − Z` link reachability from a survivor only reaches survivors. -/
lemma reach_delG_not_mem {G : SimpleGraph V} {Z : Finset V} {v u w : V}
    (h : (link (delG G Z) lab F v).Reachable u w) (hu : u ∉ Z) : w ∉ Z := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons ha _ ih => exact ih (link_delG_adj.1 ha).2.2.2

/-- `linkA` reachability at a surviving root is `G − Z` link reachability. -/
lemma reach_delG_of_linkA {G : SimpleGraph V} {Z : Finset V} {v u w : V} (hv : v ∉ Z)
    (h : (linkA G lab F v Z).Reachable u w) : (link (delG G Z) lab F v).Reachable u w :=
  h.mono (fun _ _ hadj => link_delG_adj.2 ⟨hv, hadj⟩)

variable [Fintype V]

/-! ### The deletion window -/

/-- The deletion rate is at most `α / 32`. -/
lemma delOf_le {α : ℝ} (hα : 0 < α) (h : ℕ) : delOf α h ≤ α / 32 := by
  have hM : (1 : ℝ) ≤ 2 ^ (h.choose 2) := one_le_pow₀ (by norm_num)
  have h1 : rhoOf α h ≤ α / (8 * 2 ^ (h.choose 2)) := min_le_right _ _
  have h2 : α / (8 * 2 ^ (h.choose 2)) ≤ α / 8 :=
    div_le_div_of_nonneg_left hα.le (by norm_num) (by linarith)
  unfold delOf
  linarith

/-- A small deletion set has `2 |Z| ≤ α n`. -/
lemma two_card_le {α : ℝ} (hα : 0 < α) (h : ℕ) {Z : Finset V}
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) : 2 * (Z.card : ℝ) ≤ α * Fintype.card V := by
  have := delOf_le hα h
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  nlinarith

variable {G : SimpleGraph V} {Z : Finset V}

/-- **Survivors of an active component are nonempty** (H3). -/
theorem surv_nonempty {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {v : V} {K : Finset V}
    (hK : IsActiveRow G lab F (v, K)) (hn : 0 < Fintype.card V) : ∃ u ∈ K, u ∉ Z := by
  by_contra hc
  push_neg at hc
  have h1 := hlow_of_H3 hH3 (v, K) hK
  have h2 : (K.card : ℝ) ≤ Z.card := by exact_mod_cast card_le_card hc
  have h3 := two_card_le hα h hZ
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  simp only at h1
  nlinarith

/-- **Fresh link neighbours** (H3): every active vertex of a link has a link neighbour
outside `Z`. -/
theorem fresh_nbr {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {v b : V}
    (hb : LinkActive G lab F v b) : ∃ w, w ∉ Z ∧ (link G lab F v).Adj b w := by
  by_contra hc
  push_neg at hc
  have h1 := link_degree_ge hH3 v b hb
  have h2 : (link G lab F v).neighborFinset b ⊆ Z := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    by_contra hwZ; exact hc w hwZ hw
  have h3 := card_le_card h2
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h3
  have h4 : ((link G lab F v).degree b : ℝ) ≤ Z.card := by exact_mod_cast h3
  have h5 := two_card_le hα h hZ
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos_iff.2 ⟨v⟩
  nlinarith

/-- **Robust connectivity of survivors** (H3/H4, V37 `comp_robust`), for EVERY root. -/
theorem surv_reach {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {v : V} {K : Finset V}
    (hK : IsActiveRow G lab F (v, K)) {u w : V} (hu : u ∈ K) (hw : w ∈ K) (huZ : u ∉ Z)
    (hwZ : w ∉ Z) : (linkA G lab F v Z).Reachable u w := by
  obtain ⟨h2A, -, -, -⟩ := del_window hα h hn hZ
  set s := ⌊rhoOf α h * Fintype.card V⌋₊
  have hAs : Z.card ≤ s := by omega
  obtain ⟨x0, hx0, hK⟩ := hK
  simp only at hx0 hK
  subst hK
  obtain ⟨hconn, -⟩ := comp_robust hα hH3 hH4 hn v x0 hx0
  set C := comp G lab F v x0
  let S : Finset ↥(C : Set V) := univ.filter fun z => z.1 ∈ Z
  have hS : S.card ≤ s := by
    refine le_trans ?_ hAs
    refine card_le_card_of_injOn (fun z => z.1) (fun z hz => by simpa [S] using hz) ?_
    intro z _ z' _ e; exact Subtype.ext e
  obtain ⟨p, hp, -⟩ := hconn S hS ∅ (fun x => by simp [degB]) ⟨u, hu⟩ ⟨w, hw⟩
    (by simpa [S] using huZ) (by simpa [S] using hwZ)
  exact reach_linkA_of_walk p fun z hz => by simpa [S] using hp z hz

/-- **Non-bipartite components stay non-bipartite** (H3/H4: robust connectivity of the
double cover, V37 `comp_robust`), for EVERY root. -/
theorem surv_nonbip {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {v : V} {K : Finset V}
    (hK : IsActiveRow G lab F (v, K)) (hnb : ¬ IsBip G lab F (v, K)) :
    ¬ ∃ col : V → Bool, ∀ u ∈ K, ∀ w ∈ K, (linkA G lab F v Z).Adj u w → col u ≠ col w := by
  rintro ⟨col, hcol⟩
  obtain ⟨h2A, -, -, -⟩ := del_window hα h hn hZ
  set s := ⌊rhoOf α h * Fintype.card V⌋₊
  have hAs : Z.card ≤ s := by omega
  have hnpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
  obtain ⟨u, hu, huZ⟩ := surv_nonempty hα hH3 hZ hK hnpos
  obtain ⟨x0, hx0, hK⟩ := hK
  simp only at hx0 hK
  subst hK
  obtain ⟨-, hcov⟩ := comp_robust hα hH3 hH4 hn v x0 hx0
  have hconn := hcov hnb
  set C := comp G lab F v x0
  let S : Finset (↥(C : Set V) × Bool) := univ.filter fun z => z.1.1 ∈ Z
  have hS : S.card ≤ s := by
    have : S ⊆ (univ.filter fun z : ↥(C : Set V) => z.1 ∈ Z) ×ˢ univ := by
      intro z hz; simp only [S, mem_filter, mem_univ, true_and] at hz; simp [hz]
    refine (card_le_card this).trans ?_
    rw [card_product, card_univ, Fintype.card_bool]
    have : (univ.filter fun z : ↥(C : Set V) => z.1 ∈ Z).card ≤ Z.card :=
      card_le_card_of_injOn (fun z => z.1) (fun z hz => by simpa using hz)
        (fun z _ z' _ e => Subtype.ext e)
    omega
  obtain ⟨p, hp, -⟩ := hconn S hS ∅ (fun x => by simp [degB]) (⟨u, hu⟩, true) (⟨u, hu⟩, false)
    (by simpa [S] using huZ) (by simpa [S] using huZ)
  have := cover_walk_const col hcol p fun z hz => by simpa [S] using hp z hz
  revert this
  cases col u <;> simp

/-! ### Item 1: the native rows of `G − Z` -/

/-- **Active vertices of the deleted links.** -/
theorem linkActive_delG_iff {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {v u : V} :
    LinkActive (delG G Z) lab F v u ↔ v ∉ Z ∧ u ∉ Z ∧ LinkActive G lab F v u := by
  constructor
  · rintro ⟨w, huw⟩
    obtain ⟨hv, hA, hu, -⟩ := link_delG_adj.1 huw
    exact ⟨hv, hu, w, hA⟩
  · rintro ⟨hv, hu, hact⟩
    obtain ⟨w, hwZ, huw⟩ := fresh_nbr hα hH3 hZ hact
    exact ⟨w, link_delG_adj.2 ⟨hv, huw, hu, hwZ⟩⟩

/-- **Active rows survive as `K \ Z`.** For a surviving root `v` and an active row `(v, K)` of
`G`, the row `(v, K \ Z)` is active in `G − Z` and is the `G − Z` component of each member. -/
theorem row_survives {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {v : V} (hv : v ∉ Z) {K : Finset V}
    (hK : IsActiveRow G lab F (v, K)) :
    IsActiveRow (delG G Z) lab F (v, K \ Z) ∧
      ∀ u ∈ K \ Z, comp (delG G Z) lab F v u = K \ Z := by
  have hcomp : ∀ u ∈ K \ Z, comp (delG G Z) lab F v u = K \ Z := by
    intro u hu
    rw [Finset.mem_sdiff] at hu
    have hKu : K = comp G lab F v u := S07V36.active_eq_comp hK hu.1
    ext w
    rw [S07V25.mem_comp_iff, Finset.mem_sdiff]
    constructor
    · intro hr
      refine ⟨?_, reach_delG_not_mem hr hu.2⟩
      rw [hKu, S07V25.mem_comp_iff]
      exact reach_delG_mono hr
    · rintro ⟨hwK, hwZ⟩
      exact reach_delG_of_linkA hv (surv_reach hα hH3 hH4 hn hZ hK hu.1 hwK hu.2 hwZ)
  refine ⟨?_, hcomp⟩
  have hnpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
  obtain ⟨u, hu, huZ⟩ := surv_nonempty hα hH3 hZ hK hnpos
  have hact : LinkActive G lab F v u := S07V36.linkActive_of_mem hK hu
  exact ⟨u, (linkActive_delG_iff hα hH3 hZ).2 ⟨hv, huZ, hact⟩,
    hcomp u (Finset.mem_sdiff.2 ⟨hu, huZ⟩)⟩

/-- **Every active row of `G − Z` comes from an active row of `G`.** -/
theorem row_reflects {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {v : V} {K' : Finset V}
    (hK' : IsActiveRow (delG G Z) lab F (v, K')) :
    v ∉ Z ∧ ∃ K, IsActiveRow G lab F (v, K) ∧ K' = K \ Z := by
  obtain ⟨u, hu, hK'⟩ := hK'
  simp only at hu hK'
  obtain ⟨hv, huZ, hact⟩ := (linkActive_delG_iff hα hH3 hZ).1 hu
  have hK : IsActiveRow G lab F (v, comp G lab F v u) := ⟨u, hact, rfl⟩
  refine ⟨hv, comp G lab F v u, hK, ?_⟩
  rw [← hK']
  exact (row_survives hα hH3 hH4 hn hZ hv hK).2 u
    (Finset.mem_sdiff.2 ⟨S07V38.mem_comp_self' v u, huZ⟩)

/-- **Uniqueness**: `K ↦ K \ Z` is injective on the active rows at a root. -/
theorem row_unique {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {v : V} {K₁ K₂ : Finset V}
    (h₁ : IsActiveRow G lab F (v, K₁)) (h₂ : IsActiveRow G lab F (v, K₂))
    (heq : K₁ \ Z = K₂ \ Z) : K₁ = K₂ := by
  have hnpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
  obtain ⟨u, hu, huZ⟩ := surv_nonempty hα hH3 hZ h₁ hnpos
  have hu2 : u ∈ K₂ := (Finset.mem_sdiff.1 (heq ▸ Finset.mem_sdiff.2 ⟨hu, huZ⟩)).1
  have e1 : K₁ = comp G lab F v u := S07V36.active_eq_comp h₁ hu
  have e2 : K₂ = comp G lab F v u := S07V36.active_eq_comp h₂ hu2
  rw [e1, e2]

/-- **Bipartiteness is preserved and reflected.** -/
theorem bip_iff {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {v : V} (hv : v ∉ Z) {K : Finset V}
    (hK : IsActiveRow G lab F (v, K)) :
    IsBip (delG G Z) lab F (v, K \ Z) ↔ IsBip G lab F (v, K) := by
  constructor
  · intro hb
    by_contra hnb
    apply surv_nonbip hα hH3 hH4 hn hZ hK hnb
    obtain ⟨col, hcol⟩ := hb
    refine ⟨col, fun u hu w hw huw => hcol u (Finset.mem_sdiff.2 ⟨hu, huw.2.1⟩) w
      (Finset.mem_sdiff.2 ⟨hw, huw.2.2⟩) (link_delG_adj.2 ⟨hv, huw⟩)⟩
  · rintro ⟨col, hcol⟩
    refine ⟨col, fun u hu w hw huw => hcol u (Finset.mem_sdiff.1 hu).1 w (Finset.mem_sdiff.1 hw).1
      ((link_mono (delG_le G Z) v) huw)⟩

/-! ### Signs -/

omit [Fintype V] in
/-- Along a walk inside a neighbour-closed set on which two colourings are proper, their
`xor` is constant. -/
lemma xor_const {L : SimpleGraph V} {S : Finset V} (c d : V → Bool)
    (hcl : ∀ x y, x ∈ S → L.Adj x y → y ∈ S)
    (hc : ∀ x ∈ S, ∀ y ∈ S, L.Adj x y → c x ≠ c y)
    (hd : ∀ x ∈ S, ∀ y ∈ S, L.Adj x y → d x ≠ d y) {x y : V} (p : L.Walk x y) (hx : x ∈ S) :
    xor (c x) (d x) = xor (c y) (d y) := by
  induction p with
  | nil => rfl
  | @cons a b _ ha _ ih =>
    have hb := hcl a b hx ha
    rw [← ih hb]
    have h1 := hc a hx b hb ha
    have h2 := hd a hx b hb ha
    revert h1 h2
    cases c a <;> cases c b <;> cases d a <;> cases d b <;> simp

/-- The per-component flip between the chosen colourings of `(v, K \ Z)` in `G − Z` and of
`(v, K)` in `G` (read off at one survivor; `false` if there is none). -/
def flip (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (Z : Finset V) (v : V)
    (K : Finset V) : Bool :=
  if hK : (K \ Z).Nonempty then
    xor (TypedTriangle.ComponentRows.col (delG G Z) lab F (v, K \ Z) hK.choose)
      (TypedTriangle.ComponentRows.col G lab F (v, K) hK.choose)
  else false

/-- **One sign per component.** For a native row `(v, K)` of `G` (active, bipartite) and a
surviving root `v`, `col_{G−Z}(v, K \ Z) u = flip ⊕ col_G(v, K) u` for every `u ∈ K \ Z`. -/
theorem col_flip {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {v : V} (hv : v ∉ Z) {K : Finset V}
    (hK : S07V36.IsNRow G lab F (v, K)) (u : V) (hu : u ∈ K \ Z) :
    TypedTriangle.ComponentRows.col (delG G Z) lab F (v, K \ Z) u =
      xor (flip G lab F Z v K) (TypedTriangle.ComponentRows.col G lab F (v, K) u) := by
  obtain ⟨hJact, hJcomp⟩ := row_survives hα hH3 hH4 hn hZ hv hK.1
  have hJbip : IsBip (delG G Z) lab F (v, K \ Z) := (bip_iff hα hH3 hH4 hn hZ hv hK.1).2 hK.2
  have hne : (K \ Z).Nonempty := ⟨u, hu⟩
  set u0 := hne.choose with hu0
  have hu0K : u0 ∈ K \ Z := hne.choose_spec
  -- `xor` is constant along `G − Z` link walks inside `K \ Z`
  have hcl : ∀ x y, x ∈ K \ Z → (link (delG G Z) lab F v).Adj x y → y ∈ K \ Z := by
    intro x y hx hxy
    rw [← hJcomp x hx, S07V25.mem_comp_iff]
    exact hxy.reachable
  have hcJ : ∀ x ∈ K \ Z, ∀ y ∈ K \ Z, (link (delG G Z) lab F v).Adj x y →
      TypedTriangle.ComponentRows.col (delG G Z) lab F (v, K \ Z) x ≠
        TypedTriangle.ComponentRows.col (delG G Z) lab F (v, K \ Z) y :=
    fun x hx y hy hxy => S07V36.col_proper hJbip hx hy hxy
  have hcG : ∀ x ∈ K \ Z, ∀ y ∈ K \ Z, (link (delG G Z) lab F v).Adj x y →
      TypedTriangle.ComponentRows.col G lab F (v, K) x ≠
        TypedTriangle.ComponentRows.col G lab F (v, K) y :=
    fun x hx y hy hxy => S07V36.col_proper hK.2 (Finset.mem_sdiff.1 hx).1
      (Finset.mem_sdiff.1 hy).1 ((link_mono (delG_le G Z) v) hxy)
  have hreach : (link (delG G Z) lab F v).Reachable u0 u := by
    rw [← S07V25.mem_comp_iff, hJcomp u0 hu0K]; exact hu
  obtain ⟨p⟩ := hreach
  have key := xor_const _ _ hcl hcJ hcG p hu0K
  have hflip : flip G lab F Z v K =
      xor (TypedTriangle.ComponentRows.col (delG G Z) lab F (v, K \ Z) u0)
        (TypedTriangle.ComponentRows.col G lab F (v, K) u0) := by
    unfold flip; rw [dif_pos hne]
  rw [hflip, key]
  cases TypedTriangle.ComponentRows.col (delG G Z) lab F (v, K \ Z) u <;>
    cases TypedTriangle.ComponentRows.col G lab F (v, K) u <;> rfl

/-- The integer sign `±1` of the flip. -/
def rowSign (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (Z : Finset V) (v : V)
    (K : Finset V) : ℤ :=
  if flip G lab F Z v K then -1 else 1

omit [Fintype V] in
lemma rowSign_mul_self (G : SimpleGraph V) (Z : Finset V) (v : V) (K : Finset V) :
    rowSign G lab F Z v K * rowSign G lab F Z v K = 1 := by
  unfold rowSign; split_ifs <;> norm_num

omit [Fintype V] in
lemma abs_rowSign (G : SimpleGraph V) (Z : Finset V) (v : V) (K : Finset V) :
    |(rowSign G lab F Z v K : ℝ)| = 1 := by
  unfold rowSign; split_ifs <;> norm_num

/-- **Signs agree up to one sign per component**, in `±1` form:
`sgn col_{G−Z}(v, K \ Z) u = rowSign · sgn col_G(v, K) u` for every `u ∈ K \ Z`. -/
theorem sgn_col_delG {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {v : V} (hv : v ∉ Z) {K : Finset V}
    (hK : S07V36.IsNRow G lab F (v, K)) (u : V) (hu : u ∈ K \ Z) :
    TypedTriangle.SignedCover.sgn (TypedTriangle.ComponentRows.col (delG G Z) lab F (v, K \ Z) u) =
      rowSign G lab F Z v K *
        TypedTriangle.SignedCover.sgn (TypedTriangle.ComponentRows.col G lab F (v, K) u) := by
  rw [col_flip hα hH3 hH4 hn hZ hv hK u hu]
  unfold rowSign
  cases flip G lab F Z v K <;> cases TypedTriangle.ComponentRows.col G lab F (v, K) u <;>
    simp [TypedTriangle.SignedCover.sgn]

/-- **Item 1, native rows under small vertex deletion (summary).** For every surviving root
`v ∉ Z` and active row `(v, K)` of `G`: `(v, K \ Z)` is an active row of `G − Z` (the
`G − Z` component of each of its members), it is bipartite iff `(v, K)` is, and in the
bipartite case the chosen signs agree up to the single sign `rowSign`. -/
theorem native_rows_deletion {α : ℝ} {h : ℕ} (hα : 0 < α) (hH3 : CommonNbrCond G lab F α)
    (hH4 : HingeCond G lab F α h) (hn : n1Of α ≤ Fintype.card V)
    (hZ : (Z.card : ℝ) ≤ delOf α h * Fintype.card V) {v : V} (hv : v ∉ Z) {K : Finset V}
    (hK : IsActiveRow G lab F (v, K)) :
    IsActiveRow (delG G Z) lab F (v, K \ Z) ∧
      (∀ u ∈ K \ Z, comp (delG G Z) lab F v u = K \ Z) ∧
      (IsBip (delG G Z) lab F (v, K \ Z) ↔ IsBip G lab F (v, K)) ∧
      (IsBip G lab F (v, K) → ∀ u ∈ K \ Z,
        TypedTriangle.SignedCover.sgn
            (TypedTriangle.ComponentRows.col (delG G Z) lab F (v, K \ Z) u) =
          rowSign G lab F Z v K *
            TypedTriangle.SignedCover.sgn (TypedTriangle.ComponentRows.col G lab F (v, K) u)) :=
  ⟨(row_survives hα hH3 hH4 hn hZ hv hK).1, (row_survives hα hH3 hH4 hn hZ hv hK).2,
    bip_iff hα hH3 hH4 hn hZ hv hK, fun hb => sgn_col_delG hα hH3 hH4 hn hZ hv ⟨hK, hb⟩⟩

end S07V39
