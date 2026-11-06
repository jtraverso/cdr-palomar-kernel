/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V45.CoreLink
@[expose] public section

/-!
# V45 §2 — the transparent core path contract; components and bipartiteness of the core link

`CorePathContract H lab F W t`: for every root `v ∈ W` and every ORIGINAL admissible pair `(x, y)`
(native V25 data: `S07V25.activeComps`, `IsBip`, `S07V25.colG`) there is a simple path of the
ORIGINAL link `L_v(H)` of length exactly `t` from `x` to `y` whose internal vertices lie in `W`.
This is literally the `Z = ∅`, `B = ⊥` instance of the route conclusion of
`S07V25.S07_core_H3H4` (derived in `CoreSpecialize.lean`), not an extra hypothesis on the host.

With `t` odd and `t ≥ 3`, for every root `v ∈ W`:

* `core_active_of_mem` — every vertex of `W` lying in an original active component is active in
  the TRUE core link `L_v(H[W])` (the core pool is derived from the routes);
* `core_comp_eq` — its core component is exactly `C ∩ W` (connectivity AND no mixing);
* `activeComps_core` — the active components of the core link are exactly the nonempty
  intersections `C ∩ W` of original active components `C`; `inter_injective` — distinct original
  components give distinct intersections;
* `bip_core_iff` — bipartiteness is preserved and reflected on each nonempty `C ∩ W`;
  `col_core_flip` — the chosen core colouring and the restricted original colouring agree up to
  ONE flip per component.
-/

open Finset Classical

noncomputable section

namespace S07V45

open TypedTriangle.SparseEdge TypedTriangle.ComponentRows TypedTriangle.Composition
open TypedTriangle.ActiveCover S07V42

variable {V I : Type*} [Fintype V]

section defs

variable (H : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))

/-- admissible pairs of the ORIGINAL host, with the native V25 component data -/
abbrev OrigAdm (v x y : V) : Prop :=
  S07V24.AdmPair (S07V25.activeComps H lab F) (fun v C => IsBip H lab F (v, C))
    (S07V25.colG H lab F) v x y

/-- **the transparent core path contract** (odd length `t` is a separate hypothesis) -/
def CorePathContract (W : Finset V) (t : ℕ) : Prop :=
  ∀ v ∈ W, ∀ x y, OrigAdm H lab F v x y →
    ∃ p : (link H lab F v).Walk x y, p.length = t ∧ p.IsPath ∧
      ∀ i, 0 < i → i < t → p.getVert i ∈ W

end defs

variable {H : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-! ### Generic facts on original components -/

omit [Fintype V] in
lemma support_reach {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    ∀ u ∈ p.support, G.Reachable a u := by
  induction p with
  | nil => intro u hu; simp at hu; subst hu; exact SimpleGraph.Reachable.refl _
  | @cons a c b hac p ih =>
    intro u hu
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact SimpleGraph.Reachable.refl _
    · exact hac.reachable.trans (ih u hu)

lemma activeComps_eq {v : V} {C : Finset V} (hC : C ∈ S07V25.activeComps H lab F v) {u : V}
    (hu : u ∈ C) : comp H lab F v u = C := by
  obtain ⟨x0, -, rfl⟩ := S07V25.mem_activeComps.1 hC
  exact comp_eq_of_mem H lab F hu

lemma mem_of_adj {v : V} {C : Finset V} (hC : C ∈ S07V25.activeComps H lab F v) {u w : V}
    (hu : u ∈ C) (h : (link H lab F v).Reachable u w) : w ∈ C := by
  rw [← activeComps_eq hC hu, mem_comp_iff]; exact h

lemma colG_eq {v : V} {C : Finset V} (hC : C ∈ S07V25.activeComps H lab F v) {u : V}
    (hu : u ∈ C) : S07V25.colG H lab F v u = col H lab F (v, C) u := by
  unfold S07V25.colG; rw [activeComps_eq hC hu]

omit [Fintype V] in
lemma col_proper {j : Row V} (hB : IsBip H lab F j) {u w : V} (hu : u ∈ j.2) (hw : w ∈ j.2)
    (h : (link H lab F j.1).Adj u w) : col H lab F j u ≠ col H lab F j w := by
  unfold col; rw [dif_pos hB]; exact Classical.choose_spec hB u hu w hw h

lemma link_nbr {v : V} {C : Finset V} (hC : C ∈ S07V25.activeComps H lab F v) {z : V}
    (hz : z ∈ C) : ∃ y, (link H lab F v).Adj z y := by
  obtain ⟨x0, ⟨y0, hy0⟩, rfl⟩ := S07V25.mem_activeComps.1 hC
  rw [mem_comp_iff] at hz
  obtain ⟨p⟩ := hz.symm
  cases p with
  | nil => exact ⟨y0, hy0⟩
  | cons h _ => exact ⟨_, h⟩

lemma mem_activeComps_of_active {v u w : V} (h : (link H lab F v).Adj u w) :
    comp H lab F v u ∈ S07V25.activeComps H lab F v :=
  S07V25.mem_activeComps.2 ⟨u, ⟨w, h⟩, rfl⟩

lemma self_mem_comp (v u : V) : u ∈ comp H lab F v u := by
  rw [mem_comp_iff]

/-! ### Consequences of the contract -/

variable {W : Finset V} {t : ℕ}

/-- an original admissible pair inside `W` has a core-link walk of length `t` -/
theorem core_walk_of_adm (hCt : CorePathContract H lab F W t) {v a b : V} (hv : v ∈ W)
    (hab : OrigAdm H lab F v a b) (ha : a ∈ W) (hb : b ∈ W) :
    ∃ q : (link (indG H W) lab F v).Walk a b, q.length = t := by
  obtain ⟨p, hpl, -, hpW⟩ := hCt v hv a b hab
  have hs : ∀ u ∈ p.support, u ∈ W := by
    intro u hu
    obtain ⟨n, rfl, hn⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hu
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; rw [SimpleGraph.Walk.getVert_zero]; exact ha
    · rcases lt_or_eq_of_le hn with h1 | h1
      · exact hpW n h0 (hpl ▸ h1)
      · rw [h1, SimpleGraph.Walk.getVert_length]; exact hb
  obtain ⟨q, hq, -⟩ := walk_to_core hv p hs
  exact ⟨q, hq.trans hpl⟩

theorem adm_starIm (hCt : CorePathContract H lab F W t) (ht : Odd t) {v a b : V} (hv : v ∈ W)
    (hab : OrigAdm H lab F v a b) (ha : a ∈ W) (hb : b ∈ W) :
    dl a + dl b ∈ starIm (indG H W) lab F v := by
  obtain ⟨q, hq⟩ := core_walk_of_adm hCt hv hab ha hb
  exact (walk_starIm _ lab F q).2 (hq ▸ ht)

theorem adm_reach (hCt : CorePathContract H lab F W t) {v a b : V} (hv : v ∈ W)
    (hab : OrigAdm H lab F v a b) (ha : a ∈ W) (hb : b ∈ W) :
    (link (indG H W) lab F v).Reachable a b := by
  obtain ⟨q, -⟩ := core_walk_of_adm hCt hv hab ha hb
  exact ⟨q⟩

/-- **core pool from the routes**: a vertex of `W` in an original active component has a core
neighbour `n`, which has a further core neighbour `m ≠ z` -/
theorem core_nbr (hCt : CorePathContract H lab F W t) (ht3 : 3 ≤ t) {v : V} (hv : v ∈ W)
    {C : Finset V} (hC : C ∈ S07V25.activeComps H lab F v) {z : V} (hz : z ∈ C) (hzW : z ∈ W) :
    ∃ n m, (link (indG H W) lab F v).Adj z n ∧ (link (indG H W) lab F v).Adj n m ∧ m ≠ z := by
  obtain ⟨y, hy⟩ := link_nbr hC hz
  have hyC : y ∈ C := mem_of_adj hC hz hy.reachable
  have hadm : OrigAdm H lab F v z y := by
    refine ⟨C, hC, hz, hyC, hy.ne, fun hB => ?_⟩
    rw [colG_eq hC hz, colG_eq hC hyC]
    exact col_proper hB hz hyC hy
  obtain ⟨p, hpl, hpP, hpW⟩ := hCt v hv z y hadm
  have h1 := p.adj_getVert_succ (i := 0) (by omega)
  have h2 := p.adj_getVert_succ (i := 1) (by omega)
  rw [SimpleGraph.Walk.getVert_zero] at h1
  have hW1 : p.getVert 1 ∈ W := hpW 1 (by omega) (by omega)
  have hW2 : p.getVert 2 ∈ W := hpW 2 (by omega) (by omega)
  refine ⟨p.getVert 1, p.getVert 2, link_indG_adj.2 ⟨h1, hv, hzW, hW1⟩,
    link_indG_adj.2 ⟨h2, hv, hW1, hW2⟩, fun he => ?_⟩
  have := hpP.getVert_injOn (show 2 ∈ {i | i ≤ p.length} by simp; omega)
    (show 0 ∈ {i | i ≤ p.length} by simp) (by rw [he, SimpleGraph.Walk.getVert_zero])
  omega

/-! ### Item 1: active components of the core link -/

theorem core_active_of_mem (hCt : CorePathContract H lab F W t) (ht3 : 3 ≤ t) {v : V}
    (hv : v ∈ W) {C : Finset V} (hC : C ∈ S07V25.activeComps H lab F v) {x : V} (hx : x ∈ C)
    (hxW : x ∈ W) : LinkActive (indG H W) lab F v x := by
  obtain ⟨n, -, hn, -, -⟩ := core_nbr hCt ht3 hv hC hx hxW
  exact ⟨n, hn⟩

/-- **connectivity and no mixing**: the core component of `x ∈ C ∩ W` is exactly `C ∩ W` -/
theorem core_comp_eq (hCt : CorePathContract H lab F W t) (ht3 : 3 ≤ t) {v : V} (hv : v ∈ W)
    {C : Finset V} (hC : C ∈ S07V25.activeComps H lab F v) {x : V} (hx : x ∈ C) (hxW : x ∈ W) :
    comp (indG H W) lab F v x = C ∩ W := by
  ext y
  rw [mem_comp_iff, Finset.mem_inter]
  constructor
  · intro h
    exact ⟨mem_of_adj hC hx (h.mono (link_indG_le v)), reach_core_mem h hxW⟩
  · rintro ⟨hy, hyW⟩
    by_cases hxy : x = y
    · subst hxy; exact SimpleGraph.Reachable.refl _
    by_cases hbad : IsBip H lab F (v, C) ∧ col H lab F (v, C) x = col H lab F (v, C) y
    · obtain ⟨n, -, hn, -, -⟩ := core_nbr hCt ht3 hv hC hy hyW
      have hnL := link_indG_le v hn
      have hnC : n ∈ C := mem_of_adj hC hy hnL.reachable
      have hnW : n ∈ W := (link_indG_adj.1 hn).2.2.2
      have hcol : col H lab F (v, C) y ≠ col H lab F (v, C) n := col_proper hbad.1 hy hnC hnL
      have hadm : OrigAdm H lab F v x n := by
        refine ⟨C, hC, hx, hnC, fun h => ?_, fun _ => ?_⟩
        · subst h; exact hcol hbad.2.symm
        · rw [colG_eq hC hx, colG_eq hC hnC, hbad.2]; exact hcol
      exact (adm_reach hCt hv hadm hxW hnW).trans hn.symm.reachable
    · have hadm : OrigAdm H lab F v x y := by
        refine ⟨C, hC, hx, hy, hxy, fun hB => ?_⟩
        rw [colG_eq hC hx, colG_eq hC hy]
        exact fun h => hbad ⟨hB, h⟩
      exact adm_reach hCt hv hadm hxW hyW

/-- **the active components of the TRUE core link** are exactly the nonempty intersections
`C ∩ W` of the original active components -/
theorem activeComps_core (hCt : CorePathContract H lab F W t) (ht3 : 3 ≤ t) {v : V}
    (hv : v ∈ W) :
    S07V25.activeComps (indG H W) lab F v =
      ((S07V25.activeComps H lab F v).filter (fun C => (C ∩ W).Nonempty)).image (· ∩ W) := by
  ext K
  rw [S07V25.mem_activeComps, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨y, hxy⟩, rfl⟩
    have hxW : x ∈ W := (link_indG_adj.1 hxy).2.2.1
    have hC := mem_activeComps_of_active (link_indG_le v hxy)
    refine ⟨comp H lab F v x, Finset.mem_filter.2 ⟨hC, ⟨x, Finset.mem_inter.2
      ⟨self_mem_comp v x, hxW⟩⟩⟩, ?_⟩
    exact (core_comp_eq hCt ht3 hv hC (self_mem_comp v x) hxW).symm
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨hC, ⟨x, hx⟩⟩ := Finset.mem_filter.1 hC
    rw [Finset.mem_inter] at hx
    exact ⟨x, core_active_of_mem hCt ht3 hv hC hx.1 hx.2, core_comp_eq hCt ht3 hv hC hx.1 hx.2⟩

/-- distinct original active components have distinct nonempty traces on `W` -/
theorem inter_injective {W : Finset V} {v : V} {C₁ C₂ : Finset V}
    (h₁ : C₁ ∈ S07V25.activeComps H lab F v) (h₂ : C₂ ∈ S07V25.activeComps H lab F v)
    (hne : (C₁ ∩ W).Nonempty) (heq : C₁ ∩ W = C₂ ∩ W) : C₁ = C₂ := by
  obtain ⟨x, hx⟩ := hne
  have hx2 : x ∈ C₂ ∩ W := heq ▸ hx
  rw [← activeComps_eq h₁ (Finset.mem_inter.1 hx).1, activeComps_eq h₂ (Finset.mem_inter.1 hx2).1]

/-! ### Item 2: bipartiteness and colourings -/

lemma core_walk_support (hCt : CorePathContract H lab F W t) (ht3 : 3 ≤ t) {v : V} (hv : v ∈ W)
    {C : Finset V} (hC : C ∈ S07V25.activeComps H lab F v) {a b : V} (ha : a ∈ C) (haW : a ∈ W)
    (q : (link (indG H W) lab F v).Walk a b) : ∀ u ∈ q.support, u ∈ C ∩ W := by
  intro u hu
  rw [← core_comp_eq hCt ht3 hv hC ha haW, mem_comp_iff]
  exact support_reach q u hu

/-- **bipartiteness is preserved and reflected** on each nonempty `C ∩ W` -/
theorem bip_core_iff (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t) {v : V}
    (hv : v ∈ W) {C : Finset V} (hC : C ∈ S07V25.activeComps H lab F v) {x : V} (hx : x ∈ C)
    (hxW : x ∈ W) : IsBip (indG H W) lab F (v, C ∩ W) ↔ IsBip H lab F (v, C) := by
  constructor
  · rintro ⟨c, hc⟩
    by_contra hnb
    obtain ⟨n, m, hxn, hnm, hmx⟩ := core_nbr hCt ht3 hv hC hx hxW
    have hnC : n ∈ C := mem_of_adj hC hx (link_indG_le v hxn).reachable
    have hmC : m ∈ C := mem_of_adj hC hnC (link_indG_le v hnm).reachable
    have hmW : m ∈ W := (link_indG_adj.1 hnm).2.2.2
    have hadm : OrigAdm H lab F v m x := ⟨C, hC, hmC, hx, hmx, fun h => absurd h hnb⟩
    obtain ⟨q, hq⟩ := core_walk_of_adm hCt hv hadm hmW hxW
    have hc' : ∀ u ∈ C ∩ W, ∀ w ∈ C ∩ W, (link (indG H W) lab F v).Adj u w → c u ≠ c w :=
      fun u hu w hw h => hc u hu w hw h
    have e1 := walk_col_parity _ lab F hc' q
      (core_walk_support hCt ht3 hv hC hmC hmW q)
    let r : (link (indG H W) lab F v).Walk x m :=
      SimpleGraph.Walk.cons hxn (SimpleGraph.Walk.cons hnm SimpleGraph.Walk.nil)
    have e2 := walk_col_parity _ lab F hc' r (core_walk_support hCt ht3 hv hC hx hxW r)
    have hr : r.length = 2 := rfl
    rw [hq] at e1
    rw [hr] at e2
    simp only [ht, decide_true] at e1
    have h2 : ¬ Odd 2 := by decide
    simp only [h2, decide_false] at e2
    revert e1 e2
    cases c m <;> cases c x <;> simp
  · intro hB
    exact ⟨col H lab F (v, C), fun u hu w hw h =>
      col_proper hB (Finset.mem_inter.1 hu).1 (Finset.mem_inter.1 hw).1 (link_indG_le v h)⟩

/-- **colourings agree up to one flip** on each bipartite `C ∩ W` -/
theorem col_core_flip (hCt : CorePathContract H lab F W t) (ht : Odd t) (ht3 : 3 ≤ t) {v : V}
    (hv : v ∈ W) {C : Finset V} (hC : C ∈ S07V25.activeComps H lab F v) {x : V} (hx : x ∈ C)
    (hxW : x ∈ W) (hB : IsBip H lab F (v, C)) :
    ∃ s : Bool, ∀ u ∈ C ∩ W,
      col (indG H W) lab F (v, C ∩ W) u = xor s (col H lab F (v, C) u) := by
  have hB' := (bip_core_iff hCt ht ht3 hv hC hx hxW).2 hB
  set c1 := col H lab F (v, C)
  set c2 := col (indG H W) lab F (v, C ∩ W)
  have hc1 : ∀ u ∈ C ∩ W, ∀ w ∈ C ∩ W, (link (indG H W) lab F v).Adj u w → c1 u ≠ c1 w :=
    fun u hu w hw h =>
      col_proper hB (Finset.mem_inter.1 hu).1 (Finset.mem_inter.1 hw).1 (link_indG_le v h)
  have hc2 : ∀ u ∈ C ∩ W, ∀ w ∈ C ∩ W, (link (indG H W) lab F v).Adj u w → c2 u ≠ c2 w :=
    fun u hu w hw h => col_proper hB' hu hw h
  refine ⟨xor (c1 x) (c2 x), fun u hu => ?_⟩
  have hr : (link (indG H W) lab F v).Reachable x u := by
    rw [← mem_comp_iff, core_comp_eq hCt ht3 hv hC hx hxW]; exact hu
  obtain ⟨q⟩ := hr
  have hs := core_walk_support hCt ht3 hv hC hx hxW q
  have e1 := walk_col_parity _ lab F hc1 q hs
  have e2 := walk_col_parity _ lab F hc2 q hs
  rw [← e2] at e1
  revert e1
  cases c1 x <;> cases c2 x <;> cases c1 u <;> cases c2 u <;> simp

end S07V45
