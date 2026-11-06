/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.S07V27.CoreSchedule
public import RequestProject.S07V26.RouteAdapter
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)

@[expose] public section

/-!
# V27 — the V25 core routes supply the per-root selector contract inside the core

`RouteProp G lab F t ε W` is, verbatim, the route property of the V25 core
(`S07V25.S07_core_H3H4`, last conjunct).

* `bfGraph Bf`: the forbidden edge window as a graph, `deg ≤ edeg Bf` (`bfGraph_degree_le`).
* `activeComps_disjoint`, `mem_activeComps_of_link`, `activeComp_wing`: active components of
  `L_v` are pairwise disjoint, cover every link vertex, and every vertex of one is adjacent to `v`.
* **`route_side_large`**: the V25 routes PAY for the auxiliary pools.  For an active component
  `C` of `L_v`, `|C ∩ W| > ⌊εn⌋` (non-bipartite), and each colour side of `C ∩ W` has more than
  `⌊εn⌋` vertices (bipartite): otherwise delete it and route an admissible pair of `C` around it;
  the first internal vertex of the route lies in `C ∩ W` (on the required side).
* **`coreAvail_component`**: one active component, PAR (`¬ IsBip`) or BAL (`IsBip`, sides by
  `colG`), with ports `U ⊆ C`: the core contract `CoreAvail` for the admissibility
  `compAdmC` (PAR: even; BAL: balanced), routed in `coreHost G lab F v W U (bfGraph Bf)`.
* **`coreAvail_root`**: all active components of one root at once (`coreAvail_biUnion`), ports
  `N_X(v)`, admissibility `rootAdm` (admissible in every active component).
-/

namespace S07V27

open Finset SimpleGraph SelBridge SelTyped SelSimul SelEmbed
open TypedTriangle.SparseEdge TypedTriangle.ComponentRows S07V24 S07V25 S07V26

noncomputable section
open Classical

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- The route property of the V25 core, verbatim. -/
def RouteProp (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (t : ℕ) (ε : ℝ)
    (W : Finset V) : Prop :=
  ∀ (Z : Finset V) (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ),
    (Z.card : ℝ) ≤ ε * Fintype.card V → (∀ u, B.degree u ≤ d) →
    (d : ℝ) ≤ ε * Fintype.card V →
    ∀ v x y, AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C))
        (colG G lab F) v x y →
      ∃ p ∈ pathsLen (link G lab F v) t x y, intlSet (t - 1) p ⊆ W ∧
        (∀ i : Fin (t - 1), intl (t - 1) p i ∉ Z) ∧
        ∀ k < t, ¬ B.Adj (p.getVert k) (p.getVert (k + 1))

omit [DecidableEq V] in
/-- `RouteProp` does not depend on the decidable-equality instance used for its finsets. -/
lemma routeProp_inst {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {t : ℕ} {ε : ℝ}
    {W : Finset V} (i j : DecidableEq V) (h : @RouteProp V I _ i G lab F t ε W) :
    @RouteProp V I _ j G lab F t ε W := by
  obtain rfl := Subsingleton.elim i j
  exact h

/-- The forbidden edge window as a graph. -/
def bfGraph (Bf : Finset (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet (Bf : Set (Sym2 V))

omit [Fintype V] [DecidableEq V] in
lemma bfGraph_adj {Bf : Finset (Sym2 V)} {x y : V} :
    (bfGraph Bf).Adj x y ↔ s(x, y) ∈ Bf ∧ x ≠ y := by
  simp [bfGraph]

lemma bfGraph_degree_le (Bf : Finset (Sym2 V)) (y : V) : (bfGraph Bf).degree y ≤ edeg Bf y := by
  rw [← card_neighborFinset_eq_degree]
  unfold edeg
  refine card_le_card_of_injOn (fun u => s(y, u)) ?_ ?_
  · intro u hu
    rw [mem_coe, mem_neighborFinset, bfGraph_adj] at hu
    simp only [coe_filter, Set.mem_setOf_eq]
    exact ⟨hu.1, Sym2.mem_mk_left y u⟩
  · intro a _ b _ h
    exact Sym2.congr_right.mp h

/-! ### Active components -/

omit [DecidableEq V] in
lemma activeComps_disjoint {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    {C C' : Finset V} (hC : C ∈ activeComps G lab F v) (hC' : C' ∈ activeComps G lab F v)
    (hne : C ≠ C') : Disjoint C C' := by
  obtain ⟨x, -, rfl⟩ := mem_activeComps.1 hC
  obtain ⟨x', -, rfl⟩ := mem_activeComps.1 hC'
  rw [Finset.disjoint_left]
  intro z hz hz'
  exact hne ((comp_eq_of_mem hz).symm.trans (comp_eq_of_mem hz'))

omit [DecidableEq V] in
lemma mem_activeComps_of_link {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v u y : V}
    (h : (link G lab F v).Adj u y) :
    comp G lab F v u ∈ activeComps G lab F v ∧ u ∈ comp G lab F v u :=
  ⟨mem_activeComps.2 ⟨u, ⟨y, h⟩, rfl⟩, mem_comp_iff.2 (Reachable.refl u)⟩

omit [DecidableEq V] in
lemma activeComp_closed {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    {C : Finset V} (hC : C ∈ activeComps G lab F v) {a z : V} (ha : a ∈ C)
    (h : (link G lab F v).Adj a z) : z ∈ C := by
  obtain ⟨x, -, rfl⟩ := mem_activeComps.1 hC
  exact mem_comp_iff.2 ((mem_comp_iff.1 ha).trans h.reachable)

omit [DecidableEq V] in
/-- every vertex of an active component has a link neighbour, hence is adjacent to the root -/
lemma activeComp_wing {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    {C : Finset V} (hC : C ∈ activeComps G lab F v) {a : V} (ha : a ∈ C) : G.Adj v a := by
  obtain ⟨x, ⟨y, hxy⟩, rfl⟩ := mem_activeComps.1 hC
  obtain ⟨z, hz⟩ : ∃ z, (link G lab F v).Adj a z := by
    by_cases hax : a = x
    · exact ⟨y, hax ▸ hxy⟩
    · obtain ⟨p⟩ := (mem_comp_iff.1 ha).symm
      cases p with
      | nil => exact absurd rfl hax
      | cons h _ => exact ⟨_, h⟩
  exact root_adj_of_typed (G := G) (lab := lab) (F := F) (v := v) hz

omit [DecidableEq V] in
lemma activeComp_admPair {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    {C : Finset V} (hC : C ∈ activeComps G lab F v) {a b : V} (ha : a ∈ C) (hb : b ∈ C)
    (hab : a ≠ b) (hcol : IsBip G lab F (v, C) → colG G lab F v a ≠ colG G lab F v b) :
    AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C)) (colG G lab F) v a b :=
  ⟨C, hC, ha, hb, hab, hcol⟩

omit [DecidableEq V] in
lemma activeComp_colG_ne {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    {C : Finset V} (hC : C ∈ activeComps G lab F v) (hb : IsBip G lab F (v, C)) {a z : V}
    (ha : a ∈ C) (hz : z ∈ C) (h : (link G lab F v).Adj a z) :
    colG G lab F v a ≠ colG G lab F v z := by
  obtain ⟨x, -, rfl⟩ := mem_activeComps.1 hC
  exact colG_proper hb ha hz h

/-! ### The routes pay for the auxiliary pools -/

lemma pathsLen_length {H : SimpleGraph V} [DecidableRel H.Adj] {t : ℕ} {x y : V}
    {p : H.Walk x y} (hp : p ∈ pathsLen H t x y) : p.length = t := by
  simp only [pathsLen, mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hp; exact hp.1

/-- The first internal vertex of a V25 route from `u` lies in `W`, is a link neighbour of `u`,
and avoids the deleted set. -/
lemma route_first_internal {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {t : ℕ}
    (ht3 : 3 ≤ t) {ε : ℝ} (hε : 0 < ε) {W : Finset V} (hroute : RouteProp G lab F t ε W)
    (Z : Finset V) (hZ : (Z.card : ℝ) ≤ ε * Fintype.card V) {v u w : V}
    (hadm : AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C)) (colG G lab F) v u w) :
    ∃ z, z ∈ W ∧ z ∉ Z ∧ (link G lab F v).Adj u z := by
  have h0 : ((0 : ℕ) : ℝ) ≤ ε * Fintype.card V := by
    push_cast; positivity
  obtain ⟨p, hp, hW, hZp, -⟩ := hroute Z ⊥ 0 hZ (fun u => by simp) h0 v u w hadm
  have hlen := pathsLen_length hp
  have hi : 0 < t - 1 := by omega
  refine ⟨intl (t - 1) p ⟨0, hi⟩, hW ((mem_intlSet _ _ _).2 ⟨_, rfl⟩), hZp _, ?_⟩
  have := p.adj_getVert_succ (i := 0) (by omega)
  simpa [intl] using this

/-- **The routes pay for the PAR pool**: `|C ∩ W| > ⌊εn⌋`. -/
theorem route_pool_large {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {t : ℕ}
    (ht3 : 3 ≤ t) {ε : ℝ} (hε : 0 < ε) {W : Finset V} (hroute : RouteProp G lab F t ε W)
    {v : V} {C : Finset V} (hC : C ∈ activeComps G lab F v) :
    ⌊ε * Fintype.card V⌋₊ < (C ∩ W).card := by
  obtain ⟨x, ⟨y, hxy⟩, rfl⟩ := mem_activeComps.1 hC
  have hy : y ∈ comp G lab F v x := mem_comp_iff.2 hxy.reachable
  have hx : x ∈ comp G lab F v x := mem_comp_iff.2 (Reachable.refl x)
  have hadm := activeComp_admPair hC hx hy hxy.1 (fun hb => activeComp_colG_ne hC hb hx hy hxy)
  by_contra hlt
  push_neg at hlt
  have hε0 : 0 ≤ ε * Fintype.card V := by positivity
  have hZ : (((comp G lab F v x) ∩ W).card : ℝ) ≤ ε * Fintype.card V :=
    (Nat.cast_le.2 hlt).trans (Nat.floor_le hε0)
  obtain ⟨z, hzW, hzZ, hz⟩ := route_first_internal ht3 hε hroute _ hZ hadm
  exact hzZ (mem_inter.2 ⟨activeComp_closed hC hx hz, hzW⟩)

/-- **The routes pay for the BAL pools**: each colour side of `C ∩ W` has `> ⌊εn⌋` vertices. -/
theorem route_side_large {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {t : ℕ}
    (ht3 : 3 ≤ t) {ε : ℝ} (hε : 0 < ε) {W : Finset V} (hroute : RouteProp G lab F t ε W)
    {v : V} {C : Finset V} (hC : C ∈ activeComps G lab F v) (hb : IsBip G lab F (v, C))
    (c : Bool) :
    ⌊ε * Fintype.card V⌋₊ < ((C ∩ W).filter (fun z => colG G lab F v z = c)).card := by
  obtain ⟨x, ⟨y, hxy⟩, hCx⟩ := mem_activeComps.1 hC
  have hy : y ∈ C := hCx ▸ mem_comp_iff.2 hxy.reachable
  have hx : x ∈ C := hCx ▸ mem_comp_iff.2 (Reachable.refl x)
  have hcxy := activeComp_colG_ne hC hb hx hy hxy
  -- an endpoint `u` of the edge whose colour is not `c`, and the other endpoint `w`
  obtain ⟨u, w, hu, hw, huw, hcu⟩ : ∃ u w, u ∈ C ∧ w ∈ C ∧ (link G lab F v).Adj u w ∧
      colG G lab F v u ≠ c := by
    by_cases h : colG G lab F v x = c
    · exact ⟨y, x, hy, hx, hxy.symm, fun h' => hcxy (h.trans h'.symm)⟩
    · exact ⟨x, y, hx, hy, hxy, h⟩
  have hadm := activeComp_admPair hC hu hw huw.1
    (fun _ => activeComp_colG_ne hC hb hu hw huw)
  by_contra hlt
  push_neg at hlt
  have hε0 : 0 ≤ ε * Fintype.card V := by positivity
  have hZ : ((((C ∩ W).filter (fun z => colG G lab F v z = c))).card : ℝ) ≤
      ε * Fintype.card V := (Nat.cast_le.2 hlt).trans (Nat.floor_le hε0)
  obtain ⟨z, hzW, hzZ, hz⟩ := route_first_internal ht3 hε hroute _ hZ hadm
  have hzC := activeComp_closed hC hu hz
  have hcz : colG G lab F v z = c := by
    have := activeComp_colG_ne hC hb hu hzC hz
    cases c <;> cases h1 : colG G lab F v u <;> cases h2 : colG G lab F v z <;> simp_all
  exact hzZ (mem_filter.2 ⟨mem_inter.2 ⟨hzC, hzW⟩, hcz⟩)

/-! ### The routing host -/

/-- The core routing host of a component, for every forbidden edge window. -/
theorem coreHost_spec {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {t : ℕ}
    (ht : Odd t) {ε : ℝ} {W : Finset V} (hroute : RouteProp G lab F t ε W) (v : V)
    (U : Finset V) {ρ : ℕ} (hρ : (ρ : ℝ) ≤ ε * Fintype.card V) (Allowed : V → V → Prop)
    (hAll : ∀ a b, Allowed a b →
      AdmPair (activeComps G lab F) (fun v C => IsBip G lab F (v, C)) (colG G lab F) v a b ∧
        a ∈ W ∪ U ∧ b ∈ W ∪ U)
    (Bf : Finset (Sym2 V)) (hBf : ∀ y, edeg Bf y ≤ ρ) :
    ∃ H : SimpleGraph V, H ≤ typedLink G lab F v ∧ (∀ x y, H.Adj x y → s(x, y) ∉ Bf) ∧
      (∀ x y, H.Adj x y → x ∈ W ∪ U) ∧
      RobustOddPaths H Allowed t ⌊ε * Fintype.card V⌋₊ := by
  refine ⟨coreHost G lab F v W U (bfGraph Bf), fun x y h => h.1, ?_,
    fun x y h => by convert h.2.1, ?_⟩
  · intro x y h hB
    exact h.2.2.2 (bfGraph_adj.2 ⟨hB, h.1.1⟩)
  · have hR := routes_robustOddPaths ht
      (routeProp_inst _ (fun a b => Classical.propDecidable (a = b)) hroute) v U (bfGraph Bf) ρ
      (fun u => (bfGraph_degree_le Bf u).trans (hBf u)) hρ
    intro Z hZ a b hab haZ hbZ
    obtain ⟨h1, h2, h3⟩ := hAll a b hab
    exact hR Z hZ a b ⟨h1, by convert h2, by convert h3⟩ haZ hbZ

/-! ### One component -/

/-- Admissibility of a demand in one active component: PAR even, BAL balanced (by `colG`). -/
def compAdmC (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (v : V) (C : Finset V)
    (S : Finset V) : Prop :=
  if IsBip G lab F (v, C) then
    (S.filter (fun x => colG G lab F v x = true)).card =
      (S.filter (fun x => colG G lab F v x = false)).card
  else Even S.card

omit [Fintype V] in
/-- Weakening the admissibility predicate of a valid selector. -/
theorem _root_.SelSimul.LocalSel.Valid.adm_weaken {G : SimpleGraph V} {lab : V → I}
    {F : Set (Multiset I)} {v : V} {U : Finset V} {Adm Adm' : Finset V → Prop} {Z0 : Finset V}
    {Bf : Finset (Sym2 V)} {A : ℕ} {σ : LocalSel V} (h : σ.Valid G lab F v U Adm Z0 Bf A)
    (hAA : ∀ S ⊆ U, Adm' S → Adm S) : σ.Valid G lab F v U Adm' Z0 Bf A where
  typed := h.typed
  avoidB := h.avoidB
  supp := h.supp
  wing := h.wing
  avoidZ := h.avoidZ
  portFree := h.portFree
  card_le := h.card_le
  deg_le := h.deg_le
  modes := fun S hS hA => h.modes S hS (hAA S hS hA)

omit [Fintype V] in
/-- Weakening the admissibility predicate on demands inside the port set. -/
theorem CoreAvail.adm_congr {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {v : V}
    {U : Finset V} {Adm Adm' : Finset V → Prop} {A ζ ρ : ℕ} {Wc : Finset V}
    (h : CoreAvail G lab F v U Adm A ζ ρ Wc) (hAA : ∀ S ⊆ U, Adm' S → Adm S) :
    CoreAvail G lab F v U Adm' A ζ ρ Wc := by
  intro Z0 Bf hZ0 hBf
  obtain ⟨σ, hσ, hW⟩ := h Z0 Bf hZ0 hBf
  exact ⟨σ, hσ.adm_weaken hAA, hW⟩

/-- **One active component, PAR or BAL, inside the core, from the V25 routes.** -/
theorem coreAvail_component {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {t : ℕ}
    (ht : Odd t) (ht3 : 3 ≤ t) {ε : ℝ} (hε : 0 < ε) {W : Finset V}
    (hroute : RouteProp G lab F t ε W) (v : V) (C : Finset V)
    (hC : C ∈ activeComps G lab F v) (U : Finset V) (hUC : U ⊆ C) {A ζ ρ : ℕ}
    (hA : 200 * (t - 1) + 8 ≤ A)
    (hBud : ζ + 10 * U.card + (t - 1) * (200 * U.card) ≤ ⌊ε * Fintype.card V⌋₊)
    (hρ : (ρ : ℝ) ≤ ε * Fintype.card V) :
    CoreAvail G lab F v U (compAdmC G lab F v C) A ζ ρ W := by
  set M := ⌊ε * Fintype.card V⌋₊ with hM
  set K := C.filter (fun z => z ∈ W ∪ U) with hK
  have hKC : K ⊆ C := filter_subset _ _
  have hUK : U ⊆ K := fun u hu => mem_filter.2 ⟨hUC hu, mem_union_right _ hu⟩
  have hKW : K ⊆ W ∪ U := fun z hz => (mem_filter.1 hz).2
  have hCWK : C ∩ W ⊆ K := fun z hz =>
    mem_filter.2 ⟨(mem_inter.1 hz).1, mem_union_left _ (mem_inter.1 hz).2⟩
  have hwing : ∀ a ∈ K, G.Adj v a := fun a ha => activeComp_wing hC (hKC ha)
  have h4 : (t - 1) * (4 * U.card) ≤ (t - 1) * (200 * U.card) :=
    Nat.mul_le_mul_left _ (by omega)
  by_cases hb : IsBip G lab F (v, C)
  · -- BAL
    set Xs := K.filter (fun z => colG G lab F v z = true) with hXs
    set Ys := K.filter (fun z => colG G lab F v z = false) with hYs
    have hconv : ∀ S ⊆ U, compAdmC G lab F v C S → (S ∩ Xs).card = (S ∩ Ys).card := by
      intro S hS h
      unfold compAdmC at h
      rw [if_pos hb] at h
      have e1 : S ∩ Xs = S.filter (fun x => colG G lab F v x = true) := by
        ext z; simp only [hXs, mem_inter, mem_filter]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hUK (hS h.1), h.2⟩⟩
      have e2 : S ∩ Ys = S.filter (fun x => colG G lab F v x = false) := by
        ext z; simp only [hYs, mem_inter, mem_filter]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hUK (hS h.1), h.2⟩⟩
      rw [e1, e2]; exact h
    rcases U.eq_empty_or_nonempty with hU | hU
    · subst hU
      exact coreAvail_empty G lab F v _ A ζ ρ W
    have hside : ∀ c : Bool, ζ + 10 * U.card ≤ (K.filter (fun z => colG G lab F v z = c)).card := by
      intro c
      have h1 := route_side_large ht3 hε hroute hC hb c
      have h2 : (C ∩ W).filter (fun z => colG G lab F v z = c) ⊆
          K.filter (fun z => colG G lab F v z = c) := filter_subset_filter _ hCWK
      have := card_le_card h2
      omega
    refine CoreAvail.adm_congr (coreAvail_bal G lab F v U K Xs Ys W (ℓ := t) (Bud := M) hU hA
      hBud (filter_subset _ _) (filter_subset _ _) ?_ ?_ (hside true) (hside false) hKW hwing
      (coreHost_spec ht hroute v U hρ _ ?_)) hconv
    · rw [Finset.disjoint_left]
      intro z hz hz'
      rw [mem_filter] at hz hz'
      rw [hz.2] at hz'; exact Bool.noConfusion hz'.2
    · intro u hu
      cases h : colG G lab F v u
      · exact mem_union_right _ (mem_filter.2 ⟨hUK hu, h⟩)
      · exact mem_union_left _ (mem_filter.2 ⟨hUK hu, h⟩)
    · intro a b hab
      rcases hab with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
      · rw [mem_filter] at ha hb'
        refine ⟨activeComp_admPair hC (hKC ha.1) (hKC hb'.1) ?_ ?_, hKW ha.1, hKW hb'.1⟩
        · intro h; rw [h, hb'.2] at ha; exact Bool.noConfusion ha.2
        · intro _; rw [ha.2, hb'.2]; decide
      · rw [mem_filter] at ha hb'
        refine ⟨activeComp_admPair hC (hKC ha.1) (hKC hb'.1) ?_ ?_, hKW ha.1, hKW hb'.1⟩
        · intro h; rw [h, hb'.2] at ha; exact Bool.noConfusion ha.2
        · intro _; rw [ha.2, hb'.2]; decide
  · -- PAR
    have hconv : ∀ S ⊆ U, compAdmC G lab F v C S → Even S.card := by
      intro S _ h
      unfold compAdmC at h
      rwa [if_neg hb] at h
    have hKc : ζ + 3 * U.card ≤ K.card := by
      have h1 := route_pool_large ht3 hε hroute hC
      have := card_le_card hCWK
      omega
    refine CoreAvail.adm_congr (coreAvail_par G lab F v U K W (ℓ := t) (Bud := M) (by omega)
      (by omega) hUK hKc hKW hwing (coreHost_spec ht hroute v U hρ _ ?_)) hconv
    intro a b hab
    obtain ⟨ha, hb', hne⟩ := hab
    exact ⟨activeComp_admPair hC (hKC ha) (hKC hb') hne (fun h => absurd h hb), hKW ha, hKW hb'⟩

/-! ### One root, all its active components -/

/-- S07 local admissibility of a demand at a root: admissible in every active component. -/
def rootAdm (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I)) (X : SimpleGraph V)
    [DecidableRel X.Adj] (v : V) (S : Finset V) : Prop :=
  ∀ C ∈ activeComps G lab F v, compAdmC G lab F v C (S ∩ (X.neighborFinset v ∩ C))

theorem rootAdm_empty (G : SimpleGraph V) (lab : V → I) (F : Set (Multiset I))
    (X : SimpleGraph V) [DecidableRel X.Adj] (v : V) : rootAdm G lab F X v ∅ := by
  intro C _
  unfold compAdmC
  split_ifs <;> simp

/-- **The per-root contract inside the core, all active components at once.** -/
theorem coreAvail_root {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)} {t : ℕ}
    (ht : Odd t) (ht3 : 3 ≤ t) {ε : ℝ} (hε : 0 < ε) {W : Finset V}
    (hroute : RouteProp G lab F t ε W) (X : SimpleGraph V) [DecidableRel X.Adj] (v : V)
    (hXl : ∀ u, X.Adj v u → ∃ y, (link G lab F v).Adj u y) {A ζ ρ r : ℕ}
    (hA : 200 * (t - 1) + 8 ≤ A) (hdeg : X.degree v ≤ r)
    (hBud : ζ + (A + 1) * r + 10 * r + (t - 1) * (200 * r) ≤ ⌊ε * Fintype.card V⌋₊)
    (hρ : ((ρ + 60 : ℕ) : ℝ) ≤ ε * Fintype.card V) :
    CoreAvail G lab F v (X.neighborFinset v) (rootAdm G lab F X v) A ζ ρ W := by
  set N := X.neighborFinset v with hN
  have hNr : N.card ≤ r := by rw [hN, card_neighborFinset_eq_degree]; exact hdeg
  have hUeq : N = (activeComps G lab F v).biUnion (fun C => N ∩ C) := by
    ext u
    simp only [mem_biUnion, mem_inter]
    constructor
    · intro hu
      obtain ⟨y, hy⟩ := hXl u ((mem_neighborFinset _ _ _).1 hu)
      obtain ⟨h1, h2⟩ := mem_activeComps_of_link hy
      exact ⟨_, h1, hu, h2⟩
    · rintro ⟨C, -, hu, -⟩; exact hu
  have hdisj : ∀ C ∈ activeComps G lab F v, ∀ C' ∈ activeComps G lab F v, C ≠ C' →
      Disjoint (N ∩ C) (N ∩ C') := fun C hC C' hC' hne =>
    Disjoint.mono inter_subset_right inter_subset_right (activeComps_disjoint hC hC' hne)
  have hcomp : ∀ C ∈ activeComps G lab F v, CoreAvail G lab F v (N ∩ C) (compAdmC G lab F v C)
      A (ζ + (A + 1) * r) (ρ + 60) W := by
    intro C hC
    have hc : (N ∩ C).card ≤ r := (card_le_card inter_subset_left).trans hNr
    have h1 : (t - 1) * (200 * (N ∩ C).card) ≤ (t - 1) * (200 * r) :=
      Nat.mul_le_mul_left _ (by omega)
    exact coreAvail_component ht ht3 hε hroute v C hC (N ∩ C) inter_subset_right hA
      (by omega) hρ
  have hbig := coreAvail_biUnion G lab F v (activeComps G lab F v) (fun C => N ∩ C)
    (compAdmC G lab F v) (ζ := ζ) (ρ := ρ) hdisj W hcomp
    (by rw [← hUeq]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hNr) _) le_rfl
  rw [← hUeq] at hbig
  exact hbig

end

end S07V27
