/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import RequestProject.S07V49.HingeLoss
set_option maxHeartbeats 1600000 -- build option (original: -DmaxHeartbeats=1600000)
set_option maxRecDepth 8192 -- build option (original: -DmaxRecDepth=8192)
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# V49 §5 — hinge statistics of the edge-deleted host on the same core

`edge_hinge_count`: let `U` (the surviving core `W ∖ Z`) carry the V25/V48 deletion conclusions
for hinges (original hinges of order `hOrd` with free vertices in `U`, at least
`α q^(i-4) n^(i-4) / 4`) and for pools (`|N_G(u,v;k) ∩ U| ≥ qαn/4`), and let `B` have maximum
degree `d` with

  `2 + 4d ≤ qαn/8`  and  `(5d + h + 1) 2^C(h,2) ≤ α q^h n / 8`.

Then for EVERY H4 test `(uva, uvb)` of the edge-deleted host `G \ B` (roots anywhere) there is an
order `i` with `9 ≤ i ≤ 2h - 3` such that the hinges of `G \ B` of order `i` for `(uva, uvb)`
whose free vertices lie in `U` number at least

  `hingeConstB α q h · n^(i-4)`,   `hingeConstB α q h = α³ q^(2h+1) / (2048 h² 2^C(2h,2))`.

Construction: a fresh apex `t ∈ N_G(u,v; lab a) ∩ U` with `ut, vt, at, bt ∉ B`, `t ∉ {a,b}`
(at least `qαn/8` choices), original hinges `J₁` for `(uva, uvt)` and `J₂` for `(uvt, uvb)` of
orders `i₁ = hOrd(u,v,a,t)`, `i₂ = hOrd(u,v,t,b)`, free in `U`, `B`-free, `b ∉ supp J₁`,
`a ∉ supp J₂`, disjoint free sets (each family at least half its V48 count after paying the
`B`-degree and forbidden-vertex losses), composed by `composite_hinge` into a hinge of order
`i₁ + i₂ - 3`; pigeonhole over the order, and the composition map has fibres of size at most
`2h · 2^C(2h,2)`. No common-neighbour or density assumption beyond the V48 pools is used.
-/

open Finset

noncomputable section
open Classical

namespace S07V49

open TypedTriangle.SparseEdge S07V24

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {lab : V → I} {F : Set (Multiset I)}

/-- the explicit normalized hinge constant of the edge-deleted host -/
def hingeConstB (α q : ℝ) (h : ℕ) : ℝ :=
  α ^ 3 * q ^ (2 * h + 1) / (2048 * (h : ℝ) ^ 2 * 2 ^ ((2 * h).choose 2))

lemma hingeConstB_pos {α q : ℝ} (hα : 0 < α) (hq : 0 < q) {h : ℕ} (hh : 1 ≤ h) :
    0 < hingeConstB α q h := by
  unfold hingeConstB
  have : (0 : ℝ) < h := by exact_mod_cast hh
  positivity

/-- an apex in the typed common neighbourhood closes an allowed triangle -/
lemma allowed_apex {u v a t : V} (hTa : IsAllowed G lab F {u, v, a})
    (ht : t ∈ commonNbrs G lab (lab a) u v) : IsAllowed G lab F {u, v, t} := by
  obtain ⟨huv, hua, hva⟩ := distinct_of_card_three hTa.1
  have hF : ({lab u, lab v, lab a} : Multiset I) ∈ F := by
    have := hTa.2.2
    rwa [map_lab_triple lab huv hua hva] at this
  simp only [commonNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  obtain ⟨hut, hvt, hlab⟩ := ht
  have hut' : u ≠ t := hut.ne
  have hvt' : v ≠ t := hvt.ne
  refine ⟨card_three_of_distinct huv hut' hvt', ?_, ?_⟩
  · have huvadj : G.Adj u v := hTa.2.1 u (by simp) v (by simp) huv
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | assumption | exact (show G.Adj _ _ from ‹_›).symm
  · rw [map_lab_triple lab huv hut' hvt', hlab]
    exact hF

/-- the fresh apices -/
def apexSet (G B : SimpleGraph V) [DecidableRel B.Adj] (lab : V → I) (U : Finset V)
    (u v a b : V) : Finset V :=
  (commonNbrs G lab (lab a) u v ∩ U).filter fun t =>
    t ≠ a ∧ t ≠ b ∧ ¬ B.Adj u t ∧ ¬ B.Adj v t ∧ ¬ B.Adj a t ∧ ¬ B.Adj b t

lemma apex_card (B : SimpleGraph V) [DecidableRel B.Adj] (U : Finset V) (u v a b : V) (d : ℕ)
    (hB : ∀ x, B.degree x ≤ d) :
    ((commonNbrs G lab (lab a) u v ∩ U).card : ℝ) - (2 + 4 * d) ≤
      (apexSet G B lab U u v a b).card := by
  set P := commonNbrs G lab (lab a) u v ∩ U
  set E : Finset V := {a, b} ∪ (B.neighborFinset u ∪ B.neighborFinset v ∪
    B.neighborFinset a ∪ B.neighborFinset b)
  have hsub : P \ E ⊆ apexSet G B lab U u v a b := by
    intro t ht
    simp only [P, E, mem_sdiff, mem_union, mem_insert, mem_singleton,
      SimpleGraph.mem_neighborFinset, not_or] at ht
    obtain ⟨htP, ⟨hta, htb⟩, ⟨⟨hu, hv⟩, ha⟩, hb⟩ := ht
    exact mem_filter.2 ⟨htP, hta, htb, hu, hv, ha, hb⟩
  have h1 : P.card ≤ (P \ E).card + E.card := by
    have := card_le_card_sdiff_add_card (s := P) (t := E); omega
  have hE : E.card ≤ 2 + 4 * d := by
    have e1 : E.card ≤ ({a, b} : Finset V).card + (B.neighborFinset u ∪ B.neighborFinset v ∪
      B.neighborFinset a ∪ B.neighborFinset b).card := card_union_le _ _
    have e2 := card_union_le (B.neighborFinset u ∪ B.neighborFinset v ∪ B.neighborFinset a)
      (B.neighborFinset b)
    have e3 := card_union_le (B.neighborFinset u ∪ B.neighborFinset v) (B.neighborFinset a)
    have e4 := card_union_le (B.neighborFinset u) (B.neighborFinset v)
    have e5 : ({a, b} : Finset V).card ≤ 2 := card_le_two
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at e2 e3 e4
    have := hB u; have := hB v; have := hB a; have := hB b
    omega
  have h2 := card_le_card hsub
  have : (P.card : ℝ) ≤ (apexSet G B lab U u v a b).card + (2 + 4 * d) := by
    have : P.card ≤ (apexSet G B lab U u v a b).card + (2 + 4 * d) := by omega
    exact_mod_cast this
  linarith

/-- arithmetic of the half-count after the losses -/
lemma half_loss {α q n d x A : ℝ} {h j : ℕ} (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hn : 0 ≤ n) (hj6 : 6 ≤ j) (hjh : j ≤ h) (hx : x ≤ h + 1) (hd : 0 ≤ d)
    (hA : α * q ^ (j - 4) * n ^ (j - 4) / 4 ≤ A)
    (hw : (5 * d + h + 1) * 2 ^ (h.choose 2) ≤ α * q ^ h * n / 8) :
    α * q ^ (j - 4) * n ^ (j - 4) / 8 ≤ A - (5 * d + x) * (2 ^ (j.choose 2) * n ^ (j - 5)) := by
  have hp : n ^ (j - 4) = n * n ^ (j - 5) := by rw [← pow_succ']; congr 1; omega
  have h2 : (2 : ℝ) ^ (j.choose 2) ≤ 2 ^ (h.choose 2) :=
    pow_le_pow_right₀ (by norm_num) (Nat.choose_le_choose 2 hjh)
  have hqh : q ^ h ≤ q ^ (j - 4) := pow_le_pow_of_le_one hq.le hq1 (by omega)
  have e1 : (5 * d + x) * 2 ^ (j.choose 2) ≤ α * q ^ (j - 4) * n / 8 := by
    have : (5 * d + x) * 2 ^ (j.choose 2) ≤ (5 * d + h + 1) * 2 ^ (h.choose 2) :=
      mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    have : α * q ^ h * n / 8 ≤ α * q ^ (j - 4) * n / 8 := by
      have := mul_le_mul_of_nonneg_left hqh hα.le
      have := mul_le_mul_of_nonneg_right this hn
      linarith
    linarith
  have hpos : 0 ≤ n ^ (j - 5) := by positivity
  have e2 := mul_le_mul_of_nonneg_right e1 hpos
  rw [hp] at hA ⊢
  nlinarith

/-- first family: `B`-free hinges for `(uva, uvt)`, free in `U`, avoiding `b` -/
def fam1 (G B : SimpleGraph V) [DecidableRel B.Adj] (lab : V → I) (F : Set (Multiset I)) {α : ℝ} {h : ℕ}
    (hH4 : HingeCond G lab F α h) (U : Finset V) (u v a b t : V) : Finset (Finset (Sym2 V)) :=
  (hinges G lab F u v a t (hOrd hH4 u v a t)).filter fun J => freeV u v a t J ⊆ U ∧
    (∀ e ∈ J, e ∉ B.edgeSet) ∧ Disjoint (support J) {b}

/-- second family: `B`-free hinges for `(uvt, uvb)`, free in `U`, avoiding `a` and `free(J₁)` -/
def fam2 (G B : SimpleGraph V) [DecidableRel B.Adj] (lab : V → I) (F : Set (Multiset I)) {α : ℝ} {h : ℕ}
    (hH4 : HingeCond G lab F α h) (U : Finset V) (u v a b t : V) (J1 : Finset (Sym2 V)) :
    Finset (Finset (Sym2 V)) :=
  (hinges G lab F u v t b (hOrd hH4 u v t b)).filter fun J => freeV u v t b J ⊆ U ∧
    (∀ e ∈ J, e ∉ B.edgeSet) ∧ Disjoint (support J) ({a} ∪ freeV u v a t J1)

set_option maxHeartbeats 4000000 in
/-- **normalized hinge count of the edge-deleted host, order `≤ 2h - 3`** -/
theorem edge_hinge_count {α q : ℝ} {h : ℕ} (hα : 0 < α) (hq : 0 < q) (hq1 : q ≤ 1)
    (hh : 6 ≤ h) (hH4 : HingeCond G lab F α h) {U : Finset V}
    (hhinge : ∀ u v a' b' : V, HingeTest G lab F u v a' b' →
      α * q ^ (hOrd hH4 u v a' b' - 4) *
          (Fintype.card V : ℝ) ^ (hOrd hH4 u v a' b' - 4) / 4 ≤
        ((hinges G lab F u v a' b' (hOrd hH4 u v a' b')).filter fun J =>
          freeV u v a' b' J ⊆ U).card)
    (hpool : ∀ u v : V, u ≠ v → ∀ k : I, ({lab u, lab v, k} : Multiset I) ∈ F →
      q * α * Fintype.card V / 4 ≤ ((commonNbrs G lab k u v) ∩ U).card)
    (B : SimpleGraph V) [DecidableRel B.Adj] (d : ℕ) (hB : ∀ x, B.degree x ≤ d)
    (hw1 : 2 + 4 * (d : ℝ) ≤ q * α * Fintype.card V / 8)
    (hw2 : (5 * (d : ℝ) + h + 1) * 2 ^ (h.choose 2) ≤ α * q ^ h * Fintype.card V / 8)
    {u v a b : V} (hT : HingeTest (G \ B) lab F u v a b) :
    ∃ i, 9 ≤ i ∧ i ≤ 2 * h - 3 ∧
      hingeConstB α q h * (Fintype.card V : ℝ) ^ (i - 4) ≤
        ((hinges (G \ B) lab F u v a b i).filter fun J => freeV u v a b J ⊆ U).card := by
  set n := Fintype.card V with hn
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hdR : (0 : ℝ) ≤ d := by positivity
  have hhR : (6 : ℝ) ≤ h := by exact_mod_cast hh
  obtain ⟨huv, hua, hva, hub, hvb, hab⟩ := roots_distinct hT
  have hTa : IsAllowed G lab F {u, v, a} := isAllowed_mono sdiff_le hT.2.1
  have hBuv : ¬ B.Adj u v := (allowed_sdiff_iff.1 hT.2.1).2 u (by simp) v (by simp)
  have hF : ({lab u, lab v, lab a} : Multiset I) ∈ F := by
    have := hTa.2.2; rwa [map_lab_triple lab huv hua hva] at this
  set T := apexSet G B lab U u v a b with hTdef
  have hTcard : q * α * n / 8 ≤ (T.card : ℝ) := by
    have := apex_card (G := G) (lab := lab) B U u v a b d hB
    have := hpool u v huv (lab a) hF
    linarith
  -- facts on the apices
  have hfact : ∀ t ∈ T, t ∈ U ∧ t ≠ a ∧ t ≠ b ∧ u ≠ t ∧ v ≠ t ∧ ¬ B.Adj a t ∧ ¬ B.Adj t b ∧
      IsAllowed (G \ B) lab F {u, v, t} ∧ HingeTest G lab F u v a t ∧
      HingeTest G lab F u v t b := by
    intro t ht
    obtain ⟨htP, hta, htb, hBu, hBv, hBa, hBb⟩ := mem_filter.1 ht
    obtain ⟨htc, htU⟩ := mem_inter.1 htP
    have hTt : IsAllowed G lab F {u, v, t} := allowed_apex hTa htc
    obtain ⟨-, hut, hvt⟩ := distinct_of_card_three hTt.1
    have hTt' : IsAllowed (G \ B) lab F {u, v, t} := by
      refine allowed_sdiff_iff.2 ⟨hTt, ?_⟩
      intro x hx y hy
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first
        | exact B.irrefl
        | exact hBuv | exact fun h' => hBuv h'.symm
        | exact hBu | exact fun h' => hBu h'.symm
        | exact hBv | exact fun h' => hBv h'.symm
    exact ⟨htU, hta, htb, hut, hvt, hBa, fun h' => hBb h'.symm, hTt',
      ⟨Ne.symm hta, hTa, hTt⟩, ⟨htb, hTt, isAllowed_mono sdiff_le hT.2.2⟩⟩
  -- the two families and their sizes
  have hN1 : ∀ t ∈ T, α * q ^ (hOrd hH4 u v a t - 4) * (n : ℝ) ^ (hOrd hH4 u v a t - 4) / 8 ≤
      (fam1 G B lab F hH4 U u v a b t).card := by
    intro t ht
    obtain ⟨htU, hta, htb, hut, hvt, hBa, hBb, hTt', hT1, hT2⟩ := hfact t ht
    obtain ⟨hi6, hih, -⟩ := hOrd_spec hH4 hT1
    have hdj : Disjoint ({b} : Finset V) {u, v, a, t} := by
      rw [Finset.disjoint_singleton_left]; simp only [mem_insert, mem_singleton, not_or]
      exact ⟨Ne.symm hub, Ne.symm hvb, Ne.symm hab, Ne.symm htb⟩
    have hloss := good_hinges_ge (G := G) (lab := lab) (F := F)
      ⟨huv, hua, hva, hut, hvt, Ne.symm hta⟩ (hOrd hH4 u v a t) hi6 U {b} hdj B d hB hBa
    have hA := hhinge u v a t hT1
    have := half_loss (x := (({b} : Finset V).card : ℝ)) hα hq hq1 hnR hi6 hih
      (by rw [card_singleton]; push_cast; linarith) hdR hA hw2
    exact this.trans hloss
  have hN2 : ∀ t ∈ T, ∀ J1 ∈ fam1 G B lab F hH4 U u v a b t,
      α * q ^ (hOrd hH4 u v t b - 4) * (n : ℝ) ^ (hOrd hH4 u v t b - 4) / 8 ≤
        (fam2 G B lab F hH4 U u v a b t J1).card := by
    intro t ht J1 hJ1
    obtain ⟨htU, hta, htb, hut, hvt, hBa, hBb, hTt', hT1, hT2⟩ := hfact t ht
    obtain ⟨hi6, hih, -⟩ := hOrd_spec hH4 hT2
    obtain ⟨hi6', hih', -⟩ := hOrd_spec hH4 hT1
    obtain ⟨hJ1H, -, -, hJ1b⟩ := mem_filter.1 hJ1
    have hfc := card_freeV (G := G) (lab := lab) (F := F) ⟨huv, hua, hva, hut, hvt, Ne.symm hta⟩
      hJ1H
    have hdj : Disjoint ({a} ∪ freeV u v a t J1) {u, v, t, b} := by
      rw [Finset.disjoint_left]
      intro x hx hxR
      simp only [mem_union, mem_singleton, freeV, mem_sdiff, mem_insert] at hx hxR
      rcases hx with rfl | ⟨hxs, hxr⟩
      · rcases hxR with h' | h' | h' | h'
        exacts [hua h'.symm, hva h'.symm, hta h'.symm, hab h']
      · rcases hxR with rfl | rfl | rfl | rfl
        · exact hxr (Or.inl rfl)
        · exact hxr (Or.inr (Or.inl rfl))
        · exact hxr (Or.inr (Or.inr (Or.inr rfl)))
        · exact Finset.disjoint_left.1 hJ1b hxs (mem_singleton_self _)
    have hloss := good_hinges_ge (G := G) (lab := lab) (F := F)
      ⟨huv, hut, hvt, hub, hvb, htb⟩ (hOrd hH4 u v t b) hi6 U ({a} ∪ freeV u v a t J1) hdj B d
      hB hBb
    have hA := hhinge u v t b hT2
    have hXc : ((({a} ∪ freeV u v a t J1).card : ℕ) : ℝ) ≤ h + 1 := by
      have := card_union_le ({a} : Finset V) (freeV u v a t J1)
      rw [card_singleton, hfc] at this
      have : ({a} ∪ freeV u v a t J1).card ≤ h + 1 := by omega
      exact_mod_cast this
    have := half_loss hα hq hq1 hnR hi6 hih hXc hdR hA hw2
    exact this.trans hloss
  -- the composite lands in the target family of order `i₁ + i₂ - 3`
  have hcomp : ∀ t ∈ T, ∀ J1 ∈ fam1 G B lab F hH4 U u v a b t,
      ∀ J2 ∈ fam2 G B lab F hH4 U u v a b t J1,
      J1 ∪ J2 ∪ wedge u v t ∈ (hinges (G \ B) lab F u v a b
          (hOrd hH4 u v a t + hOrd hH4 u v t b - 3)).filter
        (fun J => freeV u v a b J ⊆ U) ∧
      Disjoint J1 J2 ∧ Disjoint J2 (wedge u v t) ∧ t ∈ support J1 := by
    intro t ht J1 hJ1 J2 hJ2
    obtain ⟨htU, hta, htb, hut, hvt, hBa, hBb, hTt', hT1, hT2⟩ := hfact t ht
    obtain ⟨hi6, -, -⟩ := hOrd_spec hH4 hT1
    obtain ⟨hi6', -, -⟩ := hOrd_spec hH4 hT2
    obtain ⟨hJ1H, hJ1U, hJ1B, hJ1b⟩ := mem_filter.1 hJ1
    obtain ⟨hJ2H, hJ2U, hJ2B, hJ2X⟩ := mem_filter.1 hJ2
    have hJ1h := (mem_filter.1 hJ1H).2
    have hJ2h := (mem_filter.1 hJ2H).2
    have hb1 : b ∉ support J1 := fun h' => Finset.disjoint_left.1 hJ1b h' (mem_singleton_self _)
    have ha2 : a ∉ support J2 := fun h' => Finset.disjoint_left.1 hJ2X h' (by simp)
    have hfree : Disjoint (freeV u v a t J1) (freeV u v t b J2) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have hx2s : x ∈ support J2 := (mem_sdiff.1 hx2).1
      exact Finset.disjoint_left.1 hJ2X hx2s (mem_union_right _ hx1)
    obtain ⟨hJ, hsupp, hinter, hJ12, hJ2t⟩ := composite_hinge hT hTt' hta htb hJ1h.1 hJ2h.1
      hJ1B hJ2B hb1 ha2 hfree
    have hcard := card_support_composite hinter huv hut hvt
    have ht1 : t ∈ support J1 :=
      S10V23.roots_subset_support' hJ1h.1 huv hua hva hut hvt (by simp)
    refine ⟨mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hJ, ?_⟩,
      freeV_composite_subset hsupp hJ1U hJ2U htU⟩, hJ12, hJ2t, ht1⟩
    rw [hsupp]
    have := hJ1h.2; have := hJ2h.2
    omega
  -- pigeonhole on the order
  set ord : V → ℕ := fun t => hOrd hH4 u v a t + hOrd hH4 u v t b - 3 with hord
  have hmaps : ∀ t ∈ T, ord t ∈ Icc 9 (2 * h - 3) := by
    intro t ht
    obtain ⟨-, -, -, -, -, -, -, -, hT1, hT2⟩ := hfact t ht
    obtain ⟨a1, b1, -⟩ := hOrd_spec hH4 hT1
    obtain ⟨a2, b2, -⟩ := hOrd_spec hH4 hT2
    simp only [mem_Icc, hord]; omega
  have hIcc : ((Icc 9 (2 * h - 3)).card : ℝ) ≤ 2 * h := by
    have : (Icc 9 (2 * h - 3)).card ≤ 2 * h := by simp; omega
    exact_mod_cast this
  have hhpos : (0 : ℝ) < 2 * h := by linarith
  obtain ⟨i, hi, hTi⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps
    ⟨9, by simp; omega⟩ (b := (T.card : ℝ) / (2 * h)) (by
      rw [nsmul_eq_mul]
      calc ((Icc 9 (2 * h - 3)).card : ℝ) * ((T.card : ℝ) / (2 * h))
          ≤ (2 * h) * ((T.card : ℝ) / (2 * h)) :=
            mul_le_mul_of_nonneg_right hIcc (by positivity)
        _ = T.card := by field_simp)
  rw [mem_Icc] at hi
  refine ⟨i, hi.1, hi.2, ?_⟩
  set Ti := T.filter fun t => ord t = i with hTidef
  set S := Ti.sigma fun t => (fam1 G B lab F hH4 U u v a b t).sigma fun J1 =>
    fam2 G B lab F hH4 U u v a b t J1 with hSdef
  set M : ℝ := α ^ 2 * q ^ (2 * h) * (n : ℝ) ^ (i - 5) / 64 with hM
  -- size of the triple set
  have hS : (Ti.card : ℝ) * M ≤ S.card := by
    rw [hSdef, card_sigma]
    push_cast
    rw [← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro t ht
    obtain ⟨htT, hti⟩ := mem_filter.1 ht
    obtain ⟨-, -, -, -, -, -, -, -, hT1, hT2⟩ := hfact t htT
    obtain ⟨a1, b1, -⟩ := hOrd_spec hH4 hT1
    obtain ⟨a2, b2, -⟩ := hOrd_spec hH4 hT2
    rw [card_sigma]; push_cast
    set L1 : ℝ := α * q ^ (hOrd hH4 u v a t - 4) * (n : ℝ) ^ (hOrd hH4 u v a t - 4) / 8
    set L2 : ℝ := α * q ^ (hOrd hH4 u v t b - 4) * (n : ℝ) ^ (hOrd hH4 u v t b - 4) / 8
    have hL2 : 0 ≤ L2 := by positivity
    have hsum : (fam1 G B lab F hH4 U u v a b t).card * L2 ≤
        ∑ J1 ∈ fam1 G B lab F hH4 U u v a b t,
          ((fam2 G B lab F hH4 U u v a b t J1).card : ℝ) := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun J1 hJ1 => hN2 t htT J1 hJ1
    have hL1 := hN1 t htT
    have hML : M ≤ L1 * L2 := by
      have he : (hOrd hH4 u v a t - 4) + (hOrd hH4 u v t b - 4) = i - 5 := by
        simp only [hord] at hti; omega
      have hq2 : q ^ (2 * h) ≤ q ^ (i - 5) := pow_le_pow_of_le_one hq.le hq1 (by omega)
      have : L1 * L2 = α ^ 2 * q ^ (i - 5) * (n : ℝ) ^ (i - 5) / 64 := by
        simp only [L1, L2]
        rw [← he, pow_add, pow_add]; ring
      rw [this, hM]
      have hpn : 0 ≤ (n : ℝ) ^ (i - 5) := by positivity
      have := mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ α ^ 2)
      have := mul_le_mul_of_nonneg_right this hpn
      linarith
    calc M ≤ L1 * L2 := hML
      _ ≤ (fam1 G B lab F hH4 U u v a b t).card * L2 := mul_le_mul_of_nonneg_right hL1 hL2
      _ ≤ _ := hsum
  -- the composition map and its fibres
  set f : (Σ _ : V, Σ _ : Finset (Sym2 V), Finset (Sym2 V)) → Finset (Sym2 V) :=
    fun s => s.2.1 ∪ s.2.2 ∪ wedge u v s.1 with hf
  set Tgt := (hinges (G \ B) lab F u v a b i).filter fun J => freeV u v a b J ⊆ U with hTgt
  have hmemS : ∀ s ∈ S, s.1 ∈ T ∧ ord s.1 = i ∧ s.2.1 ∈ fam1 G B lab F hH4 U u v a b s.1 ∧
      s.2.2 ∈ fam2 G B lab F hH4 U u v a b s.1 s.2.1 := by
    rintro ⟨t, J1, J2⟩ hs
    simp only [hSdef, mem_sigma, hTidef, mem_filter] at hs
    exact ⟨hs.1.1, hs.1.2, hs.2.1, hs.2.2⟩
  have himg : S.image f ⊆ Tgt := by
    intro J hJ
    obtain ⟨⟨t, J1, J2⟩, hs, rfl⟩ := mem_image.1 hJ
    obtain ⟨htT, hti, hJ1, hJ2⟩ := hmemS _ hs
    have := (hcomp t htT J1 hJ1 J2 hJ2).1
    simp only [hord] at hti
    rw [hti] at this
    exact this
  have hfib : ∀ J ∈ S.image f, (S.filter fun s => f s = J).card ≤
      2 * h * 2 ^ ((2 * h).choose 2) := by
    intro J hJ
    have hJT := himg hJ
    obtain ⟨hJH, -⟩ := mem_filter.1 hJT
    obtain ⟨-, hJh, hJs⟩ := mem_filter.1 hJH
    set g : V × Finset (Sym2 V) → (Σ _ : V, Σ _ : Finset (Sym2 V), Finset (Sym2 V)) :=
      fun p => ⟨p.1, p.2, (J \ wedge u v p.1) \ p.2⟩
    have hsub : (S.filter fun s => f s = J) ⊆ ((freeV u v a b J) ×ˢ J.powerset).image g := by
      rintro ⟨t, J1, J2⟩ hs
      obtain ⟨hs, hfs⟩ := mem_filter.1 hs
      obtain ⟨htT, hti, hJ1, hJ2⟩ := hmemS _ hs
      obtain ⟨-, hJ12, hJ2t, ht1⟩ := hcomp t htT J1 hJ1 J2 hJ2
      obtain ⟨htU, hta, htb, hut, hvt, -⟩ := hfact t htT
      simp only [hf] at hfs
      subst hfs
      refine mem_image.2 ⟨(t, J1), mem_product.2 ⟨?_, ?_⟩, ?_⟩
      · simp only [freeV, mem_sdiff, mem_insert, mem_singleton, not_or]
        refine ⟨?_, Ne.symm hut, Ne.symm hvt, hta, htb⟩
        rw [support_union, support_union]
        exact mem_union_left _ (mem_union_left _ ht1)
      · rw [mem_powerset]; exact subset_union_left.trans subset_union_left
      · have hJ2eq : ((J1 ∪ J2 ∪ wedge u v t) \ wedge u v t) \ J1 = J2 := by
          ext e
          simp only [mem_sdiff, mem_union]
          constructor
          · rintro ⟨⟨(h1 | h2) | hw, hnw⟩, hn1⟩
            exacts [absurd h1 hn1, h2, absurd hw hnw]
          · intro he
            exact ⟨⟨Or.inl (Or.inr he), fun hw => Finset.disjoint_left.1 hJ2t he hw⟩,
              fun h1 => Finset.disjoint_left.1 hJ12 h1 he⟩
        simp only [g, hJ2eq]
    have hcf := card_freeV (G := G \ B) (lab := lab) (F := F) ⟨huv, hua, hva, hub, hvb, hab⟩ hJH
    have hJc : J.card ≤ i.choose 2 := by
      have hnd : ∀ e ∈ J, ¬ e.IsDiag := fun e he => not_isDiag_of_mem_edges (hJh.1 he)
      have := card_le_card (subset_triEdges_support hnd)
      rwa [card_triEdges, hJs] at this
    calc (S.filter fun s => f s = J).card
        ≤ (((freeV u v a b J) ×ˢ J.powerset).image g).card := card_le_card hsub
      _ ≤ ((freeV u v a b J) ×ˢ J.powerset).card := card_image_le
      _ = (i - 4) * 2 ^ J.card := by rw [card_product, card_powerset, hcf]
      _ ≤ 2 * h * 2 ^ ((2 * h).choose 2) := by
          apply Nat.mul_le_mul (by omega)
          apply Nat.pow_le_pow_right (by norm_num)
          exact hJc.trans (Nat.choose_le_choose 2 (by omega : i ≤ 2 * h))
  have hcount := card_le_mul_card_image S _ hfib
  have hTgt' : ((S.image f).card : ℝ) ≤ Tgt.card := by exact_mod_cast card_le_card himg
  have hcountR : (S.card : ℝ) ≤ (2 * h * 2 ^ ((2 * h).choose 2) : ℕ) * (S.image f).card := by
    exact_mod_cast hcount
  push_cast at hcountR
  -- final arithmetic
  have hD : (0 : ℝ) < 2 * h * 2 ^ ((2 * h).choose 2) := by positivity
  have hfinal : (T.card : ℝ) / (2 * h) * M ≤ 2 * h * 2 ^ ((2 * h).choose 2) * Tgt.card := by
    have h1 : (T.card : ℝ) / (2 * h) * M ≤ Ti.card * M :=
      mul_le_mul_of_nonneg_right hTi (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hTgt' hD.le
    linarith
  have hpn : (n : ℝ) ^ (i - 4) = n * (n : ℝ) ^ (i - 5) := by
    rw [← pow_succ']; congr 1; omega
  have hlow : hingeConstB α q h * (n : ℝ) ^ (i - 4) * (2 * h * 2 ^ ((2 * h).choose 2)) ≤
      (T.card : ℝ) / (2 * h) * M := by
    rw [hpn, hM]
    unfold hingeConstB
    have hpos5 : 0 ≤ (n : ℝ) ^ (i - 5) := by positivity
    have hTc : q * α * n / 8 / (2 * h) ≤ (T.card : ℝ) / (2 * h) :=
      div_le_div_of_nonneg_right hTcard hhpos.le
    have hM0 : 0 ≤ α ^ 2 * q ^ (2 * h) * (n : ℝ) ^ (i - 5) / 64 := by positivity
    have := mul_le_mul_of_nonneg_right hTc hM0
    refine le_trans (le_of_eq ?_) this
    field_simp
    ring
  have := hlow.trans hfinal
  exact le_of_mul_le_mul_right (by linarith) hD

end S07V49
