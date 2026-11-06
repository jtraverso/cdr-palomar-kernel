/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.KiteDefs

/-!
# CCJS Theorem 1.2: setup and Case 1

`MainSetup` collects the data of the proof: a vertex `a` of minimum degree `k`, a neighbour `b` of
degree `Δ`, a colouring of `G − ab`, the colour `β` missing at `b` and the neighbour `cc` of `a`
with `φ(a cc) = β`. A vertex `v ≠ a` is *small* if `d(v) ≤ n − Δ + 2k − 6`.

Case 1 (two small vertices) is impossible: either a kite violates `KiteProp`, or a fork violates
the fork lemma.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem good_symm {k : ℕ} {c : PEC G (Fin k)} {a b x w : V} :
    Good c a b x w ↔ Good c a b w x := by
  unfold Good; rw [c.col_symm]

theorem Good.adj {k : ℕ} {c : PEC G (Fin k)} {a b x w : V} (h : Good c a b x w) : G.Adj x w := by
  obtain ⟨θ, hθ, -⟩ := h; exact c.col_adj hθ

/-- The data of the proof of CCJS Theorem 1.2. -/
structure MainSetup (G : SimpleGraph V) [DecidableRel G.Adj] (c : PEC G (Fin G.maxDegree))
    (a b cc : V) (k : ℕ) (β : Fin G.maxDegree) : Prop where
  crit : IsDeltaCritical G
  cm : IsColMinus c a b
  da : G.degree a = k
  hmin : ∀ v, k ≤ G.degree v
  db : G.degree b = G.maxDegree
  βb : c.IsFree b β
  acc : c.col a cc = some β
  hcond : 3 * Fintype.card V + 7 * k ≤ 4 * G.maxDegree + 10

/-- `v ≠ a` is small: `d(v) ≤ n − Δ + 2k − 6`. -/
def Small (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (k : ℕ) (v : V) : Prop :=
  v ≠ a ∧ G.degree v + G.maxDegree + 6 ≤ Fintype.card V + 2 * k

namespace MainSetup

variable {c : PEC G (Fin G.maxDegree)} {a b cc : V} {k : ℕ} {β : Fin G.maxDegree}
  (S : MainSetup G c a b cc k β)
include S

theorem nonA_eq : #(nonA c a b) + 2 = k := by
  rw [← S.da]; exact S.cm.card_nonA_eq S.crit.2.1 S.db

theorem k2 : 2 ≤ k := by have := S.nonA_eq; omega

theorem kΔ : k ≤ G.maxDegree := by rw [← S.da]; exact G.degree_le_maxDegree a

theorem adj_cc : G.Adj a cc := c.col_adj S.acc

theorem cc_ne_a : cc ≠ a := S.adj_cc.ne.symm

theorem cc_ne_b : cc ≠ b := by
  rintro rfl
  have h := S.acc
  rw [S.cm.uncol] at h
  cases h

theorem cc_deg : G.maxDegree + 2 ≤ G.degree cc + k := by
  have := deg_add S.crit S.adj_cc
  rw [S.da] at this
  omega

theorem free_a_of_good_b {w : V} {δ : Fin G.maxDegree} (h : c.col b w = some δ) (hA : InA c a b δ) :
    c.IsFree a δ :=
  hA.resolve_right fun hb => hb _ h

theorem small_deg {v : V} (h : Small G a k v) : G.degree v + k ≤ G.maxDegree := by
  have := S.hcond
  have := h.2
  omega

theorem small_ne_b {v : V} (h : Small G a k v) : v ≠ b := by
  rintro rfl
  have := S.small_deg h
  have := S.db
  have := S.k2
  omega

theorem small_not_adj_a {v : V} (h : Small G a k v) : ¬ G.Adj v a := by
  intro hva
  have h1 := val_crit S.crit hva.symm
  have h2 := card_maxNbrs_le hva.symm
  have := S.small_deg h
  rw [S.da] at h2
  omega

theorem two_inA {v : V} (h : Small G a k v) :
    ∃ θ₁ θ₂, θ₁ ≠ θ₂ ∧ InA c a b θ₁ ∧ InA c a b θ₂ ∧ c.IsFree v θ₁ ∧ c.IsFree v θ₂ :=
  exists_two_inA S.crit.2.1 S.cm S.db h.1 (S.small_ne_b h) (by rw [S.da]; exact S.small_deg h)

theorem big_of_not_small {v : V} (hva : v ≠ a) (hns : ¬ Small G a k v) :
    G.maxDegree + 1 ≤ G.degree v + k := by
  by_contra hlt
  exact degree_dichotomy S.crit S.cm S.db (by rw [S.da]; exact S.k2) hva
    (by
      have : ¬ (G.degree v + G.maxDegree + 6 ≤ Fintype.card V + 2 * k) := fun h => hns ⟨hva, h⟩
      rw [S.da]; omega) (by rw [S.da]; omega)

theorem not_small_of_big {v : V} (h : G.maxDegree + 1 ≤ G.degree v + k) : ¬ Small G a k v :=
  fun hs => by have := S.small_deg hs; omega

theorem nbr_big {t s : V} (h : Small G a k t) (hst : G.Adj s t) :
    s ≠ a ∧ G.maxDegree + 1 ≤ G.degree s + k := by
  have e1 := deg_add S.crit hst
  have e2 := S.small_deg h
  have e3 := S.hcond
  have e4 := h.2
  have hsa : s ≠ a := by
    rintro rfl
    rw [S.da] at e1
    omega
  refine ⟨hsa, S.big_of_not_small hsa fun hs => ?_⟩
  have := hs.2
  omega

theorem no_good_b {t : V} (h : Small G a k t) : ¬ Good c a b b t := by
  rintro ⟨δ, hδ, hA⟩
  obtain ⟨hfa, hfb⟩ := fan_bau S.crit.2.1 S.cm hδ (S.free_a_of_good_b hδ hA) (Ne.symm h.1)
  obtain ⟨θ₁, -, -, h₁, -, hv₁, -⟩ := S.two_inA h
  rcases h₁ with h | h
  · exact hfa θ₁ h hv₁
  · exact hfb θ₁ h hv₁

theorem no_good_cc {t : V} (h : Small G a k t) : ¬ Good c a b cc t := by
  rintro ⟨γ, hγ, hA⟩
  have hK : IsK4 c b a cc t β γ :=
    ⟨S.cm.symm, S.acc, hγ, S.βb, Or.comm.1 hA, S.cc_ne_b.symm, (S.small_ne_b h).symm,
      (Ne.symm h.1)⟩
  obtain ⟨θ₁, θ₂, hne, h₁, h₂, hv₁, hv₂⟩ := S.two_inA h
  exact hK.not_two_common S.crit.2.1 hne (Or.comm.1 h₁) (Or.comm.1 h₂) hv₁ hv₂

theorem cc_not_small : ¬ Small G a k cc := by
  intro hs
  have := S.small_deg hs
  have := S.cc_deg
  omega

theorem ne_of_good {t s : V} (h : Small G a k t) (hg : Good c a b s t) : s ≠ b ∧ s ≠ cc := by
  refine ⟨?_, ?_⟩ <;> rintro rfl
  · exact S.no_good_b h hg
  · exact S.no_good_cc h hg

/-- A small vertex has two neighbours joined to it by edges coloured in `A`. -/
theorem two_good_nbrs {t : V} (h : Small G a k t) :
    ∃ s s', s ≠ s' ∧ Good c a b s t ∧ Good c a b s' t := by
  classical
  have hbad := card_badNbrs_le (c := c) (a := a) (b := b) t
  have hk := S.nonA_eq
  have hd := S.hmin t
  have hsub : G.neighborFinset t ⊆ ((G.neighborFinset t) \ badNbrs c a b t) ∪ badNbrs c a b t := by
    intro w hw
    by_cases hb : w ∈ badNbrs c a b t
    · exact mem_union_right _ hb
    · exact mem_union_left _ (mem_sdiff.2 ⟨hw, hb⟩)
  have := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_neighborFinset_eq_degree] at this
  obtain ⟨s, hs, s', hs', hne⟩ := one_lt_card.1
    (show 1 < #((G.neighborFinset t) \ badNbrs c a b t) by omega)
  have hgood : ∀ {w}, w ∈ (G.neighborFinset t) \ badNbrs c a b t → Good c a b w t := by
    intro w hw
    rw [mem_sdiff, mem_neighborFinset] at hw
    rw [good_symm]
    by_contra hn
    exact hw.2 (not_good_mem_bad S.cm hw.1 (sym2_ne_ab ⟨h.1, S.small_ne_b h⟩) hn)
  exact ⟨s, s', hne, hgood hs, hgood hs'⟩

/-- The four-centre count with centres `s₁, s₂, b, cc`. -/
theorem count4 {s₁ s₂ : V} (hne : s₁ ≠ s₂) (h₁ : s₁ ≠ a ∧ G.maxDegree + 1 ≤ G.degree s₁ + k)
    (h₂ : s₂ ≠ a ∧ G.maxDegree + 1 ≤ G.degree s₂ + k) (h₁b : s₁ ≠ b ∧ s₁ ≠ cc)
    (h₂b : s₂ ≠ b ∧ s₂ ≠ cc) :
    ∃ u, u ≠ a ∧ u ≠ s₁ ∧ u ≠ s₂ ∧ u ≠ b ∧ u ≠ cc ∧
      Good c a b s₁ u ∧ Good c a b s₂ u ∧ Good c a b b u ∧ Good c a b cc u := by
  have hk := S.nonA_eq
  have hc := S.cc_deg
  have hb := S.db
  have hh := S.hcond
  obtain ⟨u, hua, hu1, hu2, hu3, hu4, -, -, -, -, g1, g2, g3, g4⟩ :=
    exists_good_common₄ S.cm hne h₁b.1 h₁b.2 h₂b.1 h₂b.2 S.cc_ne_b.symm h₁.1 h₂.1
      S.cm.adj.ne.symm S.cc_ne_a (by omega)
  exact ⟨u, hua, hu1, hu2, hu3, hu4, g1, g2, g3, g4⟩

open Classical in
/-- Robustly, at least seven colours missing at `a` are missing at both of two small vertices. -/
theorem robust {t₁ t₂ : V} (h₁ : Small G a k t₁) (h₂ : Small G a k t₂)
    (hΔ : k + 2 ≤ G.maxDegree) : Robust G a b t₁ t₂ := by
  classical
  intro ψ hψ T hT
  set F := univ.filter fun θ => ψ.IsFree a θ ∧ ψ.IsFree t₁ θ ∧ ψ.IsFree t₂ θ with hF
  have m₁ := hψ.card_missing_other h₁.1 (S.small_ne_b h₁)
  have m₂ := hψ.card_missing_other h₂.1 (S.small_ne_b h₂)
  have mb := hψ.card_missing_end (Or.inr rfl)
  have hk : #(nonA ψ a b) + 2 = k := by rw [← S.da]; exact hψ.card_nonA_eq S.crit.2.1 S.db
  have e1 := h₁.2
  have e2 := h₂.2
  have hh := S.hcond
  have db := S.db
  have hsub : missing ψ t₁ ∩ missing ψ t₂ ⊆ (F ∪ nonA ψ a b) ∪ missing ψ b := by
    intro θ hθ
    rw [mem_inter, mem_missing, mem_missing] at hθ
    by_cases ha : ψ.IsFree a θ
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨mem_univ _, ha, hθ⟩))
    by_cases hb : ψ.IsFree b θ
    · exact mem_union_right _ (mem_missing.2 hb)
    · exact mem_union_left _ (mem_union_right _ (mem_nonA.2 fun h => h.elim ha hb))
  have i1 := card_union_add_card_inter (missing ψ t₁) (missing ψ t₂)
  have i2 := card_le_univ (missing ψ t₁ ∪ missing ψ t₂)
  rw [Fintype.card_fin] at i2
  have i3 := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  have hlt : #T < #F := by omega
  obtain ⟨θ, hθF, hθT⟩ := exists_mem_notMem_of_card_lt_card hlt
  rw [hF, mem_filter] at hθF
  exact ⟨θ, hθT, hθF.2⟩

/-- Two small vertices cannot be joined to distinct neighbours by edges of the same colour of `A`
(otherwise a kite contradicts `KiteProp`). -/
theorem kite_contra (hK : KiteProp G) {t t' : V} (ht : Small G a k t) (ht' : Small G a k t')
    (htt : t ≠ t') {s s' : V} (hg : Good c a b s t) (hcol : c.col t' s' = c.col t s) : False := by
  have hcol' : c.col s t = c.col s' t' := by rw [c.col_symm s t, ← hcol, c.col_symm]
  have hg' : Good c a b s' t' := by obtain ⟨γ, hγ, hA⟩ := hg; exact ⟨γ, hcol' ▸ hγ, hA⟩
  have hss : s ≠ s' := by
    rintro rfl
    obtain ⟨γ, hγ, -⟩ := hg
    exact htt (c.col_proper hγ (hcol' ▸ hγ))
  have hs := S.nbr_big ht hg.adj
  have hs' := S.nbr_big ht' hg'.adj
  obtain ⟨u, hua, hus, hus', hub, hucc, gs, gs', gb, gcc⟩ :=
    S.count4 hss hs hs' (S.ne_of_good ht hg) (S.ne_of_good ht' hg')
  have hut : u ≠ t := by rintro rfl; exact S.no_good_b ht gb
  have hut' : u ≠ t' := by rintro rfl; exact S.no_good_b ht' gb
  have hst' : s ≠ t' := by rintro rfl; exact S.not_small_of_big hs.2 ht'
  have hs't : s' ≠ t := by rintro rfl; exact S.not_small_of_big hs'.2 ht
  have hcct : cc ≠ t := by rintro rfl; exact S.cc_not_small ht
  have hcct' : cc ≠ t' := by rintro rfl; exact S.cc_not_small ht'
  obtain ⟨δ, hδ, hδA⟩ := gb
  refine hK c a b cc u s s' t t' ?_ S.cm ⟨δ, hδ, S.free_a_of_good_b hδ hδA⟩ (good_symm.1 gs) hg
    ⟨β, S.acc, S.βb⟩ gcc (good_symm.1 gs') hg' hcol' S.db (S.robust ht ht' (by
      have := S.small_deg ht
      have := two_le_degree S.crit hg.adj
      omega))
  have hab := S.cm.adj.ne
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or]
  exact ⟨⟨hab, S.cc_ne_a.symm, hua.symm, hs.1.symm, hs'.1.symm, ht.1.symm, ht'.1.symm⟩,
    ⟨S.cc_ne_b.symm, hub.symm, (S.ne_of_good ht hg).1.symm, (S.ne_of_good ht' hg').1.symm,
      (S.small_ne_b ht).symm, (S.small_ne_b ht').symm⟩,
    ⟨hucc.symm, (S.ne_of_good ht hg).2.symm, (S.ne_of_good ht' hg').2.symm, hcct, hcct'⟩,
    ⟨hus, hus', hut, hut'⟩, ⟨hss, hg.adj.ne, hst'⟩, ⟨hs't, hg'.adj.ne⟩, htt, not_false⟩

/-- **Case 1.** Two small vertices are impossible. -/
theorem case1 (hK : KiteProp G) {t₁ t₂ : V} (h₁ : Small G a k t₁) (h₂ : Small G a k t₂)
    (htt : t₁ ≠ t₂) : False := by
  obtain ⟨s₁, -, -, hg₁, -⟩ := S.two_good_nbrs h₁
  obtain ⟨p, q, hpq, hgp, hgq⟩ := S.two_good_nbrs h₂
  obtain ⟨s₂, hs₂, hg₂⟩ : ∃ s₂, s₂ ≠ s₁ ∧ Good c a b s₂ t₂ := by
    by_cases hp : p = s₁
    · exact ⟨q, fun e => hpq (hp.trans e.symm), hgq⟩
    · exact ⟨p, hp, hgp⟩
  obtain ⟨γ₁, hγ₁, hA₁⟩ := hg₁
  obtain ⟨γ₂, hγ₂, hA₂⟩ := hg₂
  have hγ₁t₂ : c.IsFree t₂ γ₁ := by
    intro w hw
    refine S.kite_contra hK h₁ h₂ htt (s' := w) ⟨γ₁, hγ₁, hA₁⟩ ?_
    rw [hw, c.col_symm, hγ₁]
  have hγ₂t₁ : c.IsFree t₁ γ₂ := by
    intro w hw
    refine S.kite_contra hK h₂ h₁ htt.symm (s' := w) ⟨γ₂, hγ₂, hA₂⟩ ?_
    rw [hw, c.col_symm, hγ₂]
  have hs₁ := S.nbr_big h₁ (c.col_adj hγ₁)
  have hs₂' := S.nbr_big h₂ (c.col_adj hγ₂)
  have hn₁ := S.ne_of_good h₁ ⟨γ₁, hγ₁, hA₁⟩
  have hn₂ := S.ne_of_good h₂ ⟨γ₂, hγ₂, hA₂⟩
  obtain ⟨u, hua, hu1, hu2, hub, -, gs₁, gs₂, ⟨δ, hδ, hδA⟩, -⟩ :=
    S.count4 hs₂.symm hs₁ hs₂' hn₁ hn₂
  obtain ⟨β₁, hβ₁, hβ₁A⟩ := gs₁
  obtain ⟨β₂, hβ₂, hβ₂A⟩ := gs₂
  have hut₁ : u ≠ t₁ := by rintro rfl; exact S.no_good_b h₁ ⟨δ, hδ, hδA⟩
  have hut₂ : u ≠ t₂ := by rintro rfl; exact S.no_good_b h₂ ⟨δ, hδ, hδA⟩
  have hs₁t₂ : s₁ ≠ t₂ := by rintro rfl; exact S.not_small_of_big hs₁.2 h₂
  have hs₂t₁ : s₂ ≠ t₁ := by rintro rfl; exact S.not_small_of_big hs₂'.2 h₁
  have hd : Distinct7 a b u s₁ s₂ t₁ t₂ :=
    ⟨S.cm.adj.ne, hua.symm, hs₁.1.symm, hs₂'.1.symm, h₁.1.symm, h₂.1.symm, hub.symm,
      hn₁.1.symm, hn₂.1.symm, (S.small_ne_b h₁).symm, (S.small_ne_b h₂).symm, hu1, hu2,
      hut₁, hut₂, hs₂.symm, (c.col_adj hγ₁).ne, hs₁t₂, hs₂t₁, (c.col_adj hγ₂).ne, htt⟩
  have hF : IsFork c a b u s₁ s₂ t₁ t₂ δ β₁ β₂ γ₁ γ₂ :=
    ⟨S.cm, hδ, by rw [c.col_symm]; exact hβ₁, by rw [c.col_symm]; exact hβ₂, hγ₁, hγ₂,
      S.free_a_of_good_b hδ hδA, hβ₁A, hβ₂A, hA₁, hA₂, hγ₁t₂, hγ₂t₁⟩
  refine fork_lemma S.crit hd ?_ c δ β₁ β₂ γ₁ γ₂ hF
  have := S.hcond
  have := h₁.2
  have := h₂.2
  rw [S.da]
  omega

end MainSetup

end Overfull
