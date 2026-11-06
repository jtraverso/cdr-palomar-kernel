/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Theorem12c

/-!
# CCJS Theorem 1.2 from the kite lemmas

`overfull_of_kites`: a `Δ`-critical graph `G` of order `n` with `3n + 7δ(G) ≤ 4Δ(G) + 10` is
overfull, given `KiteProp G` and `ShortKiteProp G`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace MainSetup

variable {c : PEC G (Fin G.maxDegree)} {a b cc : V} {k : ℕ} {β : Fin G.maxDegree}
  (S : MainSetup G c a b cc k β)
include S

/-- **Case 2.** At most one small vertex and `G` not overfull is impossible. -/
theorem case2 (hSK : ShortKiteProp G)
    (huniq : ∀ t t', Small G a k t → Small G a k t' → t = t') (hnot : ¬ IsOverfull G) : False := by
  classical
  obtain ⟨hdis, -⟩ := S.cm.ab_facts S.crit.2.1
  by_cases he : Even (Fintype.card V)
  · obtain ⟨t, hta, htb, hns⟩ : ∃ t, t ≠ a ∧ t ≠ b ∧ ∀ v, v ≠ t → ¬ Small G a k v := by
      by_cases hs : ∃ t₀, Small G a k t₀
      · obtain ⟨t₀, ht₀⟩ := hs
        exact ⟨t₀, ht₀.1, S.small_ne_b ht₀, fun v hv hsv => hv (huniq v t₀ hsv ht₀)⟩
      · exact ⟨cc, S.cc_ne_a, S.cc_ne_b, fun v _ hsv => hs ⟨v, hsv⟩⟩
    obtain ⟨α₁, α₂, hne, hA₁, hA₂, hn₁, hn₂⟩ := S.two_not_free hta htb
    obtain ⟨x, hxa, hxb, hxt, hx⟩ := S.other_vertex hA₁ (Or.inl ⟨he, hn₁⟩) hta htb
    obtain ⟨y, hya, hyb, hyt, hy⟩ := S.other_vertex hA₂ (Or.inl ⟨he, hn₂⟩) hta htb
    have bx := S.big_of_not_small hxa (hns x hxt)
    have byy := S.big_of_not_small hya (hns y hyt)
    have hxy : x ≠ y := by
      rintro rfl
      exact S.ne_of_two hxa hxb bx hne hA₁ hA₂ hx hy
    exact S.core hSK hxy hxa hxb hya hyb bx byy (S.lt_max_of_free hxa hxb hx)
      (S.lt_max_of_free hya hyb hy) ⟨α₁, hA₁, hx⟩ ⟨α₂, hA₂, hy⟩
  have ho : Odd (Fintype.card V) := Nat.not_even_iff_odd.1 he
  by_cases hs : ∃ t, Small G a k t
  · obtain ⟨t, ht⟩ := hs
    obtain ⟨θ₁, θ₂, hne, hA₁, hA₂, ht₁, ht₂⟩ := S.two_inA ht
    obtain ⟨x, hxa, hxb, hxt, hx⟩ :=
      S.other_vertex hA₁ (Or.inr ⟨ho, ht₁⟩) ht.1 (S.small_ne_b ht)
    obtain ⟨y, hya, hyb, hyt, hy⟩ :=
      S.other_vertex hA₂ (Or.inr ⟨ho, ht₂⟩) ht.1 (S.small_ne_b ht)
    have bx := S.big_of_not_small hxa fun hsx => hxt (huniq x t hsx ht)
    have byy := S.big_of_not_small hya fun hsy => hyt (huniq y t hsy ht)
    have hxy : x ≠ y := by
      rintro rfl
      exact S.ne_of_two hxa hxb bx hne hA₁ hA₂ hx hy
    exact S.core hSK hxy hxa hxb hya hyb bx byy (S.lt_max_of_free hxa hxb hx)
      (S.lt_max_of_free hya hyb hy) ⟨θ₁, hA₁, hx⟩ ⟨θ₂, hA₂, hy⟩
  have big : ∀ {v}, v ≠ a → G.maxDegree + 1 ≤ G.degree v + k := fun hva =>
    S.big_of_not_small hva fun hsv => hs ⟨_, hsv⟩
  obtain ⟨θ₀, h3⟩ := exists_colour_missing_three S.cm ho hnot
  obtain ⟨u₁, u₂, u₃, h1, h2, h3', h12, h13, h23⟩ := two_lt_card_iff.1 h3
  simp only [mem_filter, mem_univ, true_and] at h1 h2 h3'
  by_cases hA : InA c a b θ₀
  · have key : ∀ {p q}, p ≠ q → c.IsFree p θ₀ → c.IsFree q θ₀ → (p = a ∨ p = b) →
        (q = a ∨ q = b) → False := by
      intro p q hpq hp hq hpab hqab
      rcases hpab with rfl | rfl <;> rcases hqab with rfl | rfl
      · exact hpq rfl
      · exact hdis θ₀ hp hq
      · exact hdis θ₀ hq hp
      · exact hpq rfl
    obtain ⟨x, y, hxy, hx, hy, hxab, hyab⟩ : ∃ x y, x ≠ y ∧ c.IsFree x θ₀ ∧ c.IsFree y θ₀ ∧
        ¬ (x = a ∨ x = b) ∧ ¬ (y = a ∨ y = b) := by
      by_cases e1 : u₁ = a ∨ u₁ = b
      · exact ⟨u₂, u₃, h23, h2, h3', fun e2 => key h12 h1 h2 e1 e2,
          fun e3 => key h13 h1 h3' e1 e3⟩
      by_cases e2 : u₂ = a ∨ u₂ = b
      · exact ⟨u₁, u₃, h13, h1, h3', e1, fun e3 => key h23 h2 h3' e2 e3⟩
      · exact ⟨u₁, u₂, h12, h1, h2, e1, e2⟩
    rw [not_or] at hxab hyab
    exact S.core hSK hxy hxab.1 hxab.2 hyab.1 hyab.2 (big hxab.1) (big hyab.1)
      (S.lt_max_of_free hxab.1 hxab.2 hx) (S.lt_max_of_free hyab.1 hyab.2 hy) ⟨θ₀, hA, hx⟩
      ⟨θ₀, hA, hy⟩
  -- `θ₀ ∉ A`: move a colour of `φ̄(a)` to two of the `uᵢ`
  have hnab : ∀ {v}, c.IsFree v θ₀ → v ≠ a ∧ v ≠ b := fun hv =>
    ⟨fun e => hA (Or.inl (e ▸ hv)), fun e => hA (Or.inr (e ▸ hv))⟩
  obtain ⟨α, hα⟩ : ∃ α, c.IsFree a α := by
    have := S.cm.card_missing_end (Or.inl rfl)
    rw [S.da] at this
    have := S.kΔ
    obtain ⟨α, hα⟩ := card_pos.1 (show 0 < #(missing c a) by omega)
    exact ⟨α, mem_missing.1 hα⟩
  have hbα : ¬ c.IsFree b α := hdis α hα
  have hbθ : ¬ c.IsFree b θ₀ := fun h => hA (Or.inr h)
  have hone : ∀ {p q}, p ≠ q → c.IsFree p θ₀ → c.IsFree q θ₀ →
      (c.kempeGraph α θ₀).Reachable a p → (c.kempeGraph α θ₀).Reachable a q → False :=
    fun hpq hp hq rp rq => not_three_linked c (hnab hp).1.symm (hnab hq).1.symm hpq (Or.inl hα)
      (Or.inr hp) (Or.inr hq) rp rq
  obtain ⟨x, y, hxy, hx, hy, rx, ry⟩ : ∃ x y, x ≠ y ∧ c.IsFree x θ₀ ∧ c.IsFree y θ₀ ∧
      ¬ (c.kempeGraph α θ₀).Reachable a x ∧ ¬ (c.kempeGraph α θ₀).Reachable a y := by
    by_cases r1 : (c.kempeGraph α θ₀).Reachable a u₁
    · exact ⟨u₂, u₃, h23, h2, h3', fun r => hone h12 h1 h2 r1 r, fun r => hone h13 h1 h3' r1 r⟩
    by_cases r2 : (c.kempeGraph α θ₀).Reachable a u₂
    · exact ⟨u₁, u₃, h13, h1, h3', r1, fun r => hone h23 h2 h3' r2 r⟩
    · exact ⟨u₁, u₂, h12, h1, h2, r1, r2⟩
  obtain ⟨hxa, hxb⟩ := hnab hx
  obtain ⟨hya, hyb⟩ := hnab hy
  -- the new colouring
  obtain ⟨c', hcm', ha', hb', hx', hy'⟩ : ∃ c' : PEC G (Fin G.maxDegree), IsColMinus c' a b ∧
      (∀ ε, c'.IsFree a ε ↔ c.IsFree a ε) ∧ (∀ ε, c'.IsFree b ε ↔ c.IsFree b ε) ∧
      c'.IsFree x α ∧ c'.IsFree y α := by
    have hra : ¬ (c.kempeGraph α θ₀).Reachable x a := fun r => rx r.symm
    have hry : ¬ (c.kempeGraph α θ₀).Reachable y a := fun r => ry r.symm
    by_cases hxy' : (c.kempeGraph α θ₀).Reachable x y
    · exact ⟨c.kempeSwap α θ₀ x, S.cm.kempeSwap α θ₀ x, kfree_off c hra,
        isFree_kempeSwap_of_neither c α θ₀ x hbα hbθ, (kfree_flip₂ c (Reachable.refl x)).2 hx,
        (kfree_flip₂ c hxy').2 hy⟩
    · set c₁ := c.kempeSwap α θ₀ x with hc₁
      have hg : c₁.kempeGraph α θ₀ = c.kempeGraph α θ₀ := kempeGraph_kempeSwap_same c α θ₀ x
      have hya₁ : ¬ (c₁.kempeGraph α θ₀).Reachable y a := by rw [hg]; exact hry
      have hyx₁ : ¬ (c₁.kempeGraph α θ₀).Reachable y x := by
        rw [hg]; exact fun r => hxy' r.symm
      have hyx : ¬ (c.kempeGraph α θ₀).Reachable x y := hxy'
      have ha₁ := kfree_off c hra
      have hb₁ := isFree_kempeSwap_of_neither c α θ₀ x hbα hbθ
      have hbα₁ : ¬ c₁.IsFree b α := fun h => hbα ((hb₁ α).1 h)
      have hbθ₁ : ¬ c₁.IsFree b θ₀ := fun h => hbθ ((hb₁ θ₀).1 h)
      have hy₁ : c₁.IsFree y θ₀ := (kfree_off c hyx θ₀).2 hy
      refine ⟨c₁.kempeSwap α θ₀ y, (S.cm.kempeSwap α θ₀ x).kempeSwap α θ₀ y,
        fun ε => (kfree_off c₁ hya₁ ε).trans (ha₁ ε),
        fun ε => (isFree_kempeSwap_of_neither c₁ α θ₀ y hbα₁ hbθ₁ ε).trans (hb₁ ε), ?_,
        (kfree_flip₂ c₁ (Reachable.refl y)).2 hy₁⟩
      exact (kfree_off c₁ hyx₁ α).2 ((kfree_flip₂ c (Reachable.refl x)).2 hx)
  obtain ⟨cc', β', S'⟩ := MainSetup.of_colouring S.crit hcm' S.da S.hmin S.db S.hcond
  have hαA : InA c' a b α := Or.inl ((ha' α).2 hα)
  exact S'.core hSK hxy hxa hxb hya hyb (big hxa) (big hya) (S.lt_max_of_free hxa hxb hx)
    (S.lt_max_of_free hya hyb hy) ⟨α, hαA, hx'⟩ ⟨α, hαA, hy'⟩

end MainSetup

/-- A class-two graph has an edge. -/
theorem exists_adj_of_classTwo (h : IsClassTwo G) : ∃ x y, G.Adj x y := by
  by_contra hn
  push Not at hn
  have hE : ∀ e : G.edgeSet, False := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ x y => exact hn x y he
  exact h ⟨Coloring.mk (fun e => (hE e).elim) (fun {e₁ _} _ => (hE e₁).elim)⟩

/-- **CCJS Theorem 1.2 (variant), assuming the kite lemmas.** -/
theorem overfull_of_kites (hG : IsDeltaCritical G) (hK : KiteProp G) (hSK : ShortKiteProp G)
    (hcond : 3 * Fintype.card V + 7 * G.minDegree ≤ 4 * G.maxDegree + 10) : IsOverfull G := by
  by_contra hnot
  have : Nonempty V := hG.1.nonempty
  obtain ⟨a, ha⟩ := G.exists_minimal_degree_vertex
  obtain ⟨x, y, hxy⟩ := exists_adj_of_classTwo hG.2.1
  obtain ⟨w, haw⟩ : ∃ w, G.Adj a w := by
    by_cases hax : a = x
    · subst hax; exact ⟨y, hxy⟩
    obtain ⟨p⟩ := hG.1.preconnected a x
    cases p with
    | nil => exact absurd rfl hax
    | cons h _ => exact ⟨_, h⟩
  obtain ⟨b, hab, -, hdb⟩ := exists_maxdeg_nbr hG haw
  obtain ⟨c, hcm⟩ := exists_colMinus_of_colorable hab (hG.2.2 s(a, b) (G.mem_edgeSet.2 hab))
  obtain ⟨cc, β, S⟩ := MainSetup.of_colouring hG hcm ha.symm (fun v => G.minDegree_le_degree v)
    hdb hcond
  by_cases two : ∃ t₁ t₂, t₁ ≠ t₂ ∧ Small G a G.minDegree t₁ ∧ Small G a G.minDegree t₂
  · obtain ⟨t₁, t₂, htt, h₁, h₂⟩ := two
    exact S.case1 hK h₁ h₂ htt
  · refine S.case2 hSK (fun t t' ht ht' => ?_) hnot
    by_contra hne
    exact two ⟨t, t', hne, ht, ht'⟩

end Overfull
