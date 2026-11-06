/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.KiteB

/-!
# Kites, part C: the normal form is impossible

`KNF`: `φ̄(b) ∋ β`, `φ(a cc) = β`, `φ(bu) = α`, `φ(cc u) = τ`, `φ(us₁) = β`, `φ(us₂) = δ`,
`φ(s₁t₁) = φ(s₂t₂) = γ` with `α, τ, δ, γ ∈ φ̄(a)`; `t₁, t₂` miss `α, β, τ`, and `t₂` misses `δ`.

By `x_reach`, after uncolouring `bu` the `(α, γ)`-chain of `t₁` reaches `u`.
* If `u` is not on the `a`–`b` `(β, δ)`-chain, swap the `(β, δ)`-chain of `u`; now `x_reach` for
  `t₂` makes `t₁, t₂, u` three ends of one `(α, γ)`-chain.
* Otherwise, after uncolouring `us₂`, `u` reaches `a` (then `y_close`) or `b`; in the latter case
  colour `ab` by `β` and uncolour `a cc`: in that colouring `u` reaches `a`, and `y_close` applies
  with `cc` in the role of `b`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The normal form of a kite. -/
structure KNF (c : PEC G (Fin G.maxDegree)) (a b cc u s₁ s₂ t₁ t₂ : V)
    (α β τ δ γ : Fin G.maxDegree) : Prop where
  d7 : Distinct7 a b u s₁ s₂ t₁ t₂
  acc' : a ≠ cc
  bcc : b ≠ cc
  ccu : cc ≠ u
  ccs₁ : cc ≠ s₁
  ccs₂ : cc ≠ s₂
  cct₁ : cc ≠ t₁
  cct₂ : cc ≠ t₂
  cm : IsColMinus c a b
  βb : c.IsFree b β
  acc : c.col a cc = some β
  hbu : c.col b u = some α
  αa : c.IsFree a α
  hcu : c.col cc u = some τ
  τa : c.IsFree a τ
  hus₁ : c.col u s₁ = some β
  hus₂ : c.col u s₂ = some δ
  δa : c.IsFree a δ
  hst₁ : c.col s₁ t₁ = some γ
  hst₂ : c.col s₂ t₂ = some γ
  γa : c.IsFree a γ
  α₁ : c.IsFree t₁ α
  α₂ : c.IsFree t₂ α
  β₁ : c.IsFree t₁ β
  β₂ : c.IsFree t₂ β
  τ₁ : c.IsFree t₁ τ
  τ₂ : c.IsFree t₂ τ
  δ₂ : c.IsFree t₂ δ

set_option maxHeartbeats 1600000 in
/-- **The normal form of a kite is impossible.** -/
theorem KNF.false (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b cc u s₁ s₂ t₁ t₂ : V}
    {α β τ δ γ : Fin G.maxDegree} (h : KNF c a b cc u s₁ s₂ t₁ t₂ α β τ δ γ) : False := by
  have d := h.d7
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have hαβ : α ≠ β := fun e => hdis α h.αa (e ▸ h.βb)
  have hγβ : γ ≠ β := fun e => hdis γ h.γa (e ▸ h.βb)
  have hδβ : δ ≠ β := fun e => hdis δ h.δa (e ▸ h.βb)
  have hαδ : α ≠ δ := fun e =>
    d.bs₂ (c.col_proper (by rw [c.col_symm]; exact h.hbu) (e ▸ h.hus₂))
  have hδγ : δ ≠ γ := fun e => d.ut₂ (c.col_proper (by rw [c.col_symm]; exact h.hus₂)
    (by rw [e]; exact h.hst₂))
  have hX := x_reach hG d.ab d.au d.as₁ d.at₁ d.bu d.bs₁ d.bt₁ d.us₁ d.ut₁ d.s₁t₁ h.cm h.βb
    h.hbu h.αa h.hus₁ h.hst₁ h.γa h.α₁ h.β₁
  have hab : (c.kempeGraph β δ).Reachable a b := by
    rw [kempeGraph_comm]; exact ksAB_link hG h.cm h.δa h.βb
  by_cases hua : (c.kempeGraph β δ).Reachable u a
  · -- `u` lies on the `a`–`b` chain
    set φ' := unsetEdge c u s₂ with hφ'
    have hsub : ∀ x y, (c.kempeGraph β δ).Adj x y →
        (φ'.kempeGraph β δ).Adj x y ∨ s(x, y) = s(u, s₂) := by
      rintro x y ⟨hne, hc⟩
      by_cases e : (x = u ∧ y = s₂) ∨ (x = s₂ ∧ y = u)
      · right
        rcases e with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy]
        exact Sym2.eq_swap
      · left; exact ⟨hne, by rw [hφ', unsetEdge_col_of_ne c e]; exact hc⟩
    have fa : φ'.IsFree a δ := (isFree_unsetEdge_of_ne c d.au d.as₂ δ).2 h.δa
    have fb : φ'.IsFree b β := (isFree_unsetEdge_of_ne c d.bu d.bs₂ β).2 h.βb
    have fs : φ'.IsFree s₂ δ := (isFree_unsetEdge_right c d.us₂ h.hus₂ δ).2 (Or.inl rfl)
    rcases reach_split hsub hua with r | r
    · exact y_close hG d h.cm h.βb h.hbu h.αa h.hus₂ h.δa h.hst₁ h.hst₂ h.γa h.α₁ h.α₂ h.β₂ h.δ₂
        hX r
    rcases reach_split hsub (hua.trans hab) with r' | r'
    swap
    · exact not_three_linked φ' d.as₂.symm d.bs₂.symm d.ab (Or.inr fs) (Or.inr fa) (Or.inl fb) r r'
    -- the `cc`-version: colour `ab` by `β`, uncolour `a cc`
    obtain ⟨ψ, hcmψ, hψba, hoff, hψa, hψcc, hψw⟩ := exists_shift h.cm.symm h.acc h.βb h.bcc
    have off' : ∀ p q, p ≠ a → q ≠ a → ψ.col p q = c.col p q := fun p q hp hq =>
      hoff p q (not_pair (Or.inr hq) (Or.inl hp)) (not_pair (Or.inl hp) (Or.inr hq))
    have fw : ∀ {w}, w ≠ b → w ≠ a → w ≠ cc → ∀ μ, c.IsFree w μ → ψ.IsFree w μ :=
      fun h1 h2 h3 μ hμ => (hψw _ h1 h2 h3 μ).2 hμ
    have d' : Distinct7 a cc u s₁ s₂ t₁ t₂ :=
      ⟨h.acc', d.au, d.as₁, d.as₂, d.at₁, d.at₂, h.ccu, h.ccs₁, h.ccs₂, h.cct₁, h.cct₂, d.us₁,
        d.us₂, d.ut₁, d.ut₂, d.s₁s₂, d.s₁t₁, d.s₁t₂, d.s₂t₁, d.s₂t₂, d.t₁t₂⟩
    have hcu' : ψ.col cc u = some τ := by rw [off' cc u h.acc'.symm d.au.symm]; exact h.hcu
    have hus₁' : ψ.col u s₁ = some β := by rw [off' u s₁ d.au.symm d.as₁.symm]; exact h.hus₁
    have hus₂' : ψ.col u s₂ = some δ := by rw [off' u s₂ d.au.symm d.as₂.symm]; exact h.hus₂
    have hst₁' : ψ.col s₁ t₁ = some γ := by rw [off' s₁ t₁ d.as₁.symm d.at₁.symm]; exact h.hst₁
    have hst₂' : ψ.col s₂ t₂ = some γ := by rw [off' s₂ t₂ d.as₂.symm d.at₂.symm]; exact h.hst₂
    have hX' := x_reach hG d'.ab d'.au d'.as₁ d'.at₁ d'.bu d'.bs₁ d'.bt₁ d'.us₁ d'.ut₁ d'.s₁t₁
      hcmψ.symm hψcc hcu' ((hψa τ).2 h.τa) hus₁' hst₁' ((hψa γ).2 h.γa)
      (fw d.bt₁.symm d.at₁.symm h.cct₁.symm τ h.τ₁) (fw d.bt₁.symm d.at₁.symm h.cct₁.symm β h.β₁)
    -- in the new colouring, after uncolouring `us₂`, `u` reaches `a`
    set φ₀ := unsetEdge φ' a cc with hφ₀
    have c0 : ∀ p q, ¬ ((p = a ∧ q = cc) ∨ (p = cc ∧ q = a)) →
        ¬ ((p = u ∧ q = s₂) ∨ (p = s₂ ∧ q = u)) → φ₀.col p q = c.col p q := fun p q e1 e2 => by
      rw [hφ₀, unsetEdge_col_of_ne φ' e1, hφ', unsetEdge_col_of_ne c e2]
    have hiso : ∀ q, ¬ (φ₀.kempeGraph β δ).Adj a q := by
      rintro q ⟨-, hc⟩
      by_cases hq : q = cc
      · rw [hq, hφ₀, unsetEdge_col_self] at hc
        rcases hc with hc | hc <;> cases hc
      rw [c0 a q (not_pair (Or.inr hq) (Or.inl h.acc')) (not_pair (Or.inl d.au) (Or.inl d.as₂))]
        at hc
      rcases hc with hc | hc
      · exact hq (c.col_proper hc h.acc)
      · exact h.δa q hc
    have g0 : (φ₀.kempeGraph β δ).Reachable u b := by
      refine reach_of_pendant (a := a) (w := cc) (fun p q hpq => ?_) hiso h.acc'.symm d.au.symm
        d.ab.symm r'
      by_cases e : (p = a ∧ q = cc) ∨ (p = cc ∧ q = a)
      · right
        rcases e with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rw [hp, hq]
        exact Sym2.eq_swap
      left
      obtain ⟨hne, hc⟩ := hpq
      exact ⟨hne, by rw [hφ₀, unsetEdge_col_of_ne φ' e]; exact hc⟩
    set ψ' := unsetEdge ψ u s₂ with hψ'
    have g1 : (ψ'.kempeGraph β δ).Reachable u b := by
      refine reachable_mono_of_agree (fun x y hxy => ?_) g0
      by_cases e1 : (x = a ∧ y = cc) ∨ (x = cc ∧ y = a)
      · exfalso
        have : φ₀.col x y = none := by
          rcases e1 with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy]
          · exact unsetEdge_col_self φ' a cc
          · rw [PEC.col_symm]; exact unsetEdge_col_self φ' a cc
        rw [this] at hxy
        rcases hxy with e | e <;> cases e
      by_cases e2 : (x = u ∧ y = s₂) ∨ (x = s₂ ∧ y = u)
      · exfalso
        have : φ₀.col x y = none := by
          rw [hφ₀, unsetEdge_col_of_ne φ' e1]
          rcases e2 with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy]
          · exact unsetEdge_col_self c u s₂
          · rw [PEC.col_symm]; exact unsetEdge_col_self c u s₂
        rw [this] at hxy
        rcases hxy with e | e <;> cases e
      by_cases e3 : (x = b ∧ y = a) ∨ (x = a ∧ y = b)
      · exfalso
        have : φ₀.col x y = none := by
          rw [c0 x y e1 e2]
          rcases e3 with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy]
          · rw [c.col_symm]; exact h.cm.uncol
          · exact h.cm.uncol
        rw [this] at hxy
        rcases hxy with e | e <;> cases e
      rw [hψ', unsetEdge_col_of_ne ψ e2, hoff x y e3 e1, c0 x y e1 e2]
    have hψba' : ψ'.col b a = some β := by
      rw [hψ', unsetEdge_col_of_ne ψ (not_pair (Or.inl d.bu) (Or.inl d.bs₂))]; exact hψba
    have hU' : (ψ'.kempeGraph β δ).Reachable u a := reachable_of_col g1 (Or.inl hψba')
    exact y_close hG d' hcmψ.symm hψcc hcu' ((hψa τ).2 h.τa) hus₂' ((hψa δ).2 h.δa) hst₁' hst₂'
      ((hψa γ).2 h.γa) (fw d.bt₁.symm d.at₁.symm h.cct₁.symm τ h.τ₁)
      (fw d.bt₂.symm d.at₂.symm h.cct₂.symm τ h.τ₂) (fw d.bt₂.symm d.at₂.symm h.cct₂.symm β h.β₂)
      (fw d.bt₂.symm d.at₂.symm h.cct₂.symm δ h.δ₂) hX' hU'
  · -- `u` is off the `a`–`b` chain: swap the `(β, δ)`-chain of `u`
    have hnb : ¬ (c.kempeGraph β δ).Reachable u b := fun r => hua (r.trans hab.symm)
    have hnt : ¬ (c.kempeGraph β δ).Reachable u t₂ := fun r =>
      d.ut₂ (eq_of_reachable_of_free_both c h.β₂ h.δ₂ r.symm)
    set c' := c.kempeSwap β δ u with hc'
    have hX2 := x_reach hG d.ab d.au d.as₂ d.at₂ d.bu d.bs₂ d.bt₂ d.us₂ d.ut₂ d.s₂t₂
      (h.cm.kempeSwap β δ u) ((kfree_off c hnb β).2 h.βb)
      (kcol_keep c h.hbu (Or.inl ⟨hαβ, hαδ⟩)) ((kfree_of_ne c hαβ hαδ).2 h.αa)
      (kcol_flip₂ c h.hus₂ (Reachable.refl u)) (kcol_keep c h.hst₂ (Or.inl ⟨hγβ, hδγ.symm⟩))
      ((kfree_of_ne c hγβ hδγ.symm).2 h.γa) ((kfree_of_ne c hαβ hαδ).2 h.α₂)
      ((kfree_off c hnt β).2 h.β₂)
    have hX2' : ((unsetEdge c b u).kempeGraph α γ).Reachable t₂ u := by
      refine reachable_mono_of_agree (fun x y hxy => ?_) hX2
      by_cases e : (x = b ∧ y = u) ∨ (x = u ∧ y = b)
      · exfalso
        have : (unsetEdge c' b u).col x y = none := by
          rcases e with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy]
          · exact unsetEdge_col_self c' b u
          · rw [PEC.col_symm]; exact unsetEdge_col_self c' b u
        rw [this] at hxy
        rcases hxy with e | e <;> cases e
      rw [unsetEdge_col_of_ne c' e] at hxy ⊢
      rw [unsetEdge_col_of_ne c e]
      rcases hxy with e' | e'
      · rw [e']; rw [hc', kcol_eq_iff_of_ne c u x y hαβ hαδ] at e'; exact e'
      · rw [e']; rw [hc', kcol_eq_iff_of_ne c u x y hγβ hδγ.symm] at e'; exact e'
    have fu : (unsetEdge c b u).IsFree u α := (isFree_unsetEdge_right c d.bu h.hbu α).2 (Or.inl rfl)
    have f1 : (unsetEdge c b u).IsFree t₁ α :=
      (isFree_unsetEdge_of_ne c d.bt₁.symm d.ut₁.symm α).2 h.α₁
    have f2 : (unsetEdge c b u).IsFree t₂ α :=
      (isFree_unsetEdge_of_ne c d.bt₂.symm d.ut₂.symm α).2 h.α₂
    exact not_three_linked (unsetEdge c b u) d.ut₁ d.ut₂ d.t₁t₂ (Or.inl fu) (Or.inl f1) (Or.inl f2)
      hX.symm hX2'.symm

end Overfull
