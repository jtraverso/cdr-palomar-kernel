/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Kite0A

/-!
# Kites without `c`, part B: the normal form is impossible

`KNF0`: `φ̄(b) ∋ β`, `φ(bu) = α`, `φ(us₁) = β`, `φ(us₂) = δ`, `φ(s₁t₁) = φ(s₂t₂) = γ` with
`α, δ, γ ∈ φ̄(a)`, and `t₁, t₂` missing `α, β, δ`.

As for `KNF` (`KiteC`): by `x_reach` the `(α, γ)`-chain of `t₁` (after uncolouring `bu`) reaches
`u`; if `u` is off the `a`–`b` `(β, δ)`-chain, swapping it and `x_reach` for `t₂` give three ends of
one chain; otherwise, after uncolouring `us₂`, `u` reaches `a` (`y_close`) or `b` (`z_close`).
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The normal form of a kite without `c`. -/
structure KNF0 (c : PEC G (Fin G.maxDegree)) (a b u s₁ s₂ t₁ t₂ : V)
    (α β δ γ : Fin G.maxDegree) : Prop where
  d7 : Distinct7 a b u s₁ s₂ t₁ t₂
  cm : IsColMinus c a b
  βb : c.IsFree b β
  hbu : c.col b u = some α
  αa : c.IsFree a α
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
  δ₁ : c.IsFree t₁ δ
  δ₂ : c.IsFree t₂ δ

set_option maxHeartbeats 1600000 in
/-- **The normal form of a kite without `c` is impossible.** -/
theorem KNF0.false (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u s₁ s₂ t₁ t₂ : V}
    {α β δ γ : Fin G.maxDegree} (h : KNF0 c a b u s₁ s₂ t₁ t₂ α β δ γ) : False := by
  have d := h.d7
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have hαβ : α ≠ β := fun e => hdis α h.αa (e ▸ h.βb)
  have hγβ : γ ≠ β := fun e => hdis γ h.γa (e ▸ h.βb)
  have hαδ : α ≠ δ := fun e =>
    d.bs₂ (c.col_proper (by rw [c.col_symm]; exact h.hbu) (e ▸ h.hus₂))
  have hδγ : δ ≠ γ := fun e => d.ut₂ (c.col_proper (by rw [c.col_symm]; exact h.hus₂)
    (by rw [e]; exact h.hst₂))
  have hX := x_reach hG d.ab d.au d.as₁ d.at₁ d.bu d.bs₁ d.bt₁ d.us₁ d.ut₁ d.s₁t₁ h.cm h.βb
    h.hbu h.αa h.hus₁ h.hst₁ h.γa h.α₁ h.β₁
  have hab : (c.kempeGraph β δ).Reachable a b := by
    rw [kempeGraph_comm]; exact ksAB_link hG h.cm h.δa h.βb
  by_cases hua : (c.kempeGraph β δ).Reachable u a
  · set φ' := unsetEdge c u s₂ with hφ'
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
    · exact z_close hG d h.cm h.βb h.hus₁ h.hus₂ h.δa h.hst₁ h.hst₂ h.γa h.β₁ h.β₂ h.δ₁ h.δ₂ r'
    · exact not_three_linked φ' d.as₂.symm d.bs₂.symm d.ab (Or.inr fs) (Or.inr fa) (Or.inl fb) r r'
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
