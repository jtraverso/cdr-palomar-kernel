/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.KiteD

/-!
# Kites, part E: from the kite state to the normal form

`proc`: in state `KS`, with `φ(us₂) = μ ∈ φ̄(a)`, switch `μ, β` on all chains but the `a`–`b`
chain; then `t₁, t₂` miss `μ`, and `us₂` keeps `μ` (if `u` is on the `a`–`b` chain) or becomes `β`
(otherwise, and then `us₁ ↦ swap μ β (φ(us₁))`). `proc_tail` restores `β, τ` at `t₁, t₂`.

`ks_false`: the kite state is impossible, given a robust supply of colours of `φ̄(a)` missing at
both `t₁` and `t₂`. If some `usᵢ` is coloured `β`, `proc` on the other edge gives `KNF` (or its
mirror). Otherwise `proc` on `us₂`, followed (if `us₂` kept its colour `μ`) by the `a`–`b` swaps
`(γ, β)`, `(μ, γ)` that make `μ` the colour missing at `b`, reduces to the previous case.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

set_option maxHeartbeats 1600000 in
/-- **Making `t₁, t₂` miss the colour of `us₂`.** -/
theorem proc (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b cc u s₁ s₂ t₁ t₂ : V}
    (hd : D8 a b cc u s₁ s₂ t₁ t₂) {β α τ γ μ ν ζ ξ : Fin G.maxDegree}
    (h : KS c a b cc u s₁ s₂ t₁ t₂ β α τ γ) (hus₂ : c.col u s₂ = some μ) (μa : c.IsFree a μ)
    (hus₁ : c.col u s₁ = some ν) (ζa : c.IsFree a ζ) (ζ₁ : c.IsFree t₁ ζ) (ζ₂ : c.IsFree t₂ ζ)
    (ξa : c.IsFree a ξ) (ξ₁ : c.IsFree t₁ ξ) (ξ₂ : c.IsFree t₂ ξ) (hζα : ζ ≠ α) (hζτ : ζ ≠ τ)
    (hζμ : ζ ≠ μ) (hζν : ζ ≠ ν) (hξα : ξ ≠ α) (hξτ : ξ ≠ τ) (hξμ : ξ ≠ μ) (hξν : ξ ≠ ν)
    (hζξ : ζ ≠ ξ) :
    ∃ c' : PEC G (Fin G.maxDegree), KS c' a b cc u s₁ s₂ t₁ t₂ β α τ γ ∧ c'.IsFree t₁ μ ∧
      c'.IsFree t₂ μ ∧ (∀ x, x ≠ β → x ≠ γ → x ≠ ζ → x ≠ ξ → (c'.IsFree a x ↔ c.IsFree a x)) ∧
      ((c'.col u s₂ = some μ ∧ c'.col u s₁ = some ν) ∨
        (c'.col u s₂ = some β ∧ c'.col u s₁ = some (Equiv.swap μ β ν))) := by
  have d := hd.d7
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have nb : ∀ {x}, c.IsFree a x → x ≠ β := fun hx e => hdis _ hx (e ▸ h.βb)
  have hμβ := nb μa
  have hαβ := nb h.αa
  have hτβ := nb h.τa
  have hζβ := nb ζa
  have hξβ := nb ξa
  have ng : ∀ {x}, c.IsFree t₁ x → x ≠ γ := fun hx e => hx s₁ (by rw [c.col_symm, h.hst₁, e])
  have hγμ : γ ≠ μ := fun e => d.ut₂ (c.col_proper (by rw [c.col_symm]; exact hus₂)
    (by rw [← e]; exact h.hst₂))
  have hμτ : μ ≠ τ := fun e => hd.ccs₂ (c.col_proper (by rw [c.col_symm]; exact h.hcu)
    (by rw [← e]; exact hus₂))
  have hνμ : ν ≠ μ := fun e => d.s₁s₂ (c.col_proper hus₁ (e ▸ hus₂))
  have hντ : ν ≠ τ := fun e => hd.ccs₁ (c.col_proper (by rw [c.col_symm]; exact h.hcu)
    (by rw [← e]; exact hus₁))
  -- switch `μ, β` off the `a`–`b` chain
  have r1b : (c.kempeGraph μ β).Reachable a b := ksAB_link hG h.cm μa h.βb
  have r1cc : (c.kempeGraph μ β).Reachable a cc :=
    reachable_of_col (Reachable.refl a) (Or.inr h.acc)
  set c₁ := kempeSwapCompl c μ β a with hc₁
  have fa₁ : ∀ x, c₁.IsFree a x ↔ c.IsFree a x :=
    kempeSwapCompl_isFree_of_reachable c μ β (Reachable.refl a)
  have k1 : ∀ x y, (c.kempeGraph μ β).Reachable a x → c₁.col x y = c.col x y :=
    fun x y hx => kempeSwapCompl_col_of_reachable c μ β hx y
  have n1₁ := ab_off hG h.cm μa h.βb (Or.inr h.β₁) d.at₁.symm d.bt₁.symm
  have n1₂ := ab_off hG h.cm μa h.βb (Or.inr h.β₂) d.at₂.symm d.bt₂.symm
  have kt : ∀ {t x}, x ≠ μ → x ≠ β → c.IsFree t x → c₁.IsFree t x :=
    fun h1 h2 hx => (cfree_of_ne c h1 h2).2 hx
  have cm₁ : IsColMinus c₁ a b := h.cm.kempeSwapCompl μ β a
  have βb₁ : c₁.IsFree b β := (kempeSwapCompl_isFree_of_reachable c μ β r1b β).2 h.βb
  have acc₁ : c₁.col a cc = some β := by rw [k1 a cc (Reachable.refl a)]; exact h.acc
  have hbu₁ : c₁.col b u = some α := by rw [k1 b u r1b]; exact h.hbu
  have hcu₁ : c₁.col cc u = some τ := by rw [k1 cc u r1cc]; exact h.hcu
  have hst₁₁ : c₁.col s₁ t₁ = some γ := ccol_keep c h.hst₁ (Or.inl ⟨hγμ, nb h.γa⟩)
  have hst₂₁ : c₁.col s₂ t₂ = some γ := ccol_keep c h.hst₂ (Or.inl ⟨hγμ, nb h.γa⟩)
  have μ₁ : c₁.IsFree t₁ μ := (cfree_flip₂ c n1₁).2 h.β₁
  have μ₂ : c₁.IsFree t₂ μ := (cfree_flip₂ c n1₂).2 h.β₂
  have hαμ : α ≠ μ := fun e => d.bs₂ (c.col_proper (by rw [c.col_symm]; exact h.hbu) (e ▸ hus₂))
  have tail : ∀ ρ₁ ρ₂, c₁.col u s₁ = some ρ₁ → c₁.col u s₂ = some ρ₂ → ρ₁ ≠ τ → ρ₁ ≠ ζ →
      ρ₁ ≠ ξ → ρ₂ ≠ τ → ρ₂ ≠ ζ → ρ₂ ≠ ξ →
      ∃ c' : PEC G (Fin G.maxDegree), KS c' a b cc u s₁ s₂ t₁ t₂ β α τ γ ∧ c'.IsFree t₁ μ ∧
        c'.IsFree t₂ μ ∧ c'.col u s₁ = some ρ₁ ∧ c'.col u s₂ = some ρ₂ ∧
        (∀ x, x ≠ β → x ≠ γ → x ≠ ζ → x ≠ ξ → (c'.IsFree a x ↔ c.IsFree a x)) := by
    intro ρ₁ ρ₂ u1 u2 h1 h2 h3 h4 h5 h6
    obtain ⟨c', hc', m1, m2, v1, v2, hf⟩ := proc_tail hG hd cm₁ βb₁ acc₁ hbu₁ ((fa₁ α).2 h.αa)
      hcu₁ ((fa₁ τ).2 h.τa) hst₁₁ hst₂₁ ((fa₁ γ).2 h.γa) (kt hαμ hαβ h.α₁) (kt hαμ hαβ h.α₂)
      (kt hμτ.symm hτβ h.τ₁) (kt hμτ.symm hτβ h.τ₂) μ₁ μ₂ ((fa₁ μ).2 μa) ((fa₁ ζ).2 ζa)
      (kt hζμ hζβ ζ₁) (kt hζμ hζβ ζ₂) ((fa₁ ξ).2 ξa) (kt hξμ hξβ ξ₁) (kt hξμ hξβ ξ₂) u1 u2
      h1 h2 h3 h4 h5 h6 hμτ hζα hζτ hζμ hξα hξτ hξμ hζξ
    exact ⟨c', hc', m1, m2, v1, v2, fun x e1 e2 e3 e4 => (hf x e1 e2 e3 e4).trans (fa₁ x)⟩
  by_cases hu : (c.kempeGraph μ β).Reachable a u
  · obtain ⟨c', hc', m1, m2, v1, v2, hf⟩ := tail ν μ (by rw [k1 u s₁ hu]; exact hus₁)
      (by rw [k1 u s₂ hu]; exact hus₂) hντ hζν.symm hξν.symm hμτ hζμ.symm hξμ.symm
    exact ⟨c', hc', m1, m2, hf, Or.inl ⟨v2, v1⟩⟩
  · have u2 : c₁.col u s₂ = some β := ccol_flip₁ c hus₂ hu
    have u1 : c₁.col u s₁ = some (Equiv.swap μ β ν) := by
      rw [kempeSwapCompl_col_of_not_reachable c μ β hu, hus₁]; rfl
    have hs : Equiv.swap μ β ν ≠ τ ∧ Equiv.swap μ β ν ≠ ζ ∧ Equiv.swap μ β ν ≠ ξ := by
      by_cases e : ν = β
      · rw [e, Equiv.swap_apply_right]; exact ⟨hμτ, hζμ.symm, hξμ.symm⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hνμ e]; exact ⟨hντ, hζν.symm, hξν.symm⟩
    obtain ⟨s1, s2, s3⟩ := hs
    obtain ⟨c', hc', m1, m2, v1, v2, hf⟩ := tail _ β u1 u2 s1 s2 s3 hτβ.symm hζβ.symm hξβ.symm
    exact ⟨c', hc', m1, m2, hf, Or.inr ⟨v2, v1⟩⟩

end Overfull
