/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Kite0B

/-!
# Kites without `c`, part C: restoring the colours missing at `t₁, t₂`

`KS0`: `φ̄(b) ∋ β`, `φ(bu) = α`, `φ(s₁t₁) = φ(s₂t₂) = γ` with `α, γ ∈ φ̄(a)`, and `t₁, t₂` missing
`α, β`.

`proc_tail0` is `proc_tail` (`KiteD`) with `α` in the role of `τ`: the `a`–`b` chains `(α, β)` and
`(α, ζ)` contain `u`, through the edge `bu` coloured `α`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The kite state without `c`. -/
structure KS0 (c : PEC G (Fin G.maxDegree)) (a b u s₁ s₂ t₁ t₂ : V)
    (β α γ : Fin G.maxDegree) : Prop where
  cm : IsColMinus c a b
  βb : c.IsFree b β
  hbu : c.col b u = some α
  αa : c.IsFree a α
  hst₁ : c.col s₁ t₁ = some γ
  hst₂ : c.col s₂ t₂ = some γ
  γa : c.IsFree a γ
  α₁ : c.IsFree t₁ α
  α₂ : c.IsFree t₂ α
  β₁ : c.IsFree t₁ β
  β₂ : c.IsFree t₂ β

theorem KS0.swap {c : PEC G (Fin G.maxDegree)} {a b u s₁ s₂ t₁ t₂ : V}
    {β α γ : Fin G.maxDegree} (h : KS0 c a b u s₁ s₂ t₁ t₂ β α γ) :
    KS0 c a b u s₂ s₁ t₂ t₁ β α γ :=
  ⟨h.cm, h.βb, h.hbu, h.αa, h.hst₂, h.hst₁, h.γa, h.α₂, h.α₁, h.β₂, h.β₁⟩

set_option maxHeartbeats 4000000 in
/-- **Restoring `β` and `α` at `t₁, t₂`.** -/
theorem proc_tail0 (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u s₁ s₂ t₁ t₂ : V}
    (d : Distinct7 a b u s₁ s₂ t₁ t₂) {β α γ μ ζ ξ ρ₁ ρ₂ : Fin G.maxDegree}
    (cm : IsColMinus c a b) (βb : c.IsFree b β) (hbu : c.col b u = some α) (αa : c.IsFree a α)
    (hst₁ : c.col s₁ t₁ = some γ) (hst₂ : c.col s₂ t₂ = some γ) (γa : c.IsFree a γ)
    (α₁ : c.IsFree t₁ α) (α₂ : c.IsFree t₂ α) (μ₁ : c.IsFree t₁ μ) (μ₂ : c.IsFree t₂ μ)
    (μa : c.IsFree a μ) (ζa : c.IsFree a ζ) (ζ₁ : c.IsFree t₁ ζ) (ζ₂ : c.IsFree t₂ ζ)
    (ξa : c.IsFree a ξ) (ξ₁ : c.IsFree t₁ ξ) (ξ₂ : c.IsFree t₂ ξ)
    (hus₁ : c.col u s₁ = some ρ₁) (hus₂ : c.col u s₂ = some ρ₂)
    (hρ₁ζ : ρ₁ ≠ ζ) (hρ₁ξ : ρ₁ ≠ ξ) (hρ₂ζ : ρ₂ ≠ ζ) (hρ₂ξ : ρ₂ ≠ ξ) (hμα : μ ≠ α) (hζα : ζ ≠ α)
    (hζμ : ζ ≠ μ) (hξα : ξ ≠ α) (hξμ : ξ ≠ μ) (hζξ : ζ ≠ ξ) :
    ∃ c' : PEC G (Fin G.maxDegree), KS0 c' a b u s₁ s₂ t₁ t₂ β α γ ∧ c'.IsFree t₁ μ ∧
      c'.IsFree t₂ μ ∧ c'.col u s₁ = some ρ₁ ∧ c'.col u s₂ = some ρ₂ ∧
      (∀ x, x ≠ β → x ≠ γ → x ≠ ζ → x ≠ ξ → (c'.IsFree a x ↔ c.IsFree a x)) := by
  obtain ⟨hdis, -⟩ := cm.ab_facts hG
  have nb : ∀ {x}, c.IsFree a x → x ≠ β := fun hx e => hdis _ hx (e ▸ βb)
  have hαβ := nb αa
  have hγβ := nb γa
  have hμβ := nb μa
  have hζβ := nb ζa
  have hξβ := nb ξa
  have ng : ∀ {x}, c.IsFree t₁ x → x ≠ γ := fun hx e => hx s₁ (by rw [c.col_symm, hst₁, e])
  have hαγ := ng α₁
  have hζγ := ng ζ₁
  have hξγ := ng ξ₁
  have hρ₁γ : ρ₁ ≠ γ := fun e => d.ut₁ (c.col_proper (by rw [c.col_symm]; exact hus₁)
    (by rw [e]; exact hst₁))
  have hρ₂γ : ρ₂ ≠ γ := fun e => d.ut₂ (c.col_proper (by rw [c.col_symm]; exact hus₂)
    (by rw [e]; exact hst₂))
  -- step 2: switch `α, β` off the `a`–`b` chain (it contains `b u`)
  have r2b : (c.kempeGraph α β).Reachable a b := ksAB_link hG cm αa βb
  have r2u : (c.kempeGraph α β).Reachable a u := reachable_of_col r2b (Or.inl hbu)
  set c₂ := kempeSwapCompl c α β a with hc₂
  have cm₂ : IsColMinus c₂ a b := cm.kempeSwapCompl α β a
  have fa₂ : ∀ x, c₂.IsFree a x ↔ c.IsFree a x :=
    kempeSwapCompl_isFree_of_reachable c α β (Reachable.refl a)
  have k2 : ∀ x y, (c.kempeGraph α β).Reachable a x → c₂.col x y = c.col x y :=
    fun x y hx => kempeSwapCompl_col_of_reachable c α β hx y
  have βb₂ : c₂.IsFree b β := (kempeSwapCompl_isFree_of_reachable c α β r2b β).2 βb
  have hbu₂ : c₂.col b u = some α := by rw [k2 b u r2b]; exact hbu
  have γa₂ := (fa₂ γ).2 γa
  -- step 3: the `a`–`b` swap `(γ, β)`
  set c₃ := c₂.kempeSwap γ β a with hc₃
  have cm₃ : IsColMinus c₃ a b := cm₂.kempeSwap γ β a
  have γb₃ : c₃.IsFree b γ := ksAB_free_b hG cm₂ γa₂ βb₂
  have βa₃ : c₃.IsFree a β := ksAB_free_a hG cm₂ γa₂ βb₂
  have fa₃ : ∀ x, x ≠ γ → x ≠ β → (c₃.IsFree a x ↔ c₂.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₂ γa₂ βb₂ h1 h2
  have hbu₃ : c₃.col b u = some α := kcol_keep c₂ hbu₂ (Or.inl ⟨hαγ, hαβ⟩)
  -- step 4: the `a`–`b` swap `(ζ, γ)`
  have ζa₃ : c₃.IsFree a ζ := (fa₃ ζ hζγ hζβ).2 ((fa₂ ζ).2 ζa)
  set c₄ := c₃.kempeSwap ζ γ a with hc₄
  have cm₄ : IsColMinus c₄ a b := cm₃.kempeSwap ζ γ a
  have ζb₄ : c₄.IsFree b ζ := ksAB_free_b hG cm₃ ζa₃ γb₃
  have γa₄ : c₄.IsFree a γ := ksAB_free_a hG cm₃ ζa₃ γb₃
  have fa₄ : ∀ x, x ≠ ζ → x ≠ γ → (c₄.IsFree a x ↔ c₃.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₃ ζa₃ γb₃ h1 h2
  have hbu₄ : c₄.col b u = some α := kcol_keep c₃ hbu₃ (Or.inl ⟨hζα.symm, hαγ⟩)
  -- step 5: switch `α, ζ` off the `a`–`b` chain (it contains `b u`)
  have αa₄ : c₄.IsFree a α := (fa₄ α hζα.symm hαγ).2 ((fa₃ α hαγ hαβ).2 ((fa₂ α).2 αa))
  have r5b : (c₄.kempeGraph α ζ).Reachable a b := ksAB_link hG cm₄ αa₄ ζb₄
  have r5u : (c₄.kempeGraph α ζ).Reachable a u := reachable_of_col r5b (Or.inl hbu₄)
  set c₅ := kempeSwapCompl c₄ α ζ a with hc₅
  have cm₅ : IsColMinus c₅ a b := cm₄.kempeSwapCompl α ζ a
  have fa₅ : ∀ x, c₅.IsFree a x ↔ c₄.IsFree a x :=
    kempeSwapCompl_isFree_of_reachable c₄ α ζ (Reachable.refl a)
  have k5 : ∀ x y, (c₄.kempeGraph α ζ).Reachable a x → c₅.col x y = c₄.col x y :=
    fun x y hx => kempeSwapCompl_col_of_reachable c₄ α ζ hx y
  have ζb₅ : c₅.IsFree b ζ := (kempeSwapCompl_isFree_of_reachable c₄ α ζ r5b ζ).2 ζb₄
  have hbu₅ : c₅.col b u = some α := by rw [k5 b u r5b]; exact hbu₄
  -- step 6: the `a`–`b` swap `(ξ, ζ)`
  have ξa₅ : c₅.IsFree a ξ :=
    (fa₅ ξ).2 ((fa₄ ξ hζξ.symm hξγ).2 ((fa₃ ξ hξγ hξβ).2 ((fa₂ ξ).2 ξa)))
  set c₆ := c₅.kempeSwap ξ ζ a with hc₆
  have cm₆ : IsColMinus c₆ a b := cm₅.kempeSwap ξ ζ a
  have ξb₆ : c₆.IsFree b ξ := ksAB_free_b hG cm₅ ξa₅ ζb₅
  have fa₆ : ∀ x, x ≠ ξ → x ≠ ζ → (c₆.IsFree a x ↔ c₅.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₅ ξa₅ ζb₅ h1 h2
  have hbu₆ : c₆.col b u = some α := kcol_keep c₅ hbu₅ (Or.inl ⟨hξα.symm, hζα.symm⟩)
  -- step 7: the `a`–`b` swap `(γ, ξ)`
  have γa₆ : c₆.IsFree a γ := (fa₆ γ hξγ.symm hζγ.symm).2 ((fa₅ γ).2 γa₄)
  set c₇ := c₆.kempeSwap γ ξ a with hc₇
  have cm₇ : IsColMinus c₇ a b := cm₆.kempeSwap γ ξ a
  have γb₇ : c₇.IsFree b γ := ksAB_free_b hG cm₆ γa₆ ξb₆
  have fa₇ : ∀ x, x ≠ γ → x ≠ ξ → (c₇.IsFree a x ↔ c₆.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₆ γa₆ ξb₆ h1 h2
  have hbu₇ : c₇.col b u = some α := kcol_keep c₆ hbu₆ (Or.inl ⟨hαγ, hξα.symm⟩)
  -- step 8: the `a`–`b` swap `(β, γ)`
  have βa₇ : c₇.IsFree a β := (fa₇ β hγβ.symm hξβ.symm).2 ((fa₆ β hξβ.symm hζβ.symm).2
    ((fa₅ β).2 ((fa₄ β hζβ.symm hγβ.symm).2 βa₃)))
  set c₈ := c₇.kempeSwap β γ a with hc₈
  have cm₈ : IsColMinus c₈ a b := cm₇.kempeSwap β γ a
  have βb₈ : c₈.IsFree b β := ksAB_free_b hG cm₇ βa₇ γb₇
  have γa₈ : c₈.IsFree a γ := ksAB_free_a hG cm₇ βa₇ γb₇
  have fa₈ : ∀ x, x ≠ β → x ≠ γ → (c₈.IsFree a x ↔ c₇.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₇ βa₇ γb₇ h1 h2
  have hbu₈ : c₈.col b u = some α := kcol_keep c₇ hbu₇ (Or.inl ⟨hαβ, hαγ⟩)
  have fall : ∀ x, x ≠ β → x ≠ γ → x ≠ ζ → x ≠ ξ → (c₈.IsFree a x ↔ c.IsFree a x) :=
    fun x h1 h2 h3 h4 => (fa₈ x h1 h2).trans ((fa₇ x h2 h4).trans ((fa₆ x h4 h3).trans
      ((fa₅ x).trans ((fa₄ x h3 h2).trans ((fa₃ x h2 h1).trans (fa₂ x))))))
  -- the vertices `t₁, t₂`
  have key : ∀ t s, t ≠ a → t ≠ b → c.IsFree t α → c.IsFree t μ →
      c.IsFree t ζ → c.IsFree t ξ → c.col s t = some γ →
      c₂.IsFree t β ∧ c₂.col s t = some γ ∧ c₇.IsFree t β ∧ c₇.col s t = some γ ∧
      c₈.IsFree t α ∧ c₈.IsFree t β ∧ c₈.IsFree t μ ∧ c₈.col s t = some γ := by
    intro t s ta tb hα hμ hζ hξ hst
    have n2 := ab_off hG cm αa βb (Or.inl hα) ta tb
    have β2 : c₂.IsFree t β := (cfree_flip₁ c n2).2 hα
    have kt2 : ∀ x, x ≠ α → x ≠ β → c.IsFree t x → c₂.IsFree t x :=
      fun x h1 h2 h => (cfree_of_ne c h1 h2).2 h
    have st2 : c₂.col s t = some γ := ccol_keep c hst (Or.inl ⟨hαγ.symm, hγβ⟩)
    have n3 := ab_off hG cm₂ γa₂ βb₂ (Or.inr β2) ta tb
    have st3 := ab_keep_t hG cm₂ γa₂ βb₂ (Or.inr β2) ta tb st2
    have ζ3 : c₃.IsFree t ζ := (kfree_off c₂ n3 ζ).2 (kt2 ζ hζα hζβ hζ)
    have n4 := ab_off hG cm₃ ζa₃ γb₃ (Or.inl ζ3) ta tb
    have st4 := ab_keep_t hG cm₃ ζa₃ γb₃ (Or.inl ζ3) ta tb st3
    have ζ4 : c₄.IsFree t ζ := (kfree_off c₃ n4 ζ).2 ζ3
    have n5 := ab_off hG cm₄ αa₄ ζb₄ (Or.inr ζ4) ta tb
    have α5 : c₅.IsFree t α := (cfree_flip₂ c₄ n5).2 ζ4
    have st5 : c₅.col s t = some γ := ccol_keep c₄ st4 (Or.inl ⟨hαγ.symm, hζγ.symm⟩)
    have tr5 : ∀ x, x ≠ α → x ≠ ζ → c₂.IsFree t x → c₅.IsFree t x := fun x h1 h2 h =>
      (cfree_of_ne c₄ h1 h2).2 ((kfree_off c₃ n4 x).2 ((kfree_off c₂ n3 x).2 h))
    have ξ5 : c₅.IsFree t ξ := tr5 ξ hξα hζξ.symm (kt2 ξ hξα hξβ hξ)
    have n6 := ab_off hG cm₅ ξa₅ ζb₅ (Or.inl ξ5) ta tb
    have st6 := ab_keep_t hG cm₅ ξa₅ ζb₅ (Or.inl ξ5) ta tb st5
    have ξ6 : c₆.IsFree t ξ := (kfree_off c₅ n6 ξ).2 ξ5
    have n7 := ab_off hG cm₆ γa₆ ξb₆ (Or.inr ξ6) ta tb
    have st7 := ab_keep_t hG cm₆ γa₆ ξb₆ (Or.inr ξ6) ta tb st6
    have tr7 : ∀ x, c₅.IsFree t x → c₇.IsFree t x := fun x h =>
      (kfree_off c₆ n7 x).2 ((kfree_off c₅ n6 x).2 h)
    have β7 : c₇.IsFree t β := tr7 β (tr5 β hαβ.symm hζβ.symm β2)
    have n8 := ab_off hG cm₇ βa₇ γb₇ (Or.inl β7) ta tb
    have st8 := ab_keep_t hG cm₇ βa₇ γb₇ (Or.inl β7) ta tb st7
    have tr8 : ∀ x, c₅.IsFree t x → c₈.IsFree t x := fun x h => (kfree_off c₇ n8 x).2 (tr7 x h)
    exact ⟨β2, st2, β7, st7, tr8 α α5, (kfree_off c₇ n8 β).2 β7,
      tr8 μ (tr5 μ hμα hζμ.symm (kt2 μ hμα hμβ hμ)), st8⟩
  obtain ⟨β₁2, st₁2, β₁7, st₁7, α₁8, β₁8, μ₁8, st₁8⟩ :=
    key t₁ s₁ d.at₁.symm d.bt₁.symm α₁ μ₁ ζ₁ ξ₁ hst₁
  obtain ⟨β₂2, st₂2, β₂7, st₂7, α₂8, β₂8, μ₂8, st₂8⟩ :=
    key t₂ s₂ d.at₂.symm d.bt₂.symm α₂ μ₂ ζ₂ ξ₂ hst₂
  -- the edges `us₁, us₂`
  have usk : ∀ s t ρ, t ≠ a → t ≠ b → ρ ≠ ζ → ρ ≠ ξ → ρ ≠ γ → c.col u s = some ρ →
      c₂.IsFree t β → c₂.col s t = some γ → c₇.IsFree t β → c₇.col s t = some γ →
      c₈.col u s = some ρ := by
    intro s t ρ ta tb h2 h3 h4 hus h2t h2s h7t h7s
    have u2 : c₂.col u s = some ρ := by rw [k2 u s r2u]; exact hus
    have u3 : c₃.col u s = some ρ := by
      by_cases e : ρ = β
      · rw [e] at u2 ⊢; exact ab_keep_us hG cm₂ γa₂ βb₂ h2t ta tb h2s u2
      · exact kcol_keep c₂ u2 (Or.inl ⟨h4, e⟩)
    have u4 : c₄.col u s = some ρ := kcol_keep c₃ u3 (Or.inl ⟨h2, h4⟩)
    have u5 : c₅.col u s = some ρ := by rw [k5 u s r5u]; exact u4
    have u6 : c₆.col u s = some ρ := kcol_keep c₅ u5 (Or.inl ⟨h3, h2⟩)
    have u7 : c₇.col u s = some ρ := kcol_keep c₆ u6 (Or.inl ⟨h4, h3⟩)
    by_cases e : ρ = β
    · rw [e] at u7 ⊢; exact ab_keep_us' hG cm₇ βa₇ γb₇ h7t ta tb h7s u7
    · exact kcol_keep c₇ u7 (Or.inl ⟨e, h4⟩)
  have us₁8 := usk s₁ t₁ ρ₁ d.at₁.symm d.bt₁.symm hρ₁ζ hρ₁ξ hρ₁γ hus₁ β₁2 st₁2 β₁7 st₁7
  have us₂8 := usk s₂ t₂ ρ₂ d.at₂.symm d.bt₂.symm hρ₂ζ hρ₂ξ hρ₂γ hus₂ β₂2 st₂2 β₂7 st₂7
  exact ⟨c₈, ⟨cm₈, βb₈, hbu₈, (fall α hαβ hαγ hζα.symm hξα.symm).2 αa, st₁8, st₂8, γa₈,
    α₁8, α₂8, β₁8, β₂8⟩, μ₁8, μ₂8, us₁8, us₂8, fall⟩

end Overfull
