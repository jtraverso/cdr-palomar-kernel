/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.KiteC

/-!
# Kites, part D: restoring the colours missing at `t₁, t₂`

`KS`: the kite state `φ̄(b) ∋ β`, `φ(a cc) = β`, `φ(bu) = α`, `φ(cc u) = τ`,
`φ(s₁t₁) = φ(s₂t₂) = γ` with `α, τ, γ ∈ φ̄(a)`, and `t₁, t₂` missing `α, β, τ`.

`proc_tail`: if `t₁, t₂` miss `τ` (and `α, μ` and two fresh colours `ζ, ξ` of `φ̄(a)`), then the
operations
* switch `τ, β` on all chains but the `a`–`b` chain (it contains `a cc u`): `t₁, t₂` now miss `β`;
* swap the `a`–`b` chains `(γ, β)` and `(ζ, γ)` (now `φ(a cc) = ζ`);
* switch `τ, ζ` on all chains but the `a`–`b` chain: `t₁, t₂` miss `τ` again;
* swap the `a`–`b` chains `(ξ, ζ)`, `(γ, ξ)` and `(β, γ)`

give a colouring in state `KS` (same colours) where `t₁, t₂` still miss `μ`, and the colours of
`us₁, us₂` are unchanged. An `a`–`b` swap never meets `t₁, t₂` (they miss one of its colours); an
edge `usᵢ` coloured `β` is never on the `a`–`b` `(γ, β)`-chain, because `tᵢ sᵢ u` lies on the
`(γ, β)`-chain of `tᵢ`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Eight distinct vertices. -/
structure D8 (a b cc u s₁ s₂ t₁ t₂ : V) : Prop where
  d7 : Distinct7 a b u s₁ s₂ t₁ t₂
  acc : a ≠ cc
  bcc : b ≠ cc
  ccu : cc ≠ u
  ccs₁ : cc ≠ s₁
  ccs₂ : cc ≠ s₂
  cct₁ : cc ≠ t₁
  cct₂ : cc ≠ t₂

theorem D8.swap {a b cc u s₁ s₂ t₁ t₂ : V} (h : D8 a b cc u s₁ s₂ t₁ t₂) :
    D8 a b cc u s₂ s₁ t₂ t₁ :=
  ⟨h.d7.swap, h.acc, h.bcc, h.ccu, h.ccs₂, h.ccs₁, h.cct₂, h.cct₁⟩

/-- The kite state. -/
structure KS (c : PEC G (Fin G.maxDegree)) (a b cc u s₁ s₂ t₁ t₂ : V)
    (β α τ γ : Fin G.maxDegree) : Prop where
  cm : IsColMinus c a b
  βb : c.IsFree b β
  acc : c.col a cc = some β
  hbu : c.col b u = some α
  αa : c.IsFree a α
  hcu : c.col cc u = some τ
  τa : c.IsFree a τ
  hst₁ : c.col s₁ t₁ = some γ
  hst₂ : c.col s₂ t₂ = some γ
  γa : c.IsFree a γ
  α₁ : c.IsFree t₁ α
  α₂ : c.IsFree t₂ α
  β₁ : c.IsFree t₁ β
  β₂ : c.IsFree t₂ β
  τ₁ : c.IsFree t₁ τ
  τ₂ : c.IsFree t₂ τ

theorem KS.swap {c : PEC G (Fin G.maxDegree)} {a b cc u s₁ s₂ t₁ t₂ : V}
    {β α τ γ : Fin G.maxDegree} (h : KS c a b cc u s₁ s₂ t₁ t₂ β α τ γ) :
    KS c a b cc u s₂ s₁ t₂ t₁ β α τ γ :=
  ⟨h.cm, h.βb, h.acc, h.hbu, h.αa, h.hcu, h.τa, h.hst₂, h.hst₁, h.γa, h.α₂, h.α₁, h.β₂, h.β₁,
    h.τ₂, h.τ₁⟩

/-- An `a`–`b` swap does not touch `t`, which misses one of its colours. -/
theorem ab_off (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b t : V}
    (cm : IsColMinus c a b) {θ η : Fin G.maxDegree} (hθ : c.IsFree a θ) (hη : c.IsFree b η)
    (ht : c.IsFree t θ ∨ c.IsFree t η) (hta : t ≠ a) (htb : t ≠ b) :
    ¬ (c.kempeGraph θ η).Reachable a t :=
  ksAB_not_reach hG cm hθ hη ht hta htb (Reachable.refl t)

/-- An edge `st` keeps its colour under an `a`–`b` swap one of whose colours `t` misses. -/
theorem ab_keep_t (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b t s : V}
    (cm : IsColMinus c a b) {θ η ε : Fin G.maxDegree} (hθ : c.IsFree a θ) (hη : c.IsFree b η)
    (ht : c.IsFree t θ ∨ c.IsFree t η) (hta : t ≠ a) (htb : t ≠ b) (hst : c.col s t = some ε) :
    (c.kempeSwap θ η a).col s t = some ε := by
  rw [PEC.col_symm]
  exact kcol_keep c (by rw [PEC.col_symm]; exact hst) (Or.inr (ab_off hG cm hθ hη ht hta htb))

/-- `us` coloured `β` keeps its colour under the `a`–`b` swap `(θ, β)` when `t` misses `β` and
`st` is coloured `θ`. -/
theorem ab_keep_us (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u s t : V}
    (cm : IsColMinus c a b) {θ β : Fin G.maxDegree} (hθ : c.IsFree a θ) (hβ : c.IsFree b β)
    (htβ : c.IsFree t β) (hta : t ≠ a) (htb : t ≠ b) (hst : c.col s t = some θ)
    (hus : c.col u s = some β) : (c.kempeSwap θ β a).col u s = some β := by
  have r : (c.kempeGraph θ β).Reachable t u :=
    reachable_of_col (reachable_of_col (Reachable.refl t)
      (Or.inl (by rw [PEC.col_symm]; exact hst))) (Or.inr (by rw [PEC.col_symm]; exact hus))
  exact kcol_keep c hus (Or.inr (ksAB_not_reach hG cm hθ hβ (Or.inr htβ) hta htb r))

/-- The same, with the colours of the swap in the other order. -/
theorem ab_keep_us' (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u s t : V}
    (cm : IsColMinus c a b) {θ β : Fin G.maxDegree} (hβ : c.IsFree a β) (hθ : c.IsFree b θ)
    (htβ : c.IsFree t β) (hta : t ≠ a) (htb : t ≠ b) (hst : c.col s t = some θ)
    (hus : c.col u s = some β) : (c.kempeSwap β θ a).col u s = some β := by
  have r : (c.kempeGraph β θ).Reachable t u :=
    reachable_of_col (reachable_of_col (Reachable.refl t)
      (Or.inr (by rw [PEC.col_symm]; exact hst))) (Or.inl (by rw [PEC.col_symm]; exact hus))
  exact kcol_keep c hus (Or.inr (ksAB_not_reach hG cm hβ hθ (Or.inl htβ) hta htb r))

set_option maxHeartbeats 4000000 in
/-- **Restoring `β` and `τ` at `t₁, t₂`.** -/
theorem proc_tail (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b cc u s₁ s₂ t₁ t₂ : V}
    (hd : D8 a b cc u s₁ s₂ t₁ t₂) {β α τ γ μ ζ ξ ρ₁ ρ₂ : Fin G.maxDegree}
    (cm : IsColMinus c a b) (βb : c.IsFree b β) (acc : c.col a cc = some β)
    (hbu : c.col b u = some α) (αa : c.IsFree a α) (hcu : c.col cc u = some τ)
    (τa : c.IsFree a τ) (hst₁ : c.col s₁ t₁ = some γ) (hst₂ : c.col s₂ t₂ = some γ)
    (γa : c.IsFree a γ) (α₁ : c.IsFree t₁ α) (α₂ : c.IsFree t₂ α) (τ₁ : c.IsFree t₁ τ)
    (τ₂ : c.IsFree t₂ τ) (μ₁ : c.IsFree t₁ μ) (μ₂ : c.IsFree t₂ μ) (μa : c.IsFree a μ)
    (ζa : c.IsFree a ζ) (ζ₁ : c.IsFree t₁ ζ) (ζ₂ : c.IsFree t₂ ζ)
    (ξa : c.IsFree a ξ) (ξ₁ : c.IsFree t₁ ξ) (ξ₂ : c.IsFree t₂ ξ)
    (hus₁ : c.col u s₁ = some ρ₁) (hus₂ : c.col u s₂ = some ρ₂)
    (hρ₁τ : ρ₁ ≠ τ) (hρ₁ζ : ρ₁ ≠ ζ) (hρ₁ξ : ρ₁ ≠ ξ) (hρ₂τ : ρ₂ ≠ τ) (hρ₂ζ : ρ₂ ≠ ζ)
    (hρ₂ξ : ρ₂ ≠ ξ) (hμτ : μ ≠ τ) (hζα : ζ ≠ α) (hζτ : ζ ≠ τ) (hζμ : ζ ≠ μ) (hξα : ξ ≠ α)
    (hξτ : ξ ≠ τ) (hξμ : ξ ≠ μ) (hζξ : ζ ≠ ξ) :
    ∃ c' : PEC G (Fin G.maxDegree), KS c' a b cc u s₁ s₂ t₁ t₂ β α τ γ ∧ c'.IsFree t₁ μ ∧
      c'.IsFree t₂ μ ∧ c'.col u s₁ = some ρ₁ ∧ c'.col u s₂ = some ρ₂ ∧
      (∀ x, x ≠ β → x ≠ γ → x ≠ ζ → x ≠ ξ → (c'.IsFree a x ↔ c.IsFree a x)) := by
  have d := hd.d7
  obtain ⟨hdis, -⟩ := cm.ab_facts hG
  have nb : ∀ {x}, c.IsFree a x → x ≠ β := fun hx e => hdis _ hx (e ▸ βb)
  have hαβ := nb αa
  have hτβ := nb τa
  have hγβ := nb γa
  have hμβ := nb μa
  have hζβ := nb ζa
  have hξβ := nb ξa
  have ng : ∀ {x}, c.IsFree t₁ x → x ≠ γ := fun hx e => hx s₁ (by rw [c.col_symm, hst₁, e])
  have hαγ := ng α₁
  have hτγ := ng τ₁
  have hζγ := ng ζ₁
  have hξγ := ng ξ₁
  have hρ₁γ : ρ₁ ≠ γ := fun e => d.ut₁ (c.col_proper (by rw [c.col_symm]; exact hus₁)
    (by rw [e]; exact hst₁))
  have hρ₂γ : ρ₂ ≠ γ := fun e => d.ut₂ (c.col_proper (by rw [c.col_symm]; exact hus₂)
    (by rw [e]; exact hst₂))
  have hατ : α ≠ τ := fun e => hd.bcc (c.col_proper (by rw [c.col_symm]; exact hbu)
    (by rw [e, c.col_symm]; exact hcu))
  -- step 2: switch `τ, β` off the `a`–`b` chain
  have r2b : (c.kempeGraph τ β).Reachable a b := ksAB_link hG cm τa βb
  have r2cc : (c.kempeGraph τ β).Reachable a cc :=
    reachable_of_col (Reachable.refl a) (Or.inr acc)
  have r2u : (c.kempeGraph τ β).Reachable a u := reachable_of_col r2cc (Or.inl hcu)
  set c₂ := kempeSwapCompl c τ β a with hc₂
  have cm₂ : IsColMinus c₂ a b := cm.kempeSwapCompl τ β a
  have fa₂ : ∀ x, c₂.IsFree a x ↔ c.IsFree a x :=
    kempeSwapCompl_isFree_of_reachable c τ β (Reachable.refl a)
  have k2 : ∀ x y, (c.kempeGraph τ β).Reachable a x → c₂.col x y = c.col x y :=
    fun x y hx => kempeSwapCompl_col_of_reachable c τ β hx y
  have βb₂ : c₂.IsFree b β := (kempeSwapCompl_isFree_of_reachable c τ β r2b β).2 βb
  have acc₂ : c₂.col a cc = some β := by rw [k2 a cc (Reachable.refl a)]; exact acc
  have hbu₂ : c₂.col b u = some α := by rw [k2 b u r2b]; exact hbu
  have hcu₂ : c₂.col cc u = some τ := by rw [k2 cc u r2cc]; exact hcu
  have γa₂ := (fa₂ γ).2 γa
  -- step 3: the `a`–`b` swap `(γ, β)`
  set c₃ := c₂.kempeSwap γ β a with hc₃
  have cm₃ : IsColMinus c₃ a b := cm₂.kempeSwap γ β a
  have γb₃ : c₃.IsFree b γ := ksAB_free_b hG cm₂ γa₂ βb₂
  have βa₃ : c₃.IsFree a β := ksAB_free_a hG cm₂ γa₂ βb₂
  have fa₃ : ∀ x, x ≠ γ → x ≠ β → (c₃.IsFree a x ↔ c₂.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₂ γa₂ βb₂ h1 h2
  have acc₃ : c₃.col a cc = some γ := kcol_flip₂ c₂ acc₂ (Reachable.refl a)
  have hbu₃ : c₃.col b u = some α := kcol_keep c₂ hbu₂ (Or.inl ⟨hαγ, hαβ⟩)
  have hcu₃ : c₃.col cc u = some τ := kcol_keep c₂ hcu₂ (Or.inl ⟨hτγ, hτβ⟩)
  -- step 4: the `a`–`b` swap `(ζ, γ)`
  have ζa₃ : c₃.IsFree a ζ := (fa₃ ζ hζγ hζβ).2 ((fa₂ ζ).2 ζa)
  set c₄ := c₃.kempeSwap ζ γ a with hc₄
  have cm₄ : IsColMinus c₄ a b := cm₃.kempeSwap ζ γ a
  have ζb₄ : c₄.IsFree b ζ := ksAB_free_b hG cm₃ ζa₃ γb₃
  have γa₄ : c₄.IsFree a γ := ksAB_free_a hG cm₃ ζa₃ γb₃
  have fa₄ : ∀ x, x ≠ ζ → x ≠ γ → (c₄.IsFree a x ↔ c₃.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₃ ζa₃ γb₃ h1 h2
  have acc₄ : c₄.col a cc = some ζ := kcol_flip₂ c₃ acc₃ (Reachable.refl a)
  have hbu₄ : c₄.col b u = some α := kcol_keep c₃ hbu₃ (Or.inl ⟨hζα.symm, hαγ⟩)
  have hcu₄ : c₄.col cc u = some τ := kcol_keep c₃ hcu₃ (Or.inl ⟨hζτ.symm, hτγ⟩)
  -- step 5: switch `τ, ζ` off the `a`–`b` chain
  have τa₄ : c₄.IsFree a τ := (fa₄ τ hζτ.symm hτγ).2 ((fa₃ τ hτγ hτβ).2 ((fa₂ τ).2 τa))
  have r5b : (c₄.kempeGraph τ ζ).Reachable a b := ksAB_link hG cm₄ τa₄ ζb₄
  have r5cc : (c₄.kempeGraph τ ζ).Reachable a cc :=
    reachable_of_col (Reachable.refl a) (Or.inr acc₄)
  have r5u : (c₄.kempeGraph τ ζ).Reachable a u := reachable_of_col r5cc (Or.inl hcu₄)
  set c₅ := kempeSwapCompl c₄ τ ζ a with hc₅
  have cm₅ : IsColMinus c₅ a b := cm₄.kempeSwapCompl τ ζ a
  have fa₅ : ∀ x, c₅.IsFree a x ↔ c₄.IsFree a x :=
    kempeSwapCompl_isFree_of_reachable c₄ τ ζ (Reachable.refl a)
  have k5 : ∀ x y, (c₄.kempeGraph τ ζ).Reachable a x → c₅.col x y = c₄.col x y :=
    fun x y hx => kempeSwapCompl_col_of_reachable c₄ τ ζ hx y
  have ζb₅ : c₅.IsFree b ζ := (kempeSwapCompl_isFree_of_reachable c₄ τ ζ r5b ζ).2 ζb₄
  have acc₅ : c₅.col a cc = some ζ := by rw [k5 a cc (Reachable.refl a)]; exact acc₄
  have hbu₅ : c₅.col b u = some α := by rw [k5 b u r5b]; exact hbu₄
  have hcu₅ : c₅.col cc u = some τ := by rw [k5 cc u r5cc]; exact hcu₄
  -- step 6: the `a`–`b` swap `(ξ, ζ)`
  have ξa₅ : c₅.IsFree a ξ :=
    (fa₅ ξ).2 ((fa₄ ξ hζξ.symm hξγ).2 ((fa₃ ξ hξγ hξβ).2 ((fa₂ ξ).2 ξa)))
  set c₆ := c₅.kempeSwap ξ ζ a with hc₆
  have cm₆ : IsColMinus c₆ a b := cm₅.kempeSwap ξ ζ a
  have ξb₆ : c₆.IsFree b ξ := ksAB_free_b hG cm₅ ξa₅ ζb₅
  have fa₆ : ∀ x, x ≠ ξ → x ≠ ζ → (c₆.IsFree a x ↔ c₅.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₅ ξa₅ ζb₅ h1 h2
  have acc₆ : c₆.col a cc = some ξ := kcol_flip₂ c₅ acc₅ (Reachable.refl a)
  have hbu₆ : c₆.col b u = some α := kcol_keep c₅ hbu₅ (Or.inl ⟨hξα.symm, hζα.symm⟩)
  have hcu₆ : c₆.col cc u = some τ := kcol_keep c₅ hcu₅ (Or.inl ⟨hξτ.symm, hζτ.symm⟩)
  -- step 7: the `a`–`b` swap `(γ, ξ)`
  have γa₆ : c₆.IsFree a γ := (fa₆ γ hξγ.symm hζγ.symm).2 ((fa₅ γ).2 γa₄)
  set c₇ := c₆.kempeSwap γ ξ a with hc₇
  have cm₇ : IsColMinus c₇ a b := cm₆.kempeSwap γ ξ a
  have γb₇ : c₇.IsFree b γ := ksAB_free_b hG cm₆ γa₆ ξb₆
  have fa₇ : ∀ x, x ≠ γ → x ≠ ξ → (c₇.IsFree a x ↔ c₆.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₆ γa₆ ξb₆ h1 h2
  have acc₇ : c₇.col a cc = some γ := kcol_flip₂ c₆ acc₆ (Reachable.refl a)
  have hbu₇ : c₇.col b u = some α := kcol_keep c₆ hbu₆ (Or.inl ⟨hαγ, hξα.symm⟩)
  have hcu₇ : c₇.col cc u = some τ := kcol_keep c₆ hcu₆ (Or.inl ⟨hτγ, hξτ.symm⟩)
  -- step 8: the `a`–`b` swap `(β, γ)`
  have βa₇ : c₇.IsFree a β := (fa₇ β hγβ.symm hξβ.symm).2 ((fa₆ β hξβ.symm hζβ.symm).2
    ((fa₅ β).2 ((fa₄ β hζβ.symm hγβ.symm).2 βa₃)))
  set c₈ := c₇.kempeSwap β γ a with hc₈
  have cm₈ : IsColMinus c₈ a b := cm₇.kempeSwap β γ a
  have βb₈ : c₈.IsFree b β := ksAB_free_b hG cm₇ βa₇ γb₇
  have γa₈ : c₈.IsFree a γ := ksAB_free_a hG cm₇ βa₇ γb₇
  have fa₈ : ∀ x, x ≠ β → x ≠ γ → (c₈.IsFree a x ↔ c₇.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₇ βa₇ γb₇ h1 h2
  have acc₈ : c₈.col a cc = some β := kcol_flip₂ c₇ acc₇ (Reachable.refl a)
  have hbu₈ : c₈.col b u = some α := kcol_keep c₇ hbu₇ (Or.inl ⟨hαβ, hαγ⟩)
  have hcu₈ : c₈.col cc u = some τ := kcol_keep c₇ hcu₇ (Or.inl ⟨hτβ, hτγ⟩)
  have fall : ∀ x, x ≠ β → x ≠ γ → x ≠ ζ → x ≠ ξ → (c₈.IsFree a x ↔ c.IsFree a x) :=
    fun x h1 h2 h3 h4 => (fa₈ x h1 h2).trans ((fa₇ x h2 h4).trans ((fa₆ x h4 h3).trans
      ((fa₅ x).trans ((fa₄ x h3 h2).trans ((fa₃ x h2 h1).trans (fa₂ x))))))
  -- the vertices `t₁, t₂`
  have key : ∀ t s, t ≠ a → t ≠ b → c.IsFree t α → c.IsFree t τ → c.IsFree t μ →
      c.IsFree t ζ → c.IsFree t ξ → c.col s t = some γ →
      c₂.IsFree t β ∧ c₂.col s t = some γ ∧ c₇.IsFree t β ∧ c₇.col s t = some γ ∧
      c₈.IsFree t α ∧ c₈.IsFree t β ∧ c₈.IsFree t τ ∧ c₈.IsFree t μ ∧
      c₈.col s t = some γ := by
    intro t s ta tb hα hτ hμ hζ hξ hst
    have n2 := ab_off hG cm τa βb (Or.inl hτ) ta tb
    have β2 : c₂.IsFree t β := (cfree_flip₁ c n2).2 hτ
    have kt2 : ∀ x, x ≠ τ → x ≠ β → c.IsFree t x → c₂.IsFree t x :=
      fun x h1 h2 h => (cfree_of_ne c h1 h2).2 h
    have st2 : c₂.col s t = some γ := ccol_keep c hst (Or.inl ⟨hτγ.symm, hγβ⟩)
    have n3 := ab_off hG cm₂ γa₂ βb₂ (Or.inr β2) ta tb
    have st3 := ab_keep_t hG cm₂ γa₂ βb₂ (Or.inr β2) ta tb st2
    have ζ3 : c₃.IsFree t ζ := (kfree_off c₂ n3 ζ).2 (kt2 ζ hζτ hζβ hζ)
    have n4 := ab_off hG cm₃ ζa₃ γb₃ (Or.inl ζ3) ta tb
    have st4 := ab_keep_t hG cm₃ ζa₃ γb₃ (Or.inl ζ3) ta tb st3
    have ζ4 : c₄.IsFree t ζ := (kfree_off c₃ n4 ζ).2 ζ3
    have n5 := ab_off hG cm₄ τa₄ ζb₄ (Or.inr ζ4) ta tb
    have τ5 : c₅.IsFree t τ := (cfree_flip₂ c₄ n5).2 ζ4
    have st5 : c₅.col s t = some γ := ccol_keep c₄ st4 (Or.inl ⟨hτγ.symm, hζγ.symm⟩)
    have tr5 : ∀ x, x ≠ τ → x ≠ ζ → c₂.IsFree t x → c₅.IsFree t x := fun x h1 h2 h =>
      (cfree_of_ne c₄ h1 h2).2 ((kfree_off c₃ n4 x).2 ((kfree_off c₂ n3 x).2 h))
    have ξ5 : c₅.IsFree t ξ := tr5 ξ hξτ hζξ.symm (kt2 ξ hξτ hξβ hξ)
    have n6 := ab_off hG cm₅ ξa₅ ζb₅ (Or.inl ξ5) ta tb
    have st6 := ab_keep_t hG cm₅ ξa₅ ζb₅ (Or.inl ξ5) ta tb st5
    have ξ6 : c₆.IsFree t ξ := (kfree_off c₅ n6 ξ).2 ξ5
    have n7 := ab_off hG cm₆ γa₆ ξb₆ (Or.inr ξ6) ta tb
    have st7 := ab_keep_t hG cm₆ γa₆ ξb₆ (Or.inr ξ6) ta tb st6
    have tr7 : ∀ x, c₅.IsFree t x → c₇.IsFree t x := fun x h =>
      (kfree_off c₆ n7 x).2 ((kfree_off c₅ n6 x).2 h)
    have β7 : c₇.IsFree t β := tr7 β (tr5 β hτβ.symm hζβ.symm β2)
    have n8 := ab_off hG cm₇ βa₇ γb₇ (Or.inl β7) ta tb
    have st8 := ab_keep_t hG cm₇ βa₇ γb₇ (Or.inl β7) ta tb st7
    have tr8 : ∀ x, c₅.IsFree t x → c₈.IsFree t x := fun x h => (kfree_off c₇ n8 x).2 (tr7 x h)
    exact ⟨β2, st2, β7, st7, tr8 α (tr5 α hατ hζα.symm (kt2 α hατ hαβ hα)),
      (kfree_off c₇ n8 β).2 β7, tr8 τ τ5, tr8 μ (tr5 μ hμτ hζμ.symm (kt2 μ hμτ hμβ hμ)), st8⟩
  obtain ⟨β₁2, st₁2, β₁7, st₁7, α₁8, β₁8, τ₁8, μ₁8, st₁8⟩ :=
    key t₁ s₁ d.at₁.symm d.bt₁.symm α₁ τ₁ μ₁ ζ₁ ξ₁ hst₁
  obtain ⟨β₂2, st₂2, β₂7, st₂7, α₂8, β₂8, τ₂8, μ₂8, st₂8⟩ :=
    key t₂ s₂ d.at₂.symm d.bt₂.symm α₂ τ₂ μ₂ ζ₂ ξ₂ hst₂
  -- the edges `us₁, us₂`
  have usk : ∀ s t ρ, t ≠ a → t ≠ b → ρ ≠ τ → ρ ≠ ζ → ρ ≠ ξ → ρ ≠ γ → c.col u s = some ρ →
      c₂.IsFree t β → c₂.col s t = some γ → c₇.IsFree t β → c₇.col s t = some γ →
      c₈.col u s = some ρ := by
    intro s t ρ ta tb h1 h2 h3 h4 hus h2t h2s h7t h7s
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
  have us₁8 := usk s₁ t₁ ρ₁ d.at₁.symm d.bt₁.symm hρ₁τ hρ₁ζ hρ₁ξ hρ₁γ hus₁ β₁2 st₁2 β₁7 st₁7
  have us₂8 := usk s₂ t₂ ρ₂ d.at₂.symm d.bt₂.symm hρ₂τ hρ₂ζ hρ₂ξ hρ₂γ hus₂ β₂2 st₂2 β₂7 st₂7
  exact ⟨c₈, ⟨cm₈, βb₈, acc₈, hbu₈, (fall α hαβ hαγ hζα.symm hξα.symm).2 αa, hcu₈,
    (fall τ hτβ hτγ hζτ.symm hξτ.symm).2 τa, st₁8, st₂8, γa₈, α₁8, α₂8, β₁8, β₂8, τ₁8, τ₂8⟩,
    μ₁8, μ₂8, us₁8, us₂8, fall⟩

end Overfull
