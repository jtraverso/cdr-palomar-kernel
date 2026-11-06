/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Kite0C

/-!
# Kites without `c`, part D: Chen–Cao Lemma 4.2 (robust form)

`Kite0Prop G`: there is no kite without `c` (`K = (a, b, u, s₁, t₁)` and `K* = (a, b, u, s₂, t₂)`
Kierstead paths with all path colours in `A`, `φ(s₁t₁) = φ(s₂t₂)`) when `d(b) = Δ` and, in every
colouring of `G − ab`, at least five colours missing at `a` are missing at both `t₁` and `t₂`
(`Robust5`).

The proof is that of `kiteProp` (`KiteE`–`KiteG`) with `α = φ(bu)` in the role of `φ(cu)`, and
`KNF0.false` (with Chen–Cao's closing argument `z_close`) in place of `KNF.false`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In every colouring of `G − ab`, any four colours can be avoided by a colour missing at `a`,
`t₁` and `t₂`. -/
def Robust5 (G : SimpleGraph V) [DecidableRel G.Adj] (a b t₁ t₂ : V) : Prop :=
  ∀ ψ : PEC G (Fin G.maxDegree), IsColMinus ψ a b → ∀ S : Finset (Fin G.maxDegree), #S ≤ 4 →
    ∃ θ, θ ∉ S ∧ ψ.IsFree a θ ∧ ψ.IsFree t₁ θ ∧ ψ.IsFree t₂ θ

theorem Robust5.swap {a b t₁ t₂ : V} (h : Robust5 G a b t₁ t₂) : Robust5 G a b t₂ t₁ := by
  intro ψ hψ S hS
  obtain ⟨θ, h1, h2, h3, h4⟩ := h ψ hψ S hS
  exact ⟨θ, h1, h2, h4, h3⟩

theorem Robust5.two {a b t₁ t₂ : V} (h : Robust5 G a b t₁ t₂) {ψ : PEC G (Fin G.maxDegree)}
    (hψ : IsColMinus ψ a b) (x₁ x₂ x₃ : Fin G.maxDegree) :
    ∃ ζ ξ, ψ.IsFree a ζ ∧ ψ.IsFree t₁ ζ ∧ ψ.IsFree t₂ ζ ∧ ψ.IsFree a ξ ∧ ψ.IsFree t₁ ξ ∧
      ψ.IsFree t₂ ξ ∧ ζ ≠ x₁ ∧ ζ ≠ x₂ ∧ ζ ≠ x₃ ∧ ξ ≠ x₁ ∧ ξ ≠ x₂ ∧ ξ ≠ x₃ ∧ ζ ≠ ξ := by
  obtain ⟨ζ, hζ, z1, z2, z3⟩ := h ψ hψ {x₁, x₂, x₃} (card_le_three.trans (by omega))
  obtain ⟨ξ, hξ, y1, y2, y3⟩ := h ψ hψ {x₁, x₂, x₃, ζ} card_le_four
  simp only [mem_insert, mem_singleton, not_or] at hζ hξ
  obtain ⟨e1, e2, e3⟩ := hζ
  obtain ⟨f1, f2, f3, f4⟩ := hξ
  exact ⟨ζ, ξ, z1, z2, z3, y1, y2, y3, e1, e2, e3, f1, f2, f3, fun e => f4 e.symm⟩

set_option maxHeartbeats 1600000 in
/-- **Making `t₁, t₂` miss the colour of `us₂`** (without `c`). -/
theorem proc0 (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u s₁ s₂ t₁ t₂ : V}
    (d : Distinct7 a b u s₁ s₂ t₁ t₂) {β α γ μ ν ζ ξ : Fin G.maxDegree}
    (h : KS0 c a b u s₁ s₂ t₁ t₂ β α γ) (hus₂ : c.col u s₂ = some μ) (μa : c.IsFree a μ)
    (hus₁ : c.col u s₁ = some ν) (ζa : c.IsFree a ζ) (ζ₁ : c.IsFree t₁ ζ) (ζ₂ : c.IsFree t₂ ζ)
    (ξa : c.IsFree a ξ) (ξ₁ : c.IsFree t₁ ξ) (ξ₂ : c.IsFree t₂ ξ) (hζα : ζ ≠ α) (hζμ : ζ ≠ μ)
    (hζν : ζ ≠ ν) (hξα : ξ ≠ α) (hξμ : ξ ≠ μ) (hξν : ξ ≠ ν) (hζξ : ζ ≠ ξ) :
    ∃ c' : PEC G (Fin G.maxDegree), KS0 c' a b u s₁ s₂ t₁ t₂ β α γ ∧ c'.IsFree t₁ μ ∧
      c'.IsFree t₂ μ ∧ (∀ x, x ≠ β → x ≠ γ → x ≠ ζ → x ≠ ξ → (c'.IsFree a x ↔ c.IsFree a x)) ∧
      ((c'.col u s₂ = some μ ∧ c'.col u s₁ = some ν) ∨
        (c'.col u s₂ = some β ∧ c'.col u s₁ = some (Equiv.swap μ β ν))) := by
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have nb : ∀ {x}, c.IsFree a x → x ≠ β := fun hx e => hdis _ hx (e ▸ h.βb)
  have hμβ := nb μa
  have hαβ := nb h.αa
  have hζβ := nb ζa
  have hξβ := nb ξa
  have hγμ : γ ≠ μ := fun e => d.ut₂ (c.col_proper (by rw [c.col_symm]; exact hus₂)
    (by rw [← e]; exact h.hst₂))
  have hνμ : ν ≠ μ := fun e => d.s₁s₂ (c.col_proper hus₁ (e ▸ hus₂))
  have hαμ : α ≠ μ := fun e => d.bs₂ (c.col_proper (by rw [c.col_symm]; exact h.hbu) (e ▸ hus₂))
  -- switch `μ, β` off the `a`–`b` chain
  have r1b : (c.kempeGraph μ β).Reachable a b := ksAB_link hG h.cm μa h.βb
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
  have hbu₁ : c₁.col b u = some α := by rw [k1 b u r1b]; exact h.hbu
  have hst₁₁ : c₁.col s₁ t₁ = some γ := ccol_keep c h.hst₁ (Or.inl ⟨hγμ, nb h.γa⟩)
  have hst₂₁ : c₁.col s₂ t₂ = some γ := ccol_keep c h.hst₂ (Or.inl ⟨hγμ, nb h.γa⟩)
  have μ₁ : c₁.IsFree t₁ μ := (cfree_flip₂ c n1₁).2 h.β₁
  have μ₂ : c₁.IsFree t₂ μ := (cfree_flip₂ c n1₂).2 h.β₂
  have tail : ∀ ρ₁ ρ₂, c₁.col u s₁ = some ρ₁ → c₁.col u s₂ = some ρ₂ → ρ₁ ≠ ζ →
      ρ₁ ≠ ξ → ρ₂ ≠ ζ → ρ₂ ≠ ξ →
      ∃ c' : PEC G (Fin G.maxDegree), KS0 c' a b u s₁ s₂ t₁ t₂ β α γ ∧ c'.IsFree t₁ μ ∧
        c'.IsFree t₂ μ ∧ c'.col u s₁ = some ρ₁ ∧ c'.col u s₂ = some ρ₂ ∧
        (∀ x, x ≠ β → x ≠ γ → x ≠ ζ → x ≠ ξ → (c'.IsFree a x ↔ c.IsFree a x)) := by
    intro ρ₁ ρ₂ u1 u2 h1 h2 h3 h4
    obtain ⟨c', hc', m1, m2, v1, v2, hf⟩ := proc_tail0 hG d cm₁ βb₁ hbu₁ ((fa₁ α).2 h.αa)
      hst₁₁ hst₂₁ ((fa₁ γ).2 h.γa) (kt hαμ hαβ h.α₁) (kt hαμ hαβ h.α₂) μ₁ μ₂ ((fa₁ μ).2 μa)
      ((fa₁ ζ).2 ζa) (kt hζμ hζβ ζ₁) (kt hζμ hζβ ζ₂) ((fa₁ ξ).2 ξa) (kt hξμ hξβ ξ₁)
      (kt hξμ hξβ ξ₂) u1 u2 h1 h2 h3 h4 hαμ.symm hζα hζμ hξα hξμ hζξ
    exact ⟨c', hc', m1, m2, v1, v2, fun x e1 e2 e3 e4 => (hf x e1 e2 e3 e4).trans (fa₁ x)⟩
  by_cases hu : (c.kempeGraph μ β).Reachable a u
  · obtain ⟨c', hc', m1, m2, v1, v2, hf⟩ := tail ν μ (by rw [k1 u s₁ hu]; exact hus₁)
      (by rw [k1 u s₂ hu]; exact hus₂) hζν.symm hξν.symm hζμ.symm hξμ.symm
    exact ⟨c', hc', m1, m2, hf, Or.inl ⟨v2, v1⟩⟩
  · have u2 : c₁.col u s₂ = some β := ccol_flip₁ c hus₂ hu
    have u1 : c₁.col u s₁ = some (Equiv.swap μ β ν) := by
      rw [kempeSwapCompl_col_of_not_reachable c μ β hu, hus₁]; rfl
    have hs : Equiv.swap μ β ν ≠ ζ ∧ Equiv.swap μ β ν ≠ ξ := by
      by_cases e : ν = β
      · rw [e, Equiv.swap_apply_right]; exact ⟨hζμ.symm, hξμ.symm⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hνμ e]; exact ⟨hζν.symm, hξν.symm⟩
    obtain ⟨c', hc', m1, m2, v1, v2, hf⟩ := tail _ β u1 u2 hs.1 hs.2 hζβ.symm hξβ.symm
    exact ⟨c', hc', m1, m2, hf, Or.inr ⟨v2, v1⟩⟩

/-- **One edge `usᵢ` coloured `β`** (without `c`). -/
theorem p5_0 (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u s₁ s₂ t₁ t₂ : V}
    (d : Distinct7 a b u s₁ s₂ t₁ t₂) (hR : Robust5 G a b t₁ t₂) {β α γ μ : Fin G.maxDegree}
    (h : KS0 c a b u s₁ s₂ t₁ t₂ β α γ) (hus₁ : c.col u s₁ = some β)
    (hus₂ : c.col u s₂ = some μ) (μa : c.IsFree a μ) : False := by
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have nb : ∀ {x}, c.IsFree a x → x ≠ β := fun hx e => hdis _ hx (e ▸ h.βb)
  have hγμ : γ ≠ μ := fun e => d.ut₂ (c.col_proper (by rw [c.col_symm]; exact hus₂)
    (by rw [← e]; exact h.hst₂))
  obtain ⟨ζ, ξ, z1, z2, z3, y1, y2, y3, hζα, hζμ, -, hξα, hξμ, -, hζξ⟩ := hR.two h.cm α μ μ
  obtain ⟨c', hc', m1, m2, hf, hcase⟩ := proc0 hG d h hus₂ μa hus₁ z1 z2 z3 y1 y2 y3 hζα hζμ
    (nb z1) hξα hξμ (nb y1) hζξ
  have μa' : c'.IsFree a μ := (hf μ (nb μa) hγμ.symm hζμ.symm hξμ.symm).2 μa
  rcases hcase with ⟨v2, v1⟩ | ⟨v2, v1⟩
  · exact KNF0.false hG ⟨d, hc'.cm, hc'.βb, hc'.hbu, hc'.αa, v1, v2, μa', hc'.hst₁, hc'.hst₂,
      hc'.γa, hc'.α₁, hc'.α₂, hc'.β₁, hc'.β₂, m1, m2⟩
  · rw [Equiv.swap_apply_right] at v1
    exact KNF0.false hG ⟨d.swap, hc'.cm, hc'.βb, hc'.hbu, hc'.αa, v2, v1, μa', hc'.hst₂,
      hc'.hst₁, hc'.γa, hc'.α₂, hc'.α₁, hc'.β₂, hc'.β₁, m2, m1⟩

set_option maxHeartbeats 1600000 in
/-- **The kite state without `c` is impossible.** -/
theorem ks0_false (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u s₁ s₂ t₁ t₂ : V}
    (d : Distinct7 a b u s₁ s₂ t₁ t₂) (db : G.degree b = G.maxDegree)
    (hR : Robust5 G a b t₁ t₂) {β α γ : Fin G.maxDegree} (h : KS0 c a b u s₁ s₂ t₁ t₂ β α γ)
    (g₁ : Good c a b u s₁) (g₂ : Good c a b u s₂) : False := by
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have nb : ∀ {x}, c.IsFree a x → x ≠ β := fun hx e => hdis _ hx (e ▸ h.βb)
  have toA : ∀ {x}, InA c a b x → x ≠ β → c.IsFree a x := fun hx hne =>
    hx.resolve_right fun hb => hne (h.cm.b_only db h.βb hb)
  obtain ⟨ν₁, hus₁, hν₁A⟩ := g₁
  obtain ⟨ν₂, hus₂, hν₂A⟩ := g₂
  have hν : ν₁ ≠ ν₂ := fun e => d.s₁s₂ (c.col_proper hus₁ (e ▸ hus₂))
  by_cases e1 : ν₁ = β
  · exact p5_0 hG d hR h (e1 ▸ hus₁) hus₂ (toA hν₂A (fun e => hν (e1.trans e.symm)))
  by_cases e2 : ν₂ = β
  · exact p5_0 hG d.swap hR.swap h.swap (e2 ▸ hus₂) hus₁ (toA hν₁A e1)
  have ν₁a := toA hν₁A e1
  have ν₂a := toA hν₂A e2
  have ng : ∀ {x}, c.IsFree t₁ x → x ≠ γ := fun hx e => hx s₁ (by rw [c.col_symm, h.hst₁, e])
  have hν₁γ : ν₁ ≠ γ := fun e => d.ut₁ (c.col_proper (by rw [c.col_symm]; exact hus₁)
    (by rw [e]; exact h.hst₁))
  have hν₂γ : ν₂ ≠ γ := fun e => d.ut₂ (c.col_proper (by rw [c.col_symm]; exact hus₂)
    (by rw [e]; exact h.hst₂))
  have hαν₂ : α ≠ ν₂ := fun e => d.bs₂ (c.col_proper (by rw [c.col_symm]; exact h.hbu)
    (e ▸ hus₂))
  have hαγ := ng h.α₁
  have hαβ := nb h.αa
  obtain ⟨ζ, ξ, z1, z2, z3, y1, y2, y3, hζα, hζν₂, hζν₁, hξα, hξν₂, hξν₁, hζξ⟩ :=
    hR.two h.cm α ν₂ ν₁
  obtain ⟨c₁, h₁, m1, m2, hf, hcase⟩ := proc0 hG d h hus₂ ν₂a hus₁ z1 z2 z3 y1 y2 y3 hζα
    hζν₂ hζν₁ hξα hξν₂ hξν₁ hζξ
  have ν₁a₁ : c₁.IsFree a ν₁ := (hf ν₁ e1 hν₁γ hζν₁.symm hξν₁.symm).2 ν₁a
  rcases hcase with ⟨v2, v1⟩ | ⟨v2, v1⟩
  swap
  · rw [Equiv.swap_apply_of_ne_of_ne hν e1] at v1
    exact p5_0 hG d.swap hR.swap h₁.swap v2 v1 ν₁a₁
  -- make `ν₂` the colour missing at `b`: the `a`–`b` swaps `(γ, β)` and `(ν₂, γ)`
  have ν₂a₁ : c₁.IsFree a ν₂ := (hf ν₂ e2 hν₂γ hζν₂.symm hξν₂.symm).2 ν₂a
  have cm₁ := h₁.cm
  set c₂ := c₁.kempeSwap γ β a with hc₂
  have cm₂ : IsColMinus c₂ a b := cm₁.kempeSwap γ β a
  have γb₂ : c₂.IsFree b γ := ksAB_free_b hG cm₁ h₁.γa h₁.βb
  have fa₂ : ∀ x, x ≠ γ → x ≠ β → (c₂.IsFree a x ↔ c₁.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₁ h₁.γa h₁.βb h1 h2
  have hbu₂ : c₂.col b u = some α := kcol_keep c₁ h₁.hbu (Or.inl ⟨hαγ, hαβ⟩)
  have us₁₂ : c₂.col u s₁ = some ν₁ := kcol_keep c₁ v1 (Or.inl ⟨hν₁γ, e1⟩)
  have us₂₂ : c₂.col u s₂ = some ν₂ := kcol_keep c₁ v2 (Or.inl ⟨hν₂γ, e2⟩)
  have n2₁ := ab_off hG cm₁ h₁.γa h₁.βb (Or.inr h₁.β₁) d.at₁.symm d.bt₁.symm
  have n2₂ := ab_off hG cm₁ h₁.γa h₁.βb (Or.inr h₁.β₂) d.at₂.symm d.bt₂.symm
  have st₁₂ := ab_keep_t hG cm₁ h₁.γa h₁.βb (Or.inr h₁.β₁) d.at₁.symm d.bt₁.symm h₁.hst₁
  have st₂₂ := ab_keep_t hG cm₁ h₁.γa h₁.βb (Or.inr h₁.β₂) d.at₂.symm d.bt₂.symm h₁.hst₂
  have ν₂a₂ : c₂.IsFree a ν₂ := (fa₂ ν₂ hν₂γ e2).2 ν₂a₁
  have ν₂t₁ : c₂.IsFree t₁ ν₂ := (kfree_off c₁ n2₁ ν₂).2 m1
  have ν₂t₂ : c₂.IsFree t₂ ν₂ := (kfree_off c₁ n2₂ ν₂).2 m2
  set c₃ := c₂.kempeSwap ν₂ γ a with hc₃
  have cm₃ : IsColMinus c₃ a b := cm₂.kempeSwap ν₂ γ a
  have fa₃ : ∀ x, x ≠ ν₂ → x ≠ γ → (c₃.IsFree a x ↔ c₂.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₂ ν₂a₂ γb₂ h1 h2
  have n3₁ := ab_off hG cm₂ ν₂a₂ γb₂ (Or.inl ν₂t₁) d.at₁.symm d.bt₁.symm
  have n3₂ := ab_off hG cm₂ ν₂a₂ γb₂ (Or.inl ν₂t₂) d.at₂.symm d.bt₂.symm
  have ft₁ : ∀ x, c₁.IsFree t₁ x → c₃.IsFree t₁ x := fun x hx =>
    (kfree_off c₂ n3₁ x).2 ((kfree_off c₁ n2₁ x).2 hx)
  have ft₂ : ∀ x, c₁.IsFree t₂ x → c₃.IsFree t₂ x := fun x hx =>
    (kfree_off c₂ n3₂ x).2 ((kfree_off c₁ n2₂ x).2 hx)
  have fa : ∀ x, x ≠ ν₂ → x ≠ γ → x ≠ β → c₁.IsFree a x → c₃.IsFree a x := fun x h1 h2 h3 hx =>
    (fa₃ x h1 h2).2 ((fa₂ x h2 h3).2 hx)
  have ks₃ : KS0 c₃ a b u s₁ s₂ t₁ t₂ ν₂ α γ :=
    ⟨cm₃, ksAB_free_b hG cm₂ ν₂a₂ γb₂, kcol_keep c₂ hbu₂ (Or.inl ⟨hαν₂, hαγ⟩),
      fa α hαν₂ hαγ hαβ h₁.αa,
      ab_keep_t hG cm₂ ν₂a₂ γb₂ (Or.inl ν₂t₁) d.at₁.symm d.bt₁.symm st₁₂,
      ab_keep_t hG cm₂ ν₂a₂ γb₂ (Or.inl ν₂t₂) d.at₂.symm d.bt₂.symm st₂₂,
      ksAB_free_a hG cm₂ ν₂a₂ γb₂, ft₁ α h₁.α₁, ft₂ α h₁.α₂, ft₁ ν₂ m1, ft₂ ν₂ m2⟩
  exact p5_0 hG d.swap hR.swap ks₃.swap
    (ab_keep_us' hG cm₂ ν₂a₂ γb₂ ν₂t₂ d.at₂.symm d.bt₂.symm st₂₂ us₂₂)
    (kcol_keep c₂ us₁₂ (Or.inl ⟨hν, hν₁γ⟩)) (fa ν₁ hν hν₁γ e1 ν₁a₁)

set_option maxHeartbeats 4000000 in
/-- **A kite without `c` is impossible.** -/
theorem kite0_false (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u s₁ s₂ t₁ t₂ : V}
    (d : Distinct7 a b u s₁ s₂ t₁ t₂) (db : G.degree b = G.maxDegree) (hR : Robust5 G a b t₁ t₂)
    (cm : IsColMinus c a b) (hbu : ∃ δ, c.col b u = some δ ∧ c.IsFree a δ)
    (g₁ : Good c a b u s₁) (gst₁ : Good c a b s₁ t₁) (g₂ : Good c a b u s₂)
    (heq : c.col s₁ t₁ = c.col s₂ t₂) : False := by
  obtain ⟨α₀, hbu₀, α₀a⟩ := hbu
  obtain ⟨γ₀, hst₁, γ₀A⟩ := gst₁
  obtain ⟨β₀, β₀b⟩ := cm.exists_free_right
  have hst₂ : c.col s₂ t₂ = some γ₀ := by rw [← heq]; exact hst₁
  have dis : ∀ {ψ : PEC G (Fin G.maxDegree)}, IsColMinus ψ a b → ∀ {x y}, ψ.IsFree a x →
      ψ.IsFree b y → x ≠ y := fun hψ x y ha hb e => (hψ.ab_facts hG).1 x ha (e ▸ hb)
  have ng : ∀ {ψ : PEC G (Fin G.maxDegree)} {x}, ψ.col s₁ t₁ = some γ₀ → ψ.IsFree t₁ x →
      x ≠ γ₀ := fun hs hx e => hx s₁ (by rw [PEC.col_symm, hs, e])
  -- step 1: the `a`–`b` swap `(θ₁, β₀)`
  obtain ⟨θ₁, -, θ₁a, θ₁t₁, θ₁t₂⟩ := hR c cm ∅ (by simp)
  have l1 := ksAB_link hG cm θ₁a β₀b
  set c₁ := c.kempeSwap θ₁ β₀ a with hc₁
  have cm₁ : IsColMinus c₁ a b := cm.kempeSwap θ₁ β₀ a
  have θ₁b₁ : c₁.IsFree b θ₁ := ksAB_free_b hG cm θ₁a β₀b
  have A₁ := ksAB_inA hG cm θ₁a β₀b
  have n1₁ := ab_off hG cm θ₁a β₀b (Or.inl θ₁t₁) d.at₁.symm d.bt₁.symm
  have n1₂ := ab_off hG cm θ₁a β₀b (Or.inl θ₁t₂) d.at₂.symm d.bt₂.symm
  have hst₁₁ := ab_keep_t hG cm θ₁a β₀b (Or.inl θ₁t₁) d.at₁.symm d.bt₁.symm hst₁
  have hst₂₁ := ab_keep_t hG cm θ₁a β₀b (Or.inl θ₁t₂) d.at₂.symm d.bt₂.symm hst₂
  have hγθ₁ := (ng hst₁ θ₁t₁).symm
  have γa₁ : c₁.IsFree a γ₀ := ((A₁ γ₀).2 γ₀A).resolve_right fun hb =>
    hγθ₁ (cm₁.b_only db θ₁b₁ hb)
  obtain ⟨α₁, hbu₁, α₁a⟩ : ∃ x, c₁.col b u = some x ∧ c₁.IsFree a x := by
    by_cases e : α₀ = θ₁
    · exact ⟨β₀, kcol_flip₁ c (e ▸ hbu₀) l1, ksAB_free_a hG cm θ₁a β₀b⟩
    · exact ⟨α₀, kcol_keep c hbu₀ (Or.inl ⟨e, dis cm α₀a β₀b⟩),
        (ksAB_free_a_of_ne hG cm θ₁a β₀b e (dis cm α₀a β₀b)).2 α₀a⟩
  have g₁₁ := good_kempeSwap a (Or.inl θ₁a) (Or.inr β₀b) A₁ g₁
  have g₂₁ := good_kempeSwap a (Or.inl θ₁a) (Or.inr β₀b) A₁ g₂
  have θ₁t₁₁ := (kfree_off c n1₁ θ₁).2 θ₁t₁
  have θ₁t₂₁ := (kfree_off c n1₂ θ₁).2 θ₁t₂
  -- step 2: the `a`–`b` swap `(α₁, θ₁)`: `bu` becomes `θ₁`
  have hα₁θ₁ := dis cm₁ α₁a θ₁b₁
  set c₂ := c₁.kempeSwap α₁ θ₁ a with hc₂
  have cm₂ : IsColMinus c₂ a b := cm₁.kempeSwap α₁ θ₁ a
  have α₁b₂ : c₂.IsFree b α₁ := ksAB_free_b hG cm₁ α₁a θ₁b₁
  have θ₁a₂ : c₂.IsFree a θ₁ := ksAB_free_a hG cm₁ α₁a θ₁b₁
  have A₂ := ksAB_inA hG cm₁ α₁a θ₁b₁
  have hbu₂ : c₂.col b u = some θ₁ := kcol_flip₁ c₁ hbu₁ (ksAB_link hG cm₁ α₁a θ₁b₁)
  have n2₁ := ab_off hG cm₁ α₁a θ₁b₁ (Or.inr θ₁t₁₁) d.at₁.symm d.bt₁.symm
  have n2₂ := ab_off hG cm₁ α₁a θ₁b₁ (Or.inr θ₁t₂₁) d.at₂.symm d.bt₂.symm
  have hst₁₂ := ab_keep_t hG cm₁ α₁a θ₁b₁ (Or.inr θ₁t₁₁) d.at₁.symm d.bt₁.symm hst₁₁
  have hst₂₂ := ab_keep_t hG cm₁ α₁a θ₁b₁ (Or.inr θ₁t₂₁) d.at₂.symm d.bt₂.symm hst₂₁
  have g₁₂ := good_kempeSwap a (Or.inl α₁a) (Or.inr θ₁b₁) A₂ g₁₁
  have g₂₂ := good_kempeSwap a (Or.inl α₁a) (Or.inr θ₁b₁) A₂ g₂₁
  -- step 3: the `a`–`b` swap `(θ₂, α₁)`: `b` misses `θ₂`
  obtain ⟨θ₂, hθ₂S, θ₂a, θ₂t₁, θ₂t₂⟩ := hR c₂ cm₂ {θ₁} (by simp)
  have hθ₂θ₁ : θ₂ ≠ θ₁ := by simpa using hθ₂S
  have hγθ₂ := (ng hst₁₂ θ₂t₁).symm
  set c₃ := c₂.kempeSwap θ₂ α₁ a with hc₃
  have cm₃ : IsColMinus c₃ a b := cm₂.kempeSwap θ₂ α₁ a
  have A₃ := ksAB_inA hG cm₂ θ₂a α₁b₂
  have hθ₁α₁ := hα₁θ₁.symm
  have γa₃ : c₃.IsFree a γ₀ := by
    by_cases e : γ₀ = α₁
    · rw [e]; exact ksAB_free_a hG cm₂ θ₂a α₁b₂
    · exact (ksAB_free_a_of_ne hG cm₂ θ₂a α₁b₂ hγθ₂ e).2
        ((ksAB_free_a_of_ne hG cm₁ α₁a θ₁b₁ e hγθ₁).2 γa₁)
  have θ₁t₁₂ := (kfree_off c₁ n2₁ θ₁).2 θ₁t₁₁
  have θ₁t₂₂ := (kfree_off c₁ n2₂ θ₁).2 θ₁t₂₁
  have n3₁ := ab_off hG cm₂ θ₂a α₁b₂ (Or.inl θ₂t₁) d.at₁.symm d.bt₁.symm
  have n3₂ := ab_off hG cm₂ θ₂a α₁b₂ (Or.inl θ₂t₂) d.at₂.symm d.bt₂.symm
  have ks : KS0 c₃ a b u s₁ s₂ t₁ t₂ θ₂ θ₁ γ₀ :=
    ⟨cm₃, ksAB_free_b hG cm₂ θ₂a α₁b₂, kcol_keep c₂ hbu₂ (Or.inl ⟨hθ₂θ₁.symm, hθ₁α₁⟩),
      (ksAB_free_a_of_ne hG cm₂ θ₂a α₁b₂ hθ₂θ₁.symm hθ₁α₁).2 θ₁a₂,
      ab_keep_t hG cm₂ θ₂a α₁b₂ (Or.inl θ₂t₁) d.at₁.symm d.bt₁.symm hst₁₂,
      ab_keep_t hG cm₂ θ₂a α₁b₂ (Or.inl θ₂t₂) d.at₂.symm d.bt₂.symm hst₂₂, γa₃,
      (kfree_off c₂ n3₁ θ₁).2 θ₁t₁₂, (kfree_off c₂ n3₂ θ₁).2 θ₁t₂₂,
      (kfree_off c₂ n3₁ θ₂).2 θ₂t₁, (kfree_off c₂ n3₂ θ₂).2 θ₂t₂⟩
  exact ks0_false hG d db hR ks (good_kempeSwap a (Or.inl θ₂a) (Or.inr α₁b₂) A₃ g₁₂)
    (good_kempeSwap a (Or.inl θ₂a) (Or.inr α₁b₂) A₃ g₂₂)

/-- Chen–Cao Lemma 4.2 (kites without `c`), in robust form. -/
def Kite0Prop (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (c : PEC G (Fin G.maxDegree)) (a b u s₁ s₂ t₁ t₂ : V),
    [a, b, u, s₁, s₂, t₁, t₂].Nodup → IsColMinus c a b →
    (∃ δ, c.col b u = some δ ∧ c.IsFree a δ) → Good c a b u s₁ → Good c a b s₁ t₁ →
    Good c a b u s₂ → Good c a b s₂ t₂ → c.col s₁ t₁ = c.col s₂ t₂ →
    G.degree b = G.maxDegree → Robust5 G a b t₁ t₂ → False

/-- **Chen–Cao Lemma 4.2 (kites without `c`)**, in robust form. -/
theorem kite0Prop (hG : IsClassTwo G) : Kite0Prop G := by
  intro c a b u s₁ s₂ t₁ t₂ hnd cm hbu g₁ gst₁ g₂ _ heq db hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or, not_false_eq_true] at hnd
  obtain ⟨⟨ab, au, as₁, as₂, at₁, at₂⟩, ⟨bu, bs₁, bs₂, bt₁, bt₂⟩, ⟨us₁, us₂, ut₁, ut₂⟩,
    ⟨s₁s₂, s₁t₁, s₁t₂⟩, ⟨s₂t₁, s₂t₂⟩, t₁t₂⟩ := hnd
  exact kite0_false hG ⟨ab, au, as₁, as₂, at₁, at₂, bu, bs₁, bs₂, bt₁, bt₂, us₁, us₂, ut₁, ut₂,
    s₁s₂, s₁t₁, s₁t₂, s₂t₁, s₂t₂, t₁t₂⟩ db hR cm hbu g₁ gst₁ g₂ heq

end Overfull
