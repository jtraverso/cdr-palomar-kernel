/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.KiteE

/-!
# Kites, part F: the kite state is impossible

`ks_false`: with `d(b) = Δ` and `Robust`, the kite state `KS` with `us₁, us₂` coloured in `A` is
impossible.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Robust.swap {a b t₁ t₂ : V} (h : Robust G a b t₁ t₂) : Robust G a b t₂ t₁ := by
  intro ψ hψ S hS
  obtain ⟨θ, h1, h2, h3, h4⟩ := h ψ hψ S hS
  exact ⟨θ, h1, h2, h4, h3⟩

/-- Two fresh colours avoiding four given ones. -/
theorem Robust.two {a b t₁ t₂ : V} (h : Robust G a b t₁ t₂) {ψ : PEC G (Fin G.maxDegree)}
    (hψ : IsColMinus ψ a b) (x₁ x₂ x₃ x₄ : Fin G.maxDegree) :
    ∃ ζ ξ, ψ.IsFree a ζ ∧ ψ.IsFree t₁ ζ ∧ ψ.IsFree t₂ ζ ∧ ψ.IsFree a ξ ∧ ψ.IsFree t₁ ξ ∧
      ψ.IsFree t₂ ξ ∧ ζ ≠ x₁ ∧ ζ ≠ x₂ ∧ ζ ≠ x₃ ∧ ζ ≠ x₄ ∧ ξ ≠ x₁ ∧ ξ ≠ x₂ ∧ ξ ≠ x₃ ∧
      ξ ≠ x₄ ∧ ζ ≠ ξ := by
  obtain ⟨ζ, hζ, z1, z2, z3⟩ := h ψ hψ {x₁, x₂, x₃, x₄} (card_le_four.trans (by omega))
  obtain ⟨ξ, hξ, y1, y2, y3⟩ := h ψ hψ {x₁, x₂, x₃, x₄, ζ}
    (card_le_five.trans (by omega))
  simp only [mem_insert, mem_singleton, not_or] at hζ hξ
  obtain ⟨e1, e2, e3, e4⟩ := hζ
  obtain ⟨f1, f2, f3, f4, f5⟩ := hξ
  exact ⟨ζ, ξ, z1, z2, z3, y1, y2, y3, e1, e2, e3, e4, f1, f2, f3, f4, fun e => f5 e.symm⟩

/-- **One edge `usᵢ` coloured `β`.** -/
theorem p5 (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b cc u s₁ s₂ t₁ t₂ : V}
    (hd : D8 a b cc u s₁ s₂ t₁ t₂) (hR : Robust G a b t₁ t₂) {β α τ γ μ : Fin G.maxDegree}
    (h : KS c a b cc u s₁ s₂ t₁ t₂ β α τ γ) (hus₁ : c.col u s₁ = some β)
    (hus₂ : c.col u s₂ = some μ) (μa : c.IsFree a μ) : False := by
  have d := hd.d7
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have nb : ∀ {x}, c.IsFree a x → x ≠ β := fun hx e => hdis _ hx (e ▸ h.βb)
  have hγμ : γ ≠ μ := fun e => d.ut₂ (c.col_proper (by rw [c.col_symm]; exact hus₂)
    (by rw [← e]; exact h.hst₂))
  obtain ⟨ζ, ξ, z1, z2, z3, y1, y2, y3, hζα, hζτ, hζμ, -, hξα, hξτ, hξμ, -, hζξ⟩ :=
    hR.two h.cm α τ μ μ
  obtain ⟨c', hc', m1, m2, hf, hcase⟩ := proc hG hd h hus₂ μa hus₁ z1 z2 z3 y1 y2 y3 hζα hζτ hζμ
    (nb z1) hξα hξτ hξμ (nb y1) hζξ
  have μa' : c'.IsFree a μ := (hf μ (nb μa) hγμ.symm hζμ.symm hξμ.symm).2 μa
  rcases hcase with ⟨v2, v1⟩ | ⟨v2, v1⟩
  · exact KNF.false hG ⟨d, hd.acc, hd.bcc, hd.ccu, hd.ccs₁, hd.ccs₂, hd.cct₁, hd.cct₂, hc'.cm,
      hc'.βb, hc'.acc, hc'.hbu, hc'.αa, hc'.hcu, hc'.τa, v1, v2, μa', hc'.hst₁, hc'.hst₂, hc'.γa,
      hc'.α₁, hc'.α₂, hc'.β₁, hc'.β₂, hc'.τ₁, hc'.τ₂, m2⟩
  · rw [Equiv.swap_apply_right] at v1
    exact KNF.false hG ⟨d.swap, hd.acc, hd.bcc, hd.ccu, hd.ccs₂, hd.ccs₁, hd.cct₂, hd.cct₁,
      hc'.cm, hc'.βb, hc'.acc, hc'.hbu, hc'.αa, hc'.hcu, hc'.τa, v2, v1, μa', hc'.hst₂, hc'.hst₁,
      hc'.γa, hc'.α₂, hc'.α₁, hc'.β₂, hc'.β₁, hc'.τ₂, hc'.τ₁, m1⟩

set_option maxHeartbeats 1600000 in
/-- **The kite state is impossible.** -/
theorem ks_false (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b cc u s₁ s₂ t₁ t₂ : V}
    (hd : D8 a b cc u s₁ s₂ t₁ t₂) (db : G.degree b = G.maxDegree) (hR : Robust G a b t₁ t₂)
    {β α τ γ : Fin G.maxDegree} (h : KS c a b cc u s₁ s₂ t₁ t₂ β α τ γ)
    (g₁ : Good c a b u s₁) (g₂ : Good c a b u s₂) : False := by
  have d := hd.d7
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have nb : ∀ {x}, c.IsFree a x → x ≠ β := fun hx e => hdis _ hx (e ▸ h.βb)
  have toA : ∀ {x}, InA c a b x → x ≠ β → c.IsFree a x := fun hx hne =>
    hx.resolve_right fun hb => hne (h.cm.b_only db h.βb hb)
  obtain ⟨ν₁, hus₁, hν₁A⟩ := g₁
  obtain ⟨ν₂, hus₂, hν₂A⟩ := g₂
  have hν : ν₁ ≠ ν₂ := fun e => d.s₁s₂ (c.col_proper hus₁ (e ▸ hus₂))
  by_cases e1 : ν₁ = β
  · exact p5 hG hd hR h (e1 ▸ hus₁) hus₂ (toA hν₂A (fun e => hν (e1.trans e.symm)))
  by_cases e2 : ν₂ = β
  · exact p5 hG hd.swap hR.swap h.swap (e2 ▸ hus₂) hus₁ (toA hν₁A e1)
  have ν₁a := toA hν₁A e1
  have ν₂a := toA hν₂A e2
  have ng : ∀ {x}, c.IsFree t₁ x → x ≠ γ := fun hx e => hx s₁ (by rw [c.col_symm, h.hst₁, e])
  have hν₁γ : ν₁ ≠ γ := fun e => d.ut₁ (c.col_proper (by rw [c.col_symm]; exact hus₁)
    (by rw [e]; exact h.hst₁))
  have hν₂γ : ν₂ ≠ γ := fun e => d.ut₂ (c.col_proper (by rw [c.col_symm]; exact hus₂)
    (by rw [e]; exact h.hst₂))
  have hαν₂ : α ≠ ν₂ := fun e => d.bs₂ (c.col_proper (by rw [c.col_symm]; exact h.hbu)
    (e ▸ hus₂))
  have hαν₁ : α ≠ ν₁ := fun e => d.bs₁ (c.col_proper (by rw [c.col_symm]; exact h.hbu)
    (e ▸ hus₁))
  have hτν₂ : τ ≠ ν₂ := fun e => hd.ccs₂ (c.col_proper (by rw [c.col_symm]; exact h.hcu)
    (e ▸ hus₂))
  have hτν₁ : τ ≠ ν₁ := fun e => hd.ccs₁ (c.col_proper (by rw [c.col_symm]; exact h.hcu)
    (e ▸ hus₁))
  have hαγ := ng h.α₁
  have hτγ := ng h.τ₁
  have hαβ := nb h.αa
  have hτβ := nb h.τa
  have hγβ := nb h.γa
  obtain ⟨ζ, ξ, z1, z2, z3, y1, y2, y3, hζα, hζτ, hζν₂, hζν₁, hξα, hξτ, hξν₂, hξν₁, hζξ⟩ :=
    hR.two h.cm α τ ν₂ ν₁
  obtain ⟨c₁, h₁, m1, m2, hf, hcase⟩ := proc hG hd h hus₂ ν₂a hus₁ z1 z2 z3 y1 y2 y3 hζα hζτ
    hζν₂ hζν₁ hξα hξτ hξν₂ hξν₁ hζξ
  have ν₁a₁ : c₁.IsFree a ν₁ := (hf ν₁ e1 hν₁γ hζν₁.symm hξν₁.symm).2 ν₁a
  rcases hcase with ⟨v2, v1⟩ | ⟨v2, v1⟩
  swap
  · rw [Equiv.swap_apply_of_ne_of_ne hν e1] at v1
    exact p5 hG hd.swap hR.swap h₁.swap v2 v1 ν₁a₁
  -- make `ν₂` the colour missing at `b`: the `a`–`b` swaps `(γ, β)` and `(ν₂, γ)`
  have ν₂a₁ : c₁.IsFree a ν₂ := (hf ν₂ e2 hν₂γ hζν₂.symm hξν₂.symm).2 ν₂a
  have cm₁ := h₁.cm
  set c₂ := c₁.kempeSwap γ β a with hc₂
  have cm₂ : IsColMinus c₂ a b := cm₁.kempeSwap γ β a
  have γb₂ : c₂.IsFree b γ := ksAB_free_b hG cm₁ h₁.γa h₁.βb
  have fa₂ : ∀ x, x ≠ γ → x ≠ β → (c₂.IsFree a x ↔ c₁.IsFree a x) :=
    fun x h1 h2 => ksAB_free_a_of_ne hG cm₁ h₁.γa h₁.βb h1 h2
  have acc₂ : c₂.col a cc = some γ := kcol_flip₂ c₁ h₁.acc (Reachable.refl a)
  have hbu₂ : c₂.col b u = some α := kcol_keep c₁ h₁.hbu (Or.inl ⟨hαγ, hαβ⟩)
  have hcu₂ : c₂.col cc u = some τ := kcol_keep c₁ h₁.hcu (Or.inl ⟨hτγ, hτβ⟩)
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
  have ks₃ : KS c₃ a b cc u s₁ s₂ t₁ t₂ ν₂ α τ γ :=
    ⟨cm₃, ksAB_free_b hG cm₂ ν₂a₂ γb₂, kcol_flip₂ c₂ acc₂ (Reachable.refl a),
      kcol_keep c₂ hbu₂ (Or.inl ⟨hαν₂, hαγ⟩), fa α hαν₂ hαγ hαβ h₁.αa,
      kcol_keep c₂ hcu₂ (Or.inl ⟨hτν₂, hτγ⟩), fa τ hτν₂ hτγ hτβ h₁.τa,
      ab_keep_t hG cm₂ ν₂a₂ γb₂ (Or.inl ν₂t₁) d.at₁.symm d.bt₁.symm st₁₂,
      ab_keep_t hG cm₂ ν₂a₂ γb₂ (Or.inl ν₂t₂) d.at₂.symm d.bt₂.symm st₂₂,
      ksAB_free_a hG cm₂ ν₂a₂ γb₂, ft₁ α h₁.α₁, ft₂ α h₁.α₂, ft₁ ν₂ m1, ft₂ ν₂ m2,
      ft₁ τ h₁.τ₁, ft₂ τ h₁.τ₂⟩
  exact p5 hG hd.swap hR.swap ks₃.swap
    (ab_keep_us' hG cm₂ ν₂a₂ γb₂ ν₂t₂ d.at₂.symm d.bt₂.symm st₂₂ us₂₂)
    (kcol_keep c₂ us₁₂ (Or.inl ⟨hν, hν₁γ⟩))
    (fa ν₁ hν hν₁γ e1 ν₁a₁)

end Overfull
