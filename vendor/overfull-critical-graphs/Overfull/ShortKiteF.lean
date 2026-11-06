/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.ShortKiteE

/-!
# Short kites, part F: Case 2

In the normal form, if `x` misses a colour `τ ∈ φ̄(a)` different from `σ`, Kempe changes make `x`
miss `β` while keeping the normal form; then `case2_final` applies.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Edges coloured in `A` stay coloured in `A` under a swap of two colours of `A` that keeps `A`. -/
theorem good_kempeSwap {k : ℕ} {c : PEC G (Fin k)} {a b : V} {θ η : Fin k} (w : V)
    (hθ : InA c a b θ) (hη : InA c a b η)
    (hA : ∀ ε, InA (c.kempeSwap θ η w) a b ε ↔ InA c a b ε) {p q : V} (hg : Good c a b p q) :
    Good (c.kempeSwap θ η w) a b p q := by
  obtain ⟨ε, hε, hεA⟩ := hg
  by_cases hr : (c.kempeGraph θ η).Reachable w p
  · refine ⟨Equiv.swap θ η ε, ?_, (hA _).2 ?_⟩
    · rw [kempeSwap_col, kempeSwapFun_of_reachable c θ η hr q, hε]; rfl
    by_cases h1 : ε = θ
    · subst h1; rw [Equiv.swap_apply_left]; exact hη
    by_cases h2 : ε = η
    · subst h2; rw [Equiv.swap_apply_right]; exact hθ
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hεA
  · exact ⟨ε, by rw [kempeSwap_col, kempeSwapFun_of_not_reachable c θ η hr q, hε], (hA ε).2 hεA⟩

namespace SKNF

variable {c : PEC G (Fin G.maxDegree)} {a b cc u x y : V} {β δ ζ γ σ : Fin G.maxDegree}

/-- The normal form from its invariants. -/
theorem of_inv {c' : PEC G (Fin G.maxDegree)} (cm : IsColMinus c' a b) (d6 : Distinct6 a b cc u x y)
    (db : G.degree b = G.maxDegree) (du : G.degree u = G.maxDegree)
    (dcc : G.degree cc = G.maxDegree) (βb : c'.IsFree b β) (acc : c'.col a cc = some β)
    (hbu : c'.col b u = some δ) (δa : c'.IsFree a δ) (gcu : Good c' a b cc u)
    (gux : Good c' a b u x) (huy : c'.col u y = some β) (σy : c'.IsFree y σ)
    (σa : c'.IsFree a σ) : ∃ ζ' γ', SKNF c' a b cc u x y β δ ζ' γ' σ := by
  obtain ⟨ζ', hζ, hζA⟩ := gcu
  obtain ⟨γ', hγ, hγA⟩ := gux
  have hbonly : ∀ θ, c'.IsFree b θ → θ = β := by
    intro θ hθ
    have hm := cm.card_missing_end (Or.inr rfl)
    rw [db] at hm
    obtain ⟨μ, hμ⟩ := card_eq_one.1 (show #(missing c' b) = 1 by omega)
    have e1 : θ ∈ missing c' b := mem_missing.2 hθ
    have e2 : β ∈ missing c' b := mem_missing.2 βb
    rw [hμ, mem_singleton] at e1 e2
    rw [e1, e2]
  have hζβ : ζ' ≠ β := by
    rintro rfl
    exact d6.ccu.symm |> fun _ => d6.au (c'.col_proper (by rw [c'.col_symm]; exact acc) hζ)
  exact ⟨ζ', γ', ⟨cm, d6, db, du, dcc, βb, acc, hbu, δa, hζ,
    hζA.resolve_right fun hb => hζβ (hbonly ζ' hb), hγ, hγA, huy, σy, σa⟩⟩

set_option maxHeartbeats 1600000 in
/-- **Case 2.** In the normal form, `x` cannot miss a colour `τ ∈ φ̄(a)` different from `σ`. -/
theorem case2 (hG : IsClassTwo G) (h : SKNF c a b cc u x y β δ ζ γ σ) {τ : Fin G.maxDegree}
    (hxτ : c.IsFree x τ) (hτa : c.IsFree a τ) (hτσ : τ ≠ σ) : False := by
  have d6 := h.d6
  have hσδ := h.σδ hG
  have hδβ := h.δβ
  have hσβ := h.σβ
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have hτβ : τ ≠ β := fun e => hdis τ hτa (e ▸ h.βb)
  have hux : Good c a b u x := ⟨γ, h.hux, h.γA⟩
  have hcu : Good c a b cc u := ⟨ζ, h.hcu, Or.inl h.ζa⟩
  -- finishing from any normal form in which `x` misses `β`
  have finish : ∀ {c' : PEC G (Fin G.maxDegree)}, IsColMinus c' a b → c'.IsFree b β →
      c'.col a cc = some β → c'.col b u = some δ → c'.IsFree a δ → Good c' a b cc u →
      Good c' a b u x → c'.col u y = some β → c'.IsFree y σ → c'.IsFree a σ →
      c'.IsFree x β → False := by
    intro c' cm βb acc hbu δa gcu gux huy σy σa hxβ
    obtain ⟨ζ', γ', h'⟩ := of_inv cm d6 h.db h.du h.dcc βb acc hbu δa gcu gux huy σy σa
    exact h'.case2_final hG hxβ
  by_cases hu : (c.kempeGraph τ β).Reachable x u
  swap
  · -- swap the `(τ, β)`-chain of `x`
    have hxa : ¬ (c.kempeGraph τ β).Reachable x a := by
      rcases chain_avoids_ab hG h.cm (Or.inl hτa) (Or.inr h.βb) (Or.inl hxτ) d6.ax.symm
        d6.bx.symm (Or.inl rfl) with h1 | h1
      · exact h1
      · exact absurd hτa h1.1
    have hxb : ¬ (c.kempeGraph τ β).Reachable x b := by
      rcases chain_avoids_ab hG h.cm (Or.inl hτa) (Or.inr h.βb) (Or.inl hxτ) d6.ax.symm
        d6.bx.symm (Or.inr rfl) with h1 | h1
      · exact h1
      · exact absurd h.βb h1.2
    have hA := inA_kempeSwap_keeps hG h.cm (Or.inl hτa) (Or.inr h.βb) (Or.inl hxτ) d6.ax.symm
      d6.bx.symm
    exact finish (h.cm.kempeSwap τ β x) ((kfree_off c hxb β).2 h.βb)
      (kcol_keep c h.acc (Or.inr hxa)) (kcol_keep c h.hbu (Or.inr hxb))
      ((kfree_off c hxa δ).2 h.δa) (good_kempeSwap x (Or.inl hτa) (Or.inr h.βb) hA hcu)
      (good_kempeSwap x (Or.inl hτa) (Or.inr h.βb) hA hux) (kcol_keep c h.huy (Or.inr hu))
      ((kfree_of_ne c (Ne.symm hτσ) hσβ).2 h.σy)
      ((kfree_off c hxa σ).2 h.σa) ((kfree_flip₁ c (Reachable.refl x)).2 hxτ)
  -- the five-step sequence
  have hl := ksAB_link hG h.cm hτa h.βb
  have hnau : ¬ (c.kempeGraph τ β).Reachable a u := fun r =>
    not_three_linked c d6.ab d6.ax d6.bx (Or.inl hτa) (Or.inr h.βb) (Or.inl hxτ) hl (r.trans hu.symm)
  have hδτ : δ ≠ τ := by
    rintro rfl
    exact hnau (hl.trans (kempeGraph_adj_of_col (Or.inl h.hbu)).reachable)
  -- S1: R(τ, β)
  set c₁ := c.kempeSwap τ β a with hc₁
  have hA1 := ksAB_inA hG h.cm hτa h.βb
  have cm1 : IsColMinus c₁ a b := h.cm.kempeSwap τ β a
  have b1τ : c₁.IsFree b τ := ksAB_free_b hG h.cm hτa h.βb
  have a1β : c₁.IsFree a β := ksAB_free_a hG h.cm hτa h.βb
  have a1δ : c₁.IsFree a δ := (ksAB_free_a_of_ne hG h.cm hτa h.βb hδτ hδβ).2 h.δa
  have a1σ : c₁.IsFree a σ := (ksAB_free_a_of_ne hG h.cm hτa h.βb hτσ.symm hσβ).2 h.σa
  have c1acc : c₁.col a cc = some τ := kcol_flip₂ c h.acc (Reachable.refl a)
  have c1bu : c₁.col b u = some δ := kcol_keep c h.hbu (Or.inl ⟨hδτ, hδβ⟩)
  have c1uy : c₁.col u y = some β := kcol_keep c h.huy (Or.inr hnau)
  have x1τ : c₁.IsFree x τ := (ksAB_free_other hG h.cm hτa h.βb d6.ax.symm d6.bx.symm τ).2 hxτ
  have y1σ : c₁.IsFree y σ := (ksAB_free_other hG h.cm hτa h.βb d6.ay.symm d6.by_.symm σ).2 h.σy
  have g1cu := good_kempeSwap a (Or.inl hτa) (Or.inr h.βb) hA1 hcu
  have g1ux := good_kempeSwap a (Or.inl hτa) (Or.inr h.βb) hA1 hux
  -- S2: swap the `(δ, τ)`-chain of `x`
  have hl2 := ksAB_link hG cm1 a1δ b1τ
  have hau2 : (c₁.kempeGraph δ τ).Reachable a u :=
    hl2.trans (kempeGraph_adj_of_col (Or.inl c1bu)).reachable
  have hx2 : ∀ {z}, (c₁.kempeGraph δ τ).Reachable a z → ¬ (c₁.kempeGraph δ τ).Reachable x z :=
    fun hz r => ksAB_not_reach hG cm1 a1δ b1τ (Or.inr x1τ) d6.ax.symm d6.bx.symm r hz
  have hnx2u : ¬ (c₁.kempeGraph δ τ).Reachable x u := hx2 hau2
  have hnx2a : ¬ (c₁.kempeGraph δ τ).Reachable x a := hx2 (Reachable.refl a)
  have hnx2b : ¬ (c₁.kempeGraph δ τ).Reachable x b := hx2 hl2
  set c₂ := c₁.kempeSwap δ τ x with hc₂
  have fa2 := kfree_off c₁ hnx2a
  have fb2 := kfree_off c₁ hnx2b
  have hA2 : ∀ ε, InA c₂ a b ε ↔ InA c₁ a b ε := fun ε => by unfold InA; rw [fa2, fb2]
  have cm2 : IsColMinus c₂ a b := cm1.kempeSwap δ τ x
  have c2acc : c₂.col a cc = some τ := kcol_keep c₁ c1acc (Or.inr hnx2a)
  have c2bu : c₂.col b u = some δ := kcol_keep c₁ c1bu (Or.inr hnx2b)
  have c2uy : c₂.col u y = some β := kcol_keep c₁ c1uy (Or.inr hnx2u)
  have x2δ : c₂.IsFree x δ := (kfree_flip₂ c₁ (Reachable.refl x)).2 x1τ
  have y2σ : c₂.IsFree y σ := (kfree_of_ne c₁ hσδ hτσ.symm).2 y1σ
  have g2cu := good_kempeSwap x (Or.inl a1δ) (Or.inr b1τ) hA2 g1cu
  have g2ux := good_kempeSwap x (Or.inl a1δ) (Or.inr b1τ) hA2 g1ux
  have a2σ : c₂.IsFree a σ := (fa2 σ).2 a1σ
  have a2β : c₂.IsFree a β := (fa2 β).2 a1β
  have a2δ : c₂.IsFree a δ := (fa2 δ).2 a1δ
  have b2τ : c₂.IsFree b τ := (fb2 τ).2 b1τ
  -- S3: R(σ, τ)
  set c₃ := c₂.kempeSwap σ τ a with hc₃
  have hA3 := ksAB_inA hG cm2 a2σ b2τ
  have cm3 : IsColMinus c₃ a b := cm2.kempeSwap σ τ a
  have b3σ : c₃.IsFree b σ := ksAB_free_b hG cm2 a2σ b2τ
  have a3β : c₃.IsFree a β := (ksAB_free_a_of_ne hG cm2 a2σ b2τ hσβ.symm hτβ.symm).2 a2β
  have a3δ : c₃.IsFree a δ := (ksAB_free_a_of_ne hG cm2 a2σ b2τ hσδ.symm hδτ).2 a2δ
  have c3acc : c₃.col a cc = some σ := kcol_flip₂ c₂ c2acc (Reachable.refl a)
  have c3bu : c₃.col b u = some δ := kcol_keep c₂ c2bu (Or.inl ⟨hσδ.symm, hδτ⟩)
  have c3uy : c₃.col u y = some β := kcol_keep c₂ c2uy (Or.inl ⟨hσβ.symm, hτβ.symm⟩)
  have x3δ : c₃.IsFree x δ := (ksAB_free_other hG cm2 a2σ b2τ d6.ax.symm d6.bx.symm δ).2 x2δ
  have y3σ : c₃.IsFree y σ := (ksAB_free_other hG cm2 a2σ b2τ d6.ay.symm d6.by_.symm σ).2 y2σ
  have g3cu := good_kempeSwap a (Or.inl a2σ) (Or.inr b2τ) hA3 g2cu
  have g3ux := good_kempeSwap a (Or.inl a2σ) (Or.inr b2τ) hA3 g2ux
  -- S4: R(β, σ)
  have hyu4 : (c₃.kempeGraph β σ).Reachable y u :=
    (kempeGraph_adj_of_col (Or.inl (by rw [c₃.col_symm]; exact c3uy))).reachable
  have hnau4 : ¬ (c₃.kempeGraph β σ).Reachable a u :=
    ksAB_not_reach hG cm3 a3β b3σ (Or.inr y3σ) d6.ay.symm d6.by_.symm hyu4
  set c₄ := c₃.kempeSwap β σ a with hc₄
  have hA4 := ksAB_inA hG cm3 a3β b3σ
  have cm4 : IsColMinus c₄ a b := cm3.kempeSwap β σ a
  have b4β : c₄.IsFree b β := ksAB_free_b hG cm3 a3β b3σ
  have a4σ : c₄.IsFree a σ := ksAB_free_a hG cm3 a3β b3σ
  have a4δ : c₄.IsFree a δ := (ksAB_free_a_of_ne hG cm3 a3β b3σ hδβ hσδ.symm).2 a3δ
  have c4acc : c₄.col a cc = some β := kcol_flip₂ c₃ c3acc (Reachable.refl a)
  have c4bu : c₄.col b u = some δ := kcol_keep c₃ c3bu (Or.inl ⟨hδβ, hσδ.symm⟩)
  have c4uy : c₄.col u y = some β := kcol_keep c₃ c3uy (Or.inr hnau4)
  have x4δ : c₄.IsFree x δ := (ksAB_free_other hG cm3 a3β b3σ d6.ax.symm d6.bx.symm δ).2 x3δ
  have y4σ : c₄.IsFree y σ := (ksAB_free_other hG cm3 a3β b3σ d6.ay.symm d6.by_.symm σ).2 y3σ
  have g4cu := good_kempeSwap a (Or.inl a3β) (Or.inr b3σ) hA4 g3cu
  have g4ux := good_kempeSwap a (Or.inl a3β) (Or.inr b3σ) hA4 g3ux
  -- S5: swap the `(δ, β)`-chain of `x`
  have hl5 := ksAB_link hG cm4 a4δ b4β
  have hau5 : (c₄.kempeGraph δ β).Reachable a u :=
    hl5.trans (kempeGraph_adj_of_col (Or.inl c4bu)).reachable
  have hx5 : ∀ {z}, (c₄.kempeGraph δ β).Reachable a z → ¬ (c₄.kempeGraph δ β).Reachable x z :=
    fun hz r => ksAB_not_reach hG cm4 a4δ b4β (Or.inl x4δ) d6.ax.symm d6.bx.symm r hz
  set c₅ := c₄.kempeSwap δ β x with hc₅
  have fa5 := kfree_off c₄ (hx5 (Reachable.refl a))
  have fb5 := kfree_off c₄ (hx5 hl5)
  have hA5 : ∀ ε, InA c₅ a b ε ↔ InA c₄ a b ε := fun ε => by unfold InA; rw [fa5, fb5]
  exact finish (cm4.kempeSwap δ β x) ((fb5 β).2 b4β)
    (kcol_keep c₄ c4acc (Or.inr (hx5 (Reachable.refl a))))
    (kcol_keep c₄ c4bu (Or.inr (hx5 hl5))) ((fa5 δ).2 a4δ)
    (good_kempeSwap x (Or.inl a4δ) (Or.inr b4β) hA5 g4cu)
    (good_kempeSwap x (Or.inl a4δ) (Or.inr b4β) hA5 g4ux)
    (kcol_keep c₄ c4uy (Or.inr (hx5 hau5))) ((kfree_of_ne c₄ hσδ hσβ).2 y4σ)
    ((fa5 σ).2 a4σ) ((kfree_flip₁ c₄ (Reachable.refl x)).2 x4δ)

end SKNF

end Overfull
