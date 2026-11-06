/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.KiteF

/-!
# Kites, part G: CCJS Lemma 2.8

From a kite in the sense of `KiteProp`, five `a`–`b` swaps reach the kite state `KS`:
* `(θ₁, β₀)`: the colour missing at `b` becomes `θ₁`, missing at `t₁, t₂`;
* `(α₁, θ₁)` then `(θ₂, α₁)`: `bu` becomes `θ₁`, and `b` misses `θ₂`;
* `(τ₁, θ₂)` then `(θ₃, τ₁)`: `cc u` becomes `θ₂`, and `b` misses `θ₃`.
Here `θ₁, θ₂, θ₃` are fresh colours missing at `a, t₁, t₂` (`Robust`). The swaps never meet
`t₁, t₂`. Then `ks_false` applies.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

set_option maxHeartbeats 4000000 in
/-- **A kite is impossible.** -/
theorem kite_false (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b cc u s₁ s₂ t₁ t₂ : V}
    (hd : D8 a b cc u s₁ s₂ t₁ t₂) (db : G.degree b = G.maxDegree) (hR : Robust G a b t₁ t₂)
    (cm : IsColMinus c a b) (hbu : ∃ δ, c.col b u = some δ ∧ c.IsFree a δ)
    (g₁ : Good c a b u s₁) (gst₁ : Good c a b s₁ t₁)
    (hac : ∃ β, c.col a cc = some β ∧ c.IsFree b β) (gcu : Good c a b cc u)
    (g₂ : Good c a b u s₂) (heq : c.col s₁ t₁ = c.col s₂ t₂) : False := by
  have d := hd.d7
  obtain ⟨α₀, hbu₀, α₀a⟩ := hbu
  obtain ⟨β₀, hac₀, β₀b⟩ := hac
  obtain ⟨τ₀, hcu₀, τ₀A⟩ := gcu
  obtain ⟨γ₀, hst₁, γ₀A⟩ := gst₁
  have hst₂ : c.col s₂ t₂ = some γ₀ := by rw [← heq]; exact hst₁
  have dis : ∀ {ψ : PEC G (Fin G.maxDegree)}, IsColMinus ψ a b → ∀ {x y}, ψ.IsFree a x →
      ψ.IsFree b y → x ≠ y := fun hψ x y ha hb e => (hψ.ab_facts hG).1 x ha (e ▸ hb)
  have ng : ∀ {ψ : PEC G (Fin G.maxDegree)} {x}, ψ.col s₁ t₁ = some γ₀ → ψ.IsFree t₁ x →
      x ≠ γ₀ := fun hs hx e => hx s₁ (by rw [PEC.col_symm, hs, e])
  have τ₀a : c.IsFree a τ₀ := τ₀A.resolve_right fun hb => by
    have e := cm.b_only db β₀b hb
    rw [e] at hcu₀
    exact d.au (c.col_proper (by rw [c.col_symm]; exact hac₀) hcu₀)
  have adjne : ∀ {ψ : PEC G (Fin G.maxDegree)} {x y}, ψ.col b u = some x → ψ.col cc u = some y →
      x ≠ y := fun h1 h2 e => hd.bcc (PEC.col_proper _ (by rw [PEC.col_symm]; exact h1)
        (by rw [e, PEC.col_symm]; exact h2))
  -- step 1: the `a`–`b` swap `(θ₁, β₀)`
  obtain ⟨θ₁, -, θ₁a, θ₁t₁, θ₁t₂⟩ := hR c cm ∅ (by simp)
  have l1 := ksAB_link hG cm θ₁a β₀b
  set c₁ := c.kempeSwap θ₁ β₀ a with hc₁
  have cm₁ : IsColMinus c₁ a b := cm.kempeSwap θ₁ β₀ a
  have θ₁b₁ : c₁.IsFree b θ₁ := ksAB_free_b hG cm θ₁a β₀b
  have acc₁ : c₁.col a cc = some θ₁ := kcol_flip₂ c hac₀ (Reachable.refl a)
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
  obtain ⟨τ₁, hcu₁, τ₁a⟩ : ∃ x, c₁.col cc u = some x ∧ c₁.IsFree a x := by
    by_cases e : τ₀ = θ₁
    · exact ⟨β₀, kcol_flip₁ c (e ▸ hcu₀) (reachable_of_col (Reachable.refl a) (Or.inr hac₀)),
        ksAB_free_a hG cm θ₁a β₀b⟩
    · exact ⟨τ₀, kcol_keep c hcu₀ (Or.inl ⟨e, dis cm τ₀a β₀b⟩),
        (ksAB_free_a_of_ne hG cm θ₁a β₀b e (dis cm τ₀a β₀b)).2 τ₀a⟩
  have g₁₁ := good_kempeSwap a (Or.inl θ₁a) (Or.inr β₀b) A₁ g₁
  have g₂₁ := good_kempeSwap a (Or.inl θ₁a) (Or.inr β₀b) A₁ g₂
  have θ₁t₁₁ := (kfree_off c n1₁ θ₁).2 θ₁t₁
  have θ₁t₂₁ := (kfree_off c n1₂ θ₁).2 θ₁t₂
  -- step 2: the `a`–`b` swap `(α₁, θ₁)`
  have hα₁θ₁ := dis cm₁ α₁a θ₁b₁
  have hτ₁θ₁ := dis cm₁ τ₁a θ₁b₁
  have hτ₁α₁ := (adjne hbu₁ hcu₁).symm
  set c₂ := c₁.kempeSwap α₁ θ₁ a with hc₂
  have cm₂ : IsColMinus c₂ a b := cm₁.kempeSwap α₁ θ₁ a
  have α₁b₂ : c₂.IsFree b α₁ := ksAB_free_b hG cm₁ α₁a θ₁b₁
  have θ₁a₂ : c₂.IsFree a θ₁ := ksAB_free_a hG cm₁ α₁a θ₁b₁
  have A₂ := ksAB_inA hG cm₁ α₁a θ₁b₁
  have hbu₂ : c₂.col b u = some θ₁ := kcol_flip₁ c₁ hbu₁ (ksAB_link hG cm₁ α₁a θ₁b₁)
  have acc₂ : c₂.col a cc = some α₁ := kcol_flip₂ c₁ acc₁ (Reachable.refl a)
  have hcu₂ : c₂.col cc u = some τ₁ := kcol_keep c₁ hcu₁ (Or.inl ⟨hτ₁α₁, hτ₁θ₁⟩)
  have τ₁a₂ : c₂.IsFree a τ₁ := (ksAB_free_a_of_ne hG cm₁ α₁a θ₁b₁ hτ₁α₁ hτ₁θ₁).2 τ₁a
  have n2₁ := ab_off hG cm₁ α₁a θ₁b₁ (Or.inr θ₁t₁₁) d.at₁.symm d.bt₁.symm
  have n2₂ := ab_off hG cm₁ α₁a θ₁b₁ (Or.inr θ₁t₂₁) d.at₂.symm d.bt₂.symm
  have hst₁₂ := ab_keep_t hG cm₁ α₁a θ₁b₁ (Or.inr θ₁t₁₁) d.at₁.symm d.bt₁.symm hst₁₁
  have hst₂₂ := ab_keep_t hG cm₁ α₁a θ₁b₁ (Or.inr θ₁t₂₁) d.at₂.symm d.bt₂.symm hst₂₁
  have g₁₂ := good_kempeSwap a (Or.inl α₁a) (Or.inr θ₁b₁) A₂ g₁₁
  have g₂₂ := good_kempeSwap a (Or.inl α₁a) (Or.inr θ₁b₁) A₂ g₂₁
  -- step 3: the `a`–`b` swap `(θ₂, α₁)`
  obtain ⟨θ₂, hθ₂S, θ₂a, θ₂t₁, θ₂t₂⟩ := hR c₂ cm₂ {τ₁, θ₁} (card_le_two.trans (by omega))
  simp only [mem_insert, mem_singleton, not_or] at hθ₂S
  obtain ⟨hθ₂τ₁', hθ₂θ₁'⟩ := hθ₂S
  have hθ₂τ₁ : θ₂ ≠ τ₁ := hθ₂τ₁'
  have hθ₂θ₁ : θ₂ ≠ θ₁ := hθ₂θ₁'
  have hθ₂α₁ := dis cm₂ θ₂a α₁b₂
  have hγθ₂ := (ng hst₁₂ θ₂t₁).symm
  set c₃ := c₂.kempeSwap θ₂ α₁ a with hc₃
  have cm₃ : IsColMinus c₃ a b := cm₂.kempeSwap θ₂ α₁ a
  have θ₂b₃ : c₃.IsFree b θ₂ := ksAB_free_b hG cm₂ θ₂a α₁b₂
  have A₃ := ksAB_inA hG cm₂ θ₂a α₁b₂
  have hθ₁α₁ := hα₁θ₁.symm
  have hbu₃ : c₃.col b u = some θ₁ := kcol_keep c₂ hbu₂ (Or.inl ⟨hθ₂θ₁.symm, hθ₁α₁⟩)
  have acc₃ : c₃.col a cc = some θ₂ := kcol_flip₂ c₂ acc₂ (Reachable.refl a)
  have hcu₃ : c₃.col cc u = some τ₁ := kcol_keep c₂ hcu₂ (Or.inl ⟨hθ₂τ₁.symm, hτ₁α₁⟩)
  have θ₁a₃ : c₃.IsFree a θ₁ := (ksAB_free_a_of_ne hG cm₂ θ₂a α₁b₂ hθ₂θ₁.symm hθ₁α₁).2 θ₁a₂
  have τ₁a₃ : c₃.IsFree a τ₁ := (ksAB_free_a_of_ne hG cm₂ θ₂a α₁b₂ hθ₂τ₁.symm hτ₁α₁).2 τ₁a₂
  have γa₃ : c₃.IsFree a γ₀ := by
    by_cases e : γ₀ = α₁
    · rw [e]; exact ksAB_free_a hG cm₂ θ₂a α₁b₂
    · exact (ksAB_free_a_of_ne hG cm₂ θ₂a α₁b₂ hγθ₂ e).2
        ((ksAB_free_a_of_ne hG cm₁ α₁a θ₁b₁ e hγθ₁).2 γa₁)
  have θ₁t₁₂ := (kfree_off c₁ n2₁ θ₁).2 θ₁t₁₁
  have θ₁t₂₂ := (kfree_off c₁ n2₂ θ₁).2 θ₁t₂₁
  have n3₁ := ab_off hG cm₂ θ₂a α₁b₂ (Or.inl θ₂t₁) d.at₁.symm d.bt₁.symm
  have n3₂ := ab_off hG cm₂ θ₂a α₁b₂ (Or.inl θ₂t₂) d.at₂.symm d.bt₂.symm
  have hst₁₃ := ab_keep_t hG cm₂ θ₂a α₁b₂ (Or.inl θ₂t₁) d.at₁.symm d.bt₁.symm hst₁₂
  have hst₂₃ := ab_keep_t hG cm₂ θ₂a α₁b₂ (Or.inl θ₂t₂) d.at₂.symm d.bt₂.symm hst₂₂
  have g₁₃ := good_kempeSwap a (Or.inl θ₂a) (Or.inr α₁b₂) A₃ g₁₂
  have g₂₃ := good_kempeSwap a (Or.inl θ₂a) (Or.inr α₁b₂) A₃ g₂₂
  -- step 4: the `a`–`b` swap `(τ₁, θ₂)`
  set c₄ := c₃.kempeSwap τ₁ θ₂ a with hc₄
  have cm₄ : IsColMinus c₄ a b := cm₃.kempeSwap τ₁ θ₂ a
  have τ₁b₄ : c₄.IsFree b τ₁ := ksAB_free_b hG cm₃ τ₁a₃ θ₂b₃
  have θ₂a₄ : c₄.IsFree a θ₂ := ksAB_free_a hG cm₃ τ₁a₃ θ₂b₃
  have A₄ := ksAB_inA hG cm₃ τ₁a₃ θ₂b₃
  have hθ₁τ₁ := adjne hbu₃ hcu₃
  have hcu₄ : c₄.col cc u = some θ₂ :=
    kcol_flip₁ c₃ hcu₃ (reachable_of_col (Reachable.refl a) (Or.inr acc₃))
  have acc₄ : c₄.col a cc = some τ₁ := kcol_flip₂ c₃ acc₃ (Reachable.refl a)
  have hbu₄ : c₄.col b u = some θ₁ := kcol_keep c₃ hbu₃ (Or.inl ⟨hθ₁τ₁, hθ₂θ₁.symm⟩)
  have θ₁a₄ : c₄.IsFree a θ₁ := (ksAB_free_a_of_ne hG cm₃ τ₁a₃ θ₂b₃ hθ₁τ₁ hθ₂θ₁.symm).2 θ₁a₃
  have θ₁t₁₃ := (kfree_off c₂ n3₁ θ₁).2 θ₁t₁₂
  have θ₁t₂₃ := (kfree_off c₂ n3₂ θ₁).2 θ₁t₂₂
  have θ₂t₁₃ := (kfree_off c₂ n3₁ θ₂).2 θ₂t₁
  have θ₂t₂₃ := (kfree_off c₂ n3₂ θ₂).2 θ₂t₂
  have n4₁ := ab_off hG cm₃ τ₁a₃ θ₂b₃ (Or.inr θ₂t₁₃) d.at₁.symm d.bt₁.symm
  have n4₂ := ab_off hG cm₃ τ₁a₃ θ₂b₃ (Or.inr θ₂t₂₃) d.at₂.symm d.bt₂.symm
  have hst₁₄ := ab_keep_t hG cm₃ τ₁a₃ θ₂b₃ (Or.inr θ₂t₁₃) d.at₁.symm d.bt₁.symm hst₁₃
  have hst₂₄ := ab_keep_t hG cm₃ τ₁a₃ θ₂b₃ (Or.inr θ₂t₂₃) d.at₂.symm d.bt₂.symm hst₂₃
  have g₁₄ := good_kempeSwap a (Or.inl τ₁a₃) (Or.inr θ₂b₃) A₄ g₁₃
  have g₂₄ := good_kempeSwap a (Or.inl τ₁a₃) (Or.inr θ₂b₃) A₄ g₂₃
  -- step 5: the `a`–`b` swap `(θ₃, τ₁)`
  obtain ⟨θ₃, hθ₃S, θ₃a, θ₃t₁, θ₃t₂⟩ := hR c₄ cm₄ {θ₁, θ₂} (card_le_two.trans (by omega))
  simp only [mem_insert, mem_singleton, not_or] at hθ₃S
  obtain ⟨hθ₃θ₁', hθ₃θ₂'⟩ := hθ₃S
  have hθ₃θ₁ : θ₃ ≠ θ₁ := hθ₃θ₁'
  have hθ₃θ₂ : θ₃ ≠ θ₂ := hθ₃θ₂'
  have hθ₃τ₁ := dis cm₄ θ₃a τ₁b₄
  have hγθ₃ := (ng hst₁₄ θ₃t₁).symm
  have hγθ₂' := hγθ₂
  set c₅ := c₄.kempeSwap θ₃ τ₁ a with hc₅
  have cm₅ : IsColMinus c₅ a b := cm₄.kempeSwap θ₃ τ₁ a
  have A₅ := ksAB_inA hG cm₄ θ₃a τ₁b₄
  have n5₁ := ab_off hG cm₄ θ₃a τ₁b₄ (Or.inl θ₃t₁) d.at₁.symm d.bt₁.symm
  have n5₂ := ab_off hG cm₄ θ₃a τ₁b₄ (Or.inl θ₃t₂) d.at₂.symm d.bt₂.symm
  have t₁₅ : ∀ x, c₃.IsFree t₁ x → c₅.IsFree t₁ x := fun x h =>
    (kfree_off c₄ n5₁ x).2 ((kfree_off c₃ n4₁ x).2 h)
  have t₂₅ : ∀ x, c₃.IsFree t₂ x → c₅.IsFree t₂ x := fun x h =>
    (kfree_off c₄ n5₂ x).2 ((kfree_off c₃ n4₂ x).2 h)
  have γa₅ : c₅.IsFree a γ₀ := by
    by_cases e : γ₀ = τ₁
    · rw [e]; exact ksAB_free_a hG cm₄ θ₃a τ₁b₄
    · exact (ksAB_free_a_of_ne hG cm₄ θ₃a τ₁b₄ hγθ₃ e).2
        ((ksAB_free_a_of_ne hG cm₃ τ₁a₃ θ₂b₃ e hγθ₂).2 γa₃)
  have ks : KS c₅ a b cc u s₁ s₂ t₁ t₂ θ₃ θ₁ θ₂ γ₀ :=
    ⟨cm₅, ksAB_free_b hG cm₄ θ₃a τ₁b₄, kcol_flip₂ c₄ acc₄ (Reachable.refl a),
      kcol_keep c₄ hbu₄ (Or.inl ⟨hθ₃θ₁.symm, hθ₁τ₁⟩),
      (ksAB_free_a_of_ne hG cm₄ θ₃a τ₁b₄ hθ₃θ₁.symm hθ₁τ₁).2 θ₁a₄,
      kcol_keep c₄ hcu₄ (Or.inl ⟨hθ₃θ₂.symm, hθ₂τ₁⟩),
      (ksAB_free_a_of_ne hG cm₄ θ₃a τ₁b₄ hθ₃θ₂.symm hθ₂τ₁).2 θ₂a₄,
      ab_keep_t hG cm₄ θ₃a τ₁b₄ (Or.inl θ₃t₁) d.at₁.symm d.bt₁.symm hst₁₄,
      ab_keep_t hG cm₄ θ₃a τ₁b₄ (Or.inl θ₃t₂) d.at₂.symm d.bt₂.symm hst₂₄, γa₅,
      t₁₅ θ₁ θ₁t₁₃, t₂₅ θ₁ θ₁t₂₃, (kfree_off c₄ n5₁ θ₃).2 θ₃t₁, (kfree_off c₄ n5₂ θ₃).2 θ₃t₂,
      t₁₅ θ₂ θ₂t₁₃, t₂₅ θ₂ θ₂t₂₃⟩
  exact ks_false hG hd db hR ks (good_kempeSwap a (Or.inl θ₃a) (Or.inr τ₁b₄) A₅ g₁₄)
    (good_kempeSwap a (Or.inl θ₃a) (Or.inr τ₁b₄) A₅ g₂₄)

/-- **CCJS Lemma 2.8 (kites)**, in the form used by Theorem 1.2. -/
theorem kiteProp (hG : IsClassTwo G) : KiteProp G := by
  intro c a b cc u s₁ s₂ t₁ t₂ hnd cm hbu g₁ gst₁ hac gcu g₂ _ heq db hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or, not_false_eq_true] at hnd
  obtain ⟨⟨ab, acc, au, as₁, as₂, at₁, at₂⟩, ⟨bcc, bu, bs₁, bs₂, bt₁, bt₂⟩,
    ⟨ccu, ccs₁, ccs₂, cct₁, cct₂⟩, ⟨us₁, us₂, ut₁, ut₂⟩, ⟨s₁s₂, s₁t₁, s₁t₂⟩, ⟨s₂t₁, s₂t₂⟩,
    t₁t₂⟩ := hnd
  exact kite_false hG ⟨⟨ab, au, as₁, as₂, at₁, at₂, bu, bs₁, bs₂, bt₁, bt₂, us₁, us₂, ut₁, ut₂,
    s₁s₂, s₁t₁, s₁t₂, s₂t₁, s₂t₂, t₁t₂⟩, acc, bcc, ccu, ccs₁, ccs₂, cct₁, cct₂⟩ db hR cm hbu g₁
    gst₁ hac gcu g₂ heq

end Overfull
