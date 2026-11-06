/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Fork57b

/-!
# Fork lemma, Claim 5.8

For rainbow forks with `{α, β₁, β₂} ⊆ φ̄(t₁) ∩ φ̄(t₂)`, we may assume that `γ₁` or `γ₂` is missing
at `b`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b u s₁ s₂ t₁ t₂ : V}

/-- `{α, β₁, β₂} ⊆ φ̄(t₁) ∩ φ̄(t₂)`. -/
def TFull {k : ℕ} (c : PEC G (Fin k)) (t₁ t₂ : V) (α β₁ β₂ : Fin k) : Prop :=
  Both c t₁ t₂ α ∧ Both c t₁ t₂ β₁ ∧ Both c t₁ t₂ β₂

/-- After swapping an `a`–`b` chain the ends keep their missing colours, so `T` stays full. -/
theorem TFull.of_swapAB (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)}
    (hd : Distinct7 a b u s₁ s₂ t₁ t₂) (hcm : IsColMinus c a b) {α β₁ β₂ θ η : Fin G.maxDegree}
    (hθ : c.IsFree a θ) (hη : c.IsFree b η) (hT : TFull c t₁ t₂ α β₁ β₂) :
    TFull (c.kempeSwap θ η a) t₁ t₂ α β₁ β₂ := by
  have h1 := fun ε => ksAB_free_other hG hcm hθ hη hd.at₁.symm hd.bt₁.symm ε
  have h2 := fun ε => ksAB_free_other hG hcm hθ hη hd.at₂.symm hd.bt₂.symm ε
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := hT
  exact ⟨⟨(h1 _).2 a1, (h2 _).2 a2⟩, ⟨(h1 _).2 b1, (h2 _).2 b2⟩, ⟨(h1 _).2 c1, (h2 _).2 c2⟩⟩

variable (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
  {α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree} (hr : Rainbow α β₁ β₂ γ₁ γ₂)
  (hT1 : ∀ c' : PEC G (Fin G.maxDegree), IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ →
    TFull c' t₁ t₂ α β₁ β₂ → c'.IsFree b γ₁ → False)
include hG hd hr hT1

/-- Claim 5.8 (a2): a colour of `A ∩ φ̄(t₁)` outside the fork colours is missing at `a`. -/
theorem c58_a2 {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂)
    (hT : TFull c t₁ t₂ α β₁ β₂) (hγ₁a : c.IsFree a γ₁) {δ : Fin G.maxDegree}
    (hδA : InA c a b δ) (hδ₁ : c.IsFree t₁ δ) (hδβ₁ : δ ≠ β₁) (hδβ₂ : δ ≠ β₂)
    (hδγ₂ : δ ≠ γ₂) : c.IsFree a δ := by
  by_contra hδa
  have hδb : c.IsFree b δ := hδA.resolve_left hδa
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have hαδ : α ≠ δ := fun e => hdis α h.αa (e ▸ hδb)
  have hnt₁ : ¬ (c.kempeGraph γ₁ δ).Reachable a t₁ :=
    ksAB_not_reach hG h.cm hγ₁a hδb (Or.inr hδ₁) hd.at₁.symm hd.bt₁.symm (Reachable.refl t₁)
  have hf := h.of_swapAB hG hd hγ₁a hδb hr.1.symm
    (kcol_keep c h.cbu (Or.inl ⟨hr.1.symm, hαδ⟩))
    (kcol_keep c h.cus₁ (Or.inl ⟨h.β₁γ₁ hd, hδβ₁.symm⟩))
    (kcol_keep c h.cus₂ (Or.inl ⟨hr.2.1.symm, hδβ₂.symm⟩))
    (by rw [PEC.col_symm]; exact kcol_keep c h.ct₁s (Or.inr hnt₁))
    (kcol_keep c h.cst₂ (Or.inl ⟨h.γ₁γ₂.symm, hδγ₂.symm⟩))
  exact hT1 _ hf (hT.of_swapAB hG hd h.cm hγ₁a hδb) (ksAB_free_b hG h.cm hγ₁a hδb)

/-- **Claim 5.8.** Given that forks with `γ₁ ∈ φ̄(b)` or `γ₂ ∈ φ̄(b)` are impossible, every rainbow
fork with `T` full is impossible. -/
theorem claim58 (hH : ForkHyp G a b t₁ t₂)
    (hT2 : ∀ c' : PEC G (Fin G.maxDegree), IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ →
      TFull c' t₁ t₂ α β₁ β₂ → c'.IsFree b γ₂ → False)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂)
    (hT : TFull c t₁ t₂ α β₁ β₂) : False := by
  by_cases hγ₁b : c.IsFree b γ₁
  · exact hT1 c h hT hγ₁b
  by_cases hγ₂b : c.IsFree b γ₂
  · exact hT2 c h hT hγ₂b
  have hγ₁a : c.IsFree a γ₁ := h.γ₁A.resolve_right hγ₁b
  have hγ₂a : c.IsFree a γ₂ := h.γ₂A.resolve_right hγ₂b
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  -- (a1) `β₁, β₂ ∈ φ̄(a)`
  have hβ₁a : c.IsFree a β₁ := by
    by_contra hn
    have hb : c.IsFree b β₁ := h.β₁A.resolve_left hn
    have hs₁ : (c.kempeGraph γ₁ β₁).Reachable t₁ s₁ :=
      (kempeGraph_adj_of_col (Or.inl h.ct₁s)).reachable
    have hu : (c.kempeGraph γ₁ β₁).Reachable t₁ u := reachable_of_col hs₁ (Or.inr h.cs₁u)
    have hnr : ∀ {x}, (c.kempeGraph γ₁ β₁).Reachable t₁ x →
        ¬ (c.kempeGraph γ₁ β₁).Reachable a x := fun hx =>
      ksAB_not_reach hG h.cm hγ₁a hb (Or.inr hT.2.1.1) hd.at₁.symm hd.bt₁.symm hx
    have hf := h.of_swapAB hG hd hγ₁a hb hr.1.symm
      (kcol_keep c h.cbu (Or.inl ⟨hr.1.symm, h.αβ₁ hd⟩)) (kcol_keep c h.cus₁ (Or.inr (hnr hu)))
      (kcol_keep c h.cus₂ (Or.inl ⟨hr.2.1.symm, (h.β₁β₂ hd).symm⟩))
      (by rw [PEC.col_symm]; exact kcol_keep c h.ct₁s (Or.inr (hnr (Reachable.refl t₁))))
      (kcol_keep c h.cst₂ (Or.inl ⟨h.γ₁γ₂.symm, hr.2.2.2⟩))
    exact hT1 _ hf (hT.of_swapAB hG hd h.cm hγ₁a hb) (ksAB_free_b hG h.cm hγ₁a hb)
  have hβ₂a : c.IsFree a β₂ := by
    by_contra hn
    have hb : c.IsFree b β₂ := h.β₂A.resolve_left hn
    have hs₂ : (c.kempeGraph γ₂ β₂).Reachable t₂ s₂ :=
      (kempeGraph_adj_of_col (Or.inl h.ct₂s)).reachable
    have hu : (c.kempeGraph γ₂ β₂).Reachable t₂ u := reachable_of_col hs₂ (Or.inr h.cs₂u)
    have hnr : ∀ {x}, (c.kempeGraph γ₂ β₂).Reachable t₂ x →
        ¬ (c.kempeGraph γ₂ β₂).Reachable a x := fun hx =>
      ksAB_not_reach hG h.cm hγ₂a hb (Or.inr hT.2.2.2) hd.at₂.symm hd.bt₂.symm hx
    have hf := h.of_swapAB hG hd hγ₂a hb hr.2.2.1.symm
      (kcol_keep c h.cbu (Or.inl ⟨hr.2.2.1.symm, h.αβ₂ hd⟩))
      (kcol_keep c h.cus₁ (Or.inl ⟨hr.2.2.2.symm, h.β₁β₂ hd⟩))
      (kcol_keep c h.cus₂ (Or.inr (hnr hu))) (kcol_keep c h.cst₁ (Or.inl ⟨h.γ₁γ₂, hr.2.1⟩))
      (by rw [PEC.col_symm]; exact kcol_keep c h.ct₂s (Or.inr (hnr (Reachable.refl t₂))))
    exact hT2 _ hf (hT.of_swapAB hG hd h.cm hγ₂a hb) (ksAB_free_b hG h.cm hγ₂a hb)
  -- a colour `δ ∈ A ∩ φ̄(t₁)` outside the fork colours
  obtain ⟨δ, hδα, hδβ₁, hδβ₂, hδγ₂, hδA, hδ₁⟩ := (hH c h.cm).2.1 α β₁ β₂ γ₂
  have hδa := c58_a2 hG hd hr hT1 h hT hγ₁a hδA hδ₁ hδβ₁ hδβ₂ hδγ₂
  -- (a3) a colour missing at `b`
  obtain ⟨η, hηb⟩ := h.cm.exists_free_right
  have hne : ∀ {x}, c.IsFree a x → x ≠ η := fun hx e => hdis _ hx (e ▸ hηb)
  have hf := h.of_swapAB hG hd hδa hηb hδα.symm
    (kcol_keep c h.cbu (Or.inl ⟨hδα.symm, hne h.αa⟩))
    (kcol_keep c h.cus₁ (Or.inl ⟨hδβ₁.symm, hne hβ₁a⟩))
    (kcol_keep c h.cus₂ (Or.inl ⟨hδβ₂.symm, hne hβ₂a⟩))
    (kcol_keep c h.cst₁ (Or.inl ⟨fun e => h.not_free_t₁ (by rw [e]; exact hδ₁), hne hγ₁a⟩))
    (kcol_keep c h.cst₂ (Or.inl ⟨hδγ₂.symm, hne hγ₂a⟩))
  have hδa' := c58_a2 hG hd hr hT1 hf (hT.of_swapAB hG hd h.cm hδa hηb)
    ((ksAB_free_a_of_ne hG h.cm hδa hηb (fun e => h.not_free_t₁ (by rw [e]; exact hδ₁)) (hne hγ₁a)).2 hγ₁a)
    ((ksAB_inA hG h.cm hδa hηb δ).2 hδA)
    ((ksAB_free_other hG h.cm hδa hηb hd.at₁.symm hd.bt₁.symm δ).2 hδ₁) hδβ₁ hδβ₂ hδγ₂
  exact (hf.cm.ab_facts hG).1 δ hδa' (ksAB_free_b hG h.cm hδa hηb)

end Overfull
