/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Fork56a

/-!
# Fork lemma, Claim 5.6: Cases 2 and 4 (`γ₁ = β₂`)

Cao–Chen (2020), proof of Claim 5.6, items (b1)–(b7). Hypotheses provided by the earlier cases:
`hY` (a fork with `γ₁ = δ' ∉ {α, β₁, β₂}` and the same other colours is impossible), `hZ` (a fork
with `γ₁ = α` and the same other colours is impossible), and, in Case 4 only, `hW` (Case 2 for
`γ₂ = δ'`).
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b u s₁ s₂ t₁ t₂ : V} {α β₁ β₂ γ₂ : Fin G.maxDegree}

/-- (b1): the `(δ, β₂)`-chain of `t₁` passes along `us₂`. -/
theorem case24_b1 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hY : ∀ (c' : PEC G (Fin G.maxDegree)) (δ' : Fin G.maxDegree),
      IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ δ' γ₂ → δ' ≠ α → δ' ≠ β₁ → δ' ≠ β₂ → False)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ β₂ γ₂)
    {δ : Fin G.maxDegree} (hδ : IsDelta c a b t₁ t₂ α β₁ β₂ δ) :
    (c.kempeGraph δ β₂).Reachable t₁ s₂ := by
  obtain ⟨hδA, hδ₁, hδ₂, hδα, hδβ₁, hδβ₂⟩ := hδ
  by_contra hn
  have hnu : ¬ (c.kempeGraph δ β₂).Reachable t₁ u := fun r =>
    hn (reachable_of_col r (Or.inr h.cus₂))
  have hγ₂δ : γ₂ ≠ δ := fun e => h.not_free_t₂ (e ▸ hδ₂)
  have hγ₂β₂ : γ₂ ≠ β₂ := (h.β₂γ₂ hd).symm
  have ht₂ : ¬ (c.kempeGraph δ β₂).Reachable t₁ t₂ := fun r =>
    hd.t₁t₂ (eq_of_reachable_of_free_both c hδ₂ h.γ₁t₂ r.symm)
  have hkeep := fun (z : V) (hz : z = a ∨ z = b) =>
    kempeSwap_keeps_ab hG h.cm hδA h.β₂A (Or.inl hδ₁) hd.at₁.symm hd.bt₁.symm hz
  have hA := inA_kempeSwap_keeps hG h.cm hδA h.β₂A (Or.inl hδ₁) hd.at₁.symm hd.bt₁.symm
  refine hY (c.kempeSwap δ β₂ t₁) δ ⟨h.cm.kempeSwap δ β₂ t₁,
    kcol_keep c h.cbu (Or.inl ⟨hδα.symm, h.αβ₂ hd⟩),
    kcol_keep c h.cus₁ (Or.inl ⟨hδβ₁.symm, h.β₁β₂ hd⟩), kcol_keep c h.cus₂ (Or.inr hnu), ?_,
    kcol_keep c h.cst₂ (Or.inl ⟨hγ₂δ, hγ₂β₂⟩), (hkeep a (Or.inl rfl) α).2 h.αa, (hA β₁).2 h.β₁A,
    (hA β₂).2 h.β₂A, (hA δ).2 hδA, (hA γ₂).2 h.γ₂A, (kfree_off c ht₂ δ).2 hδ₂,
    (kfree_of_ne c hγ₂δ hγ₂β₂).2 h.γ₂t₁⟩ hδα hδβ₁ hδβ₂
  rw [PEC.col_symm]
  exact kcol_flip₂ c h.ct₁s (Reachable.refl t₁)

/-- (b2): `β₂ ∈ φ̄(b)` and `α ∈ φ̄(t₁) ∩ φ̄(t₂)` is impossible. -/
theorem case24_b2 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hZ : ∀ c' : PEC G (Fin G.maxDegree), IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂ → False)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ β₂ γ₂)
    (hγ₂α : γ₂ ≠ α) (hβ₂b : c.IsFree b β₂) (hα₁ : c.IsFree t₁ α) (hα₂ : c.IsFree t₂ α) :
    False := by
  have hl := ksAB_link hG h.cm h.αa hβ₂b
  have hub := reachable_of_col hl (Or.inl h.cbu)
  have hnu : ¬ (c.kempeGraph α β₂).Reachable t₁ u := fun r =>
    ksAB_not_reach hG h.cm h.αa hβ₂b (Or.inl hα₁) hd.at₁.symm hd.bt₁.symm r hub
  have ht₂ : ¬ (c.kempeGraph α β₂).Reachable t₁ t₂ := fun r =>
    hd.t₁t₂ (eq_of_reachable_of_free_both c hα₂ h.γ₁t₂ r.symm)
  have hγ₂β₂ : γ₂ ≠ β₂ := (h.β₂γ₂ hd).symm
  have hkeep := fun (z : V) (hz : z = a ∨ z = b) =>
    kempeSwap_keeps_ab hG h.cm (Or.inl h.αa) h.β₂A (Or.inl hα₁) hd.at₁.symm hd.bt₁.symm hz
  have hA := inA_kempeSwap_keeps hG h.cm (Or.inl h.αa) h.β₂A (Or.inl hα₁) hd.at₁.symm
    hd.bt₁.symm
  refine hZ (c.kempeSwap α β₂ t₁) ⟨h.cm.kempeSwap α β₂ t₁, ?_,
    kcol_keep c h.cus₁ (Or.inl ⟨(h.αβ₁ hd).symm, h.β₁β₂ hd⟩), kcol_keep c h.cus₂ (Or.inr hnu), ?_,
    kcol_keep c h.cst₂ (Or.inl ⟨hγ₂α, hγ₂β₂⟩), (hkeep a (Or.inl rfl) α).2 h.αa, (hA β₁).2 h.β₁A,
    (hA β₂).2 h.β₂A, (hA α).2 (Or.inl h.αa), (hA γ₂).2 h.γ₂A, (kfree_off c ht₂ α).2 hα₂,
    (kfree_of_ne c hγ₂α hγ₂β₂).2 h.γ₂t₁⟩
  · rw [PEC.col_symm]
    exact kcol_keep c h.cub (Or.inr hnu)
  · rw [PEC.col_symm]
    exact kcol_flip₂ c h.ct₁s (Reachable.refl t₁)

/-- (b3): `δ ∈ φ̄(b)` and `α ∈ φ̄(t₁) ∩ φ̄(t₂)` is impossible. -/
theorem case24_b3 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hY : ∀ (c' : PEC G (Fin G.maxDegree)) (δ' : Fin G.maxDegree),
      IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ δ' γ₂ → δ' ≠ α → δ' ≠ β₁ → δ' ≠ β₂ → False)
    (hZ : ∀ c' : PEC G (Fin G.maxDegree), IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂ → False)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ β₂ γ₂)
    (hγ₂α : γ₂ ≠ α) {δ : Fin G.maxDegree} (hδ : IsDelta c a b t₁ t₂ α β₁ β₂ δ)
    (hδb : c.IsFree b δ) (hα₁ : c.IsFree t₁ α) (hα₂ : c.IsFree t₂ α) : False := by
  by_cases hβ₂b : c.IsFree b β₂
  · exact case24_b2 hG hd hZ h hγ₂α hβ₂b hα₁ hα₂
  have hβ₂a : c.IsFree a β₂ := h.β₂A.resolve_right hβ₂b
  have hb1 := case24_b1 hG hd hY h hδ
  obtain ⟨hδA, hδ₁, hδ₂, hδα, hδβ₁, hδβ₂⟩ := hδ
  rw [kempeGraph_comm] at hb1
  have hus : (c.kempeGraph β₂ δ).Reachable t₁ u := reachable_of_col hb1 (Or.inl h.cs₂u)
  have hnr : ∀ {x}, (c.kempeGraph β₂ δ).Reachable t₁ x → ¬ (c.kempeGraph β₂ δ).Reachable a x :=
    fun hx => ksAB_not_reach hG h.cm hβ₂a hδb (Or.inr hδ₁) hd.at₁.symm hd.bt₁.symm hx
  have hγ₂δ : γ₂ ≠ δ := fun e => h.not_free_t₂ (e ▸ hδ₂)
  have hf := h.of_swapAB hG hd hβ₂a hδb (h.αβ₂ hd)
    (kcol_keep c h.cbu (Or.inl ⟨h.αβ₂ hd, hδα.symm⟩))
    (kcol_keep c h.cus₁ (Or.inl ⟨h.β₁β₂ hd, hδβ₁.symm⟩)) (kcol_keep c h.cus₂ (Or.inr (hnr hus)))
    (by rw [PEC.col_symm]; exact kcol_keep c h.ct₁s (Or.inr (hnr (Reachable.refl t₁))))
    (kcol_keep c h.cst₂ (Or.inl ⟨(h.β₂γ₂ hd).symm, hγ₂δ⟩))
  exact case24_b2 hG hd hZ hf hγ₂α (ksAB_free_b hG h.cm hβ₂a hδb)
    ((ksAB_free_other hG h.cm hβ₂a hδb hd.at₁.symm hd.bt₁.symm α).2 hα₁)
    ((ksAB_free_other hG h.cm hβ₂a hδb hd.at₂.symm hd.bt₂.symm α).2 hα₂)

/-- A delta-colour exists for a fork with `γ₁ = β₂`. -/
theorem case24_delta (hH : ForkHyp G a b t₁ t₂) {c : PEC G (Fin G.maxDegree)}
    (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ β₂ γ₂) :
    ∃ δ, IsDelta c a b t₁ t₂ α β₁ β₂ δ := by
  obtain ⟨δ, h1, h2, hA, ht₁, ht₂⟩ := (hH c h.cm).1 α β₁
  exact ⟨δ, hA, ht₁, ht₂, h1, h2, fun e => h.not_free_t₁ (e ▸ ht₁)⟩

/-- (b4): a delta-colour is missing at `a`. -/
theorem case24_b4 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hH : ForkHyp G a b t₁ t₂)
    (hY : ∀ (c' : PEC G (Fin G.maxDegree)) (δ' : Fin G.maxDegree),
      IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ δ' γ₂ → δ' ≠ α → δ' ≠ β₁ → δ' ≠ β₂ → False)
    (hZ : ∀ c' : PEC G (Fin G.maxDegree), IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂ → False)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ β₂ γ₂)
    (hγ₂α : γ₂ ≠ α) {δ : Fin G.maxDegree} (hδ : IsDelta c a b t₁ t₂ α β₁ β₂ δ) :
    c.IsFree a δ := by
  obtain ⟨hδA, hδ₁, hδ₂, hδα, hδβ₁, hδβ₂⟩ := hδ
  by_contra hδa
  have hδb : c.IsFree b δ := hδA.resolve_left hδa
  have hl := ksAB_link hG h.cm h.αa hδb
  have hnr : ∀ {w}, (c.IsFree w α ∨ c.IsFree w δ) → w ≠ a → w ≠ b →
      ¬ (c.kempeGraph α δ).Reachable a w := fun hw hwa hwb =>
    ksAB_not_reach hG h.cm h.αa hδb hw hwa hwb (Reachable.refl _)
  have hta := fun ε => kempeSwapCompl_isFree_of_reachable c α δ (Reachable.refl a) ε
  have htb := fun ε => kempeSwapCompl_isFree_of_reachable c α δ hl ε
  have hA' : ∀ ε, InA (kempeSwapCompl c α δ a) a b ε ↔ InA c a b ε := by
    intro ε; unfold InA; rw [hta, htb]
  have hγ₂δ : γ₂ ≠ δ := fun e => h.not_free_t₂ (e ▸ hδ₂)
  have hβ₁α := (h.αβ₁ hd).symm
  have hβ₂α := (h.αβ₂ hd).symm
  set c' := kempeSwapCompl c α δ a with hc'
  have hα₁ : c'.IsFree t₁ α := (cfree_flip₂ c (hnr (Or.inr hδ₁) hd.at₁.symm hd.bt₁.symm)).2 hδ₁
  have hα₂ : c'.IsFree t₂ α := (cfree_flip₂ c (hnr (Or.inr hδ₂) hd.at₂.symm hd.bt₂.symm)).2 hδ₂
  have hf : IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ β₂ γ₂ :=
    ⟨h.cm.kempeSwapCompl α δ a, ccol_keep c h.cbu (Or.inr hl),
      ccol_keep c h.cus₁ (Or.inl ⟨hβ₁α, hδβ₁.symm⟩), ccol_keep c h.cus₂ (Or.inl ⟨hβ₂α, hδβ₂.symm⟩),
      ccol_keep c h.cst₁ (Or.inl ⟨hβ₂α, hδβ₂.symm⟩), ccol_keep c h.cst₂ (Or.inl ⟨hγ₂α, hγ₂δ⟩),
      (hta α).2 h.αa, (hA' β₁).2 h.β₁A, (hA' β₂).2 h.β₂A, (hA' β₂).2 h.γ₁A, (hA' γ₂).2 h.γ₂A,
      (cfree_of_ne c hβ₂α hδβ₂.symm).2 h.γ₁t₂, (cfree_of_ne c hγ₂α hγ₂δ).2 h.γ₂t₁⟩
  have hδb' : c'.IsFree b δ := (htb δ).2 hδb
  obtain ⟨δ', hδ'⟩ := case24_delta hH hf
  by_cases hb' : c'.IsFree b δ'
  · exact case24_b3 hG hd hY hZ hf hγ₂α hδ' hb' hα₁ hα₂
  obtain ⟨hA'', h₁'', h₂'', hα'', hβ₁'', hβ₂''⟩ := hδ'
  have ha' : c'.IsFree a δ' := hA''.resolve_right hb'
  have hγ₂δ' : γ₂ ≠ δ' := fun e => hf.not_free_t₂ (e ▸ h₂'')
  have hf' := hf.of_swapAB hG hd ha' hδb' hα''.symm
    (kcol_keep c' hf.cbu (Or.inl ⟨hα''.symm, hδα.symm⟩))
    (kcol_keep c' hf.cus₁ (Or.inl ⟨hβ₁''.symm, hδβ₁.symm⟩))
    (kcol_keep c' hf.cus₂ (Or.inl ⟨hβ₂''.symm, hδβ₂.symm⟩))
    (kcol_keep c' hf.cst₁ (Or.inl ⟨hβ₂''.symm, hδβ₂.symm⟩))
    (kcol_keep c' hf.cst₂ (Or.inl ⟨hγ₂δ', hγ₂δ⟩))
  exact case24_b3 hG hd hY hZ hf' hγ₂α
    (IsDelta.of_swapAB hG hf.cm hd.at₁ hd.at₂ hd.bt₁ hd.bt₂
      ⟨hA'', h₁'', h₂'', hα'', hβ₁'', hβ₂''⟩ ha' hδb')
    (ksAB_free_b hG hf.cm ha' hδb')
    ((ksAB_free_other hG hf.cm ha' hδb' hd.at₁.symm hd.bt₁.symm α).2 hα₁)
    ((ksAB_free_other hG hf.cm ha' hδb' hd.at₂.symm hd.bt₂.symm α).2 hα₂)

/-- (b5): `β₂` is missing at `a`. -/
theorem case24_b5 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hH : ForkHyp G a b t₁ t₂)
    (hY : ∀ (c' : PEC G (Fin G.maxDegree)) (δ' : Fin G.maxDegree),
      IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ δ' γ₂ → δ' ≠ α → δ' ≠ β₁ → δ' ≠ β₂ → False)
    (hZ : ∀ c' : PEC G (Fin G.maxDegree), IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂ → False)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ β₂ γ₂)
    (hγ₂α : γ₂ ≠ α) {δ : Fin G.maxDegree} (hδ : IsDelta c a b t₁ t₂ α β₁ β₂ δ)
    (hβ₂b : c.IsFree b β₂) : False := by
  have hδa := case24_b4 hG hd hH hY hZ h hγ₂α hδ
  have hb1 := case24_b1 hG hd hY h hδ
  have hδ' := hδ
  obtain ⟨hδA, hδ₁, hδ₂, hδα, hδβ₁, hδβ₂⟩ := hδ
  have hus : (c.kempeGraph δ β₂).Reachable t₁ u := reachable_of_col hb1 (Or.inr h.cs₂u)
  have hnr : ∀ {x}, (c.kempeGraph δ β₂).Reachable t₁ x → ¬ (c.kempeGraph δ β₂).Reachable a x :=
    fun hx => ksAB_not_reach hG h.cm hδa hβ₂b (Or.inl hδ₁) hd.at₁.symm hd.bt₁.symm hx
  have hγ₂δ : γ₂ ≠ δ := fun e => h.not_free_t₂ (e ▸ hδ₂)
  have hf := h.of_swapAB hG hd hδa hβ₂b hδα.symm
    (kcol_keep c h.cbu (Or.inl ⟨hδα.symm, h.αβ₂ hd⟩))
    (kcol_keep c h.cus₁ (Or.inl ⟨hδβ₁.symm, h.β₁β₂ hd⟩)) (kcol_keep c h.cus₂ (Or.inr (hnr hus)))
    (by rw [PEC.col_symm]; exact kcol_keep c h.ct₁s (Or.inr (hnr (Reachable.refl t₁))))
    (kcol_keep c h.cst₂ (Or.inl ⟨hγ₂δ, (h.β₂γ₂ hd).symm⟩))
  have hδb' := ksAB_free_b hG h.cm hδa hβ₂b
  have hδa' := case24_b4 hG hd hH hY hZ hf hγ₂α
    (IsDelta.of_swapAB hG h.cm hd.at₁ hd.at₂ hd.bt₁ hd.bt₂ hδ' hδa hβ₂b)
  exact (hf.cm.ab_facts hG).1 δ hδa' hδb'

/-- (b6): for `η ∈ φ̄(b)`, `P_a(δ, η)` passes along `us₁`. -/
theorem case24_b6 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hH : ForkHyp G a b t₁ t₂)
    (hY : ∀ (c' : PEC G (Fin G.maxDegree)) (δ' : Fin G.maxDegree),
      IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ δ' γ₂ → δ' ≠ α → δ' ≠ β₁ → δ' ≠ β₂ → False)
    (hZ : ∀ c' : PEC G (Fin G.maxDegree), IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂ → False)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ β₂ γ₂)
    (hγ₂α : γ₂ ≠ α) {δ : Fin G.maxDegree} (hδ : IsDelta c a b t₁ t₂ α β₁ β₂ δ)
    (hβ₂a : c.IsFree a β₂) {η : Fin G.maxDegree} (hηb : c.IsFree b η)
    (hpass : η ≠ β₁ ∨ ¬ (c.kempeGraph δ η).Reachable a s₁) : False := by
  have hδa := case24_b4 hG hd hH hY hZ h hγ₂α hδ
  have hδ' := hδ
  obtain ⟨hδA, hδ₁, hδ₂, hδα, hδβ₁, hδβ₂⟩ := hδ
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have hαη : α ≠ η := fun e => hdis α h.αa (e ▸ hηb)
  have hβ₂η : β₂ ≠ η := fun e => hdis β₂ hβ₂a (e ▸ hηb)
  have hnr₂ : ¬ (c.kempeGraph δ η).Reachable a t₂ :=
    ksAB_not_reach hG h.cm hδa hηb (Or.inl hδ₂) hd.at₂.symm hd.bt₂.symm (Reachable.refl t₂)
  have hf := h.of_swapAB hG hd hδa hηb hδα.symm (kcol_keep c h.cbu (Or.inl ⟨hδα.symm, hαη⟩))
    (by
      rw [PEC.col_symm]
      exact kcol_keep c h.cs₁u (hpass.elim (fun hne => Or.inl ⟨hδβ₁.symm, hne.symm⟩) Or.inr))
    (kcol_keep c h.cus₂ (Or.inl ⟨hδβ₂.symm, hβ₂η⟩))
    (kcol_keep c h.cst₁ (Or.inl ⟨hδβ₂.symm, hβ₂η⟩))
    (by rw [PEC.col_symm]; exact kcol_keep c h.ct₂s (Or.inr hnr₂))
  have hδa' := case24_b4 hG hd hH hY hZ hf hγ₂α
    (IsDelta.of_swapAB hG h.cm hd.at₁ hd.at₂ hd.bt₁ hd.bt₂ hδ' hδa hηb)
  exact (hf.cm.ab_facts hG).1 δ hδa' (ksAB_free_b hG h.cm hδa hηb)

/-- **Claim 5.6, Cases 2 and 4.** A fork with `γ₁ = β₂` and `γ₂ ≠ α` is impossible. -/
theorem case24 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hH : ForkHyp G a b t₁ t₂)
    (hY : ∀ (c' : PEC G (Fin G.maxDegree)) (δ' : Fin G.maxDegree),
      IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ δ' γ₂ → δ' ≠ α → δ' ≠ β₁ → δ' ≠ β₂ → False)
    (hZ : ∀ c' : PEC G (Fin G.maxDegree), IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂ → False)
    (hW : γ₂ = β₁ → ∀ (c' : PEC G (Fin G.maxDegree)) (δ' : Fin G.maxDegree),
      IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ β₂ δ' → δ' ≠ α → δ' ≠ β₁ → δ' ≠ β₂ → False)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ β₂ γ₂)
    (hγ₂α : γ₂ ≠ α) : False := by
  obtain ⟨δ, hδ⟩ := case24_delta hH h
  have hδa := case24_b4 hG hd hH hY hZ h hγ₂α hδ
  have hβ₂a : c.IsFree a β₂ :=
    h.β₂A.resolve_right fun hb => case24_b5 hG hd hH hY hZ h hγ₂α hδ hb
  obtain ⟨η, hη⟩ := h.cm.exists_free_right
  have hηβ₁ : η = β₁ := by
    by_contra hne
    exact case24_b6 hG hd hH hY hZ h hγ₂α hδ hβ₂a hη (Or.inl hne)
  subst hηβ₁
  have hpass : (c.kempeGraph δ η).Reachable a s₁ := by
    by_contra hp
    exact case24_b6 hG hd hH hY hZ h hγ₂α hδ hβ₂a hη (Or.inr hp)
  have hδ' := hδ
  obtain ⟨hδA, hδ₁, hδ₂, hδα, hδβ₁, hδβ₂⟩ := hδ
  -- switch `δ, β₁` on all chains except `P_a(δ, β₁)`
  have hl := ksAB_link hG h.cm hδa hη
  have hnr : ∀ {w}, (c.IsFree w δ ∨ c.IsFree w η) → w ≠ a → w ≠ b →
      ¬ (c.kempeGraph δ η).Reachable a w := fun hw hwa hwb =>
    ksAB_not_reach hG h.cm hδa hη hw hwa hwb (Reachable.refl _)
  have hta := fun ε => kempeSwapCompl_isFree_of_reachable c δ η (Reachable.refl a) ε
  have htb := fun ε => kempeSwapCompl_isFree_of_reachable c δ η hl ε
  have hA' : ∀ ε, InA (kempeSwapCompl c δ η a) a b ε ↔ InA c a b ε := by
    intro ε; unfold InA; rw [hta, htb]
  have hnt₁ := hnr (Or.inl hδ₁) hd.at₁.symm hd.bt₁.symm
  have hnt₂ := hnr (Or.inl hδ₂) hd.at₂.symm hd.bt₂.symm
  have hαδ : α ≠ δ := hδα.symm
  have hαη : α ≠ η := h.αβ₁ hd
  have hβ₂δ : β₂ ≠ δ := hδβ₂.symm
  have hβ₂η : β₂ ≠ η := (h.β₁β₂ hd).symm
  have hγ₂δ : γ₂ ≠ δ := fun e => h.not_free_t₂ (e ▸ hδ₂)
  set c' := kempeSwapCompl c δ η a with hc'
  have hcbu : c'.col b u = some α := ccol_keep c h.cbu (Or.inl ⟨hαδ, hαη⟩)
  have hcus₁ : c'.col u s₁ = some η := by
    rw [PEC.col_symm]; exact ccol_keep c h.cs₁u (Or.inr hpass)
  have hcus₂ : c'.col u s₂ = some β₂ := ccol_keep c h.cus₂ (Or.inl ⟨hβ₂δ, hβ₂η⟩)
  have hcst₁ : c'.col s₁ t₁ = some β₂ := ccol_keep c h.cst₁ (Or.inl ⟨hβ₂δ, hβ₂η⟩)
  by_cases h4 : γ₂ = η
  · -- Case 4: `s₂t₂` becomes `δ`, giving Case 2
    subst h4
    have hcst₂ : c'.col s₂ t₂ = some δ := by
      rw [PEC.col_symm]; exact ccol_flip₂ c h.ct₂s hnt₂
    refine hW rfl c' δ ⟨h.cm.kempeSwapCompl δ γ₂ a, hcbu, hcus₁, hcus₂, hcst₁, hcst₂,
      (hta α).2 h.αa, (hA' γ₂).2 h.β₁A, (hA' β₂).2 h.β₂A, (hA' β₂).2 h.γ₁A, (hA' δ).2 hδA,
      (cfree_of_ne c hβ₂δ hβ₂η).2 h.γ₁t₂, (cfree_flip₂ c hnt₁).2 h.γ₂t₁⟩ hδα hδβ₁ hδβ₂
  · -- Case 2: then swap the `F`-avoiding chain `P_a(β₂, β₁)`
    have hcst₂ : c'.col s₂ t₂ = some γ₂ := ccol_keep c h.cst₂ (Or.inl ⟨hγ₂δ, h4⟩)
    have hf : IsFork c' a b u s₁ s₂ t₁ t₂ α η β₂ β₂ γ₂ :=
      ⟨h.cm.kempeSwapCompl δ η a, hcbu, hcus₁, hcus₂, hcst₁, hcst₂, (hta α).2 h.αa,
        (hA' η).2 h.β₁A, (hA' β₂).2 h.β₂A, (hA' β₂).2 h.γ₁A, (hA' γ₂).2 h.γ₂A,
        (cfree_of_ne c hβ₂δ hβ₂η).2 h.γ₁t₂, (cfree_of_ne c hγ₂δ h4).2 h.γ₂t₁⟩
    have hηt₁ : c'.IsFree t₁ η := (cfree_flip₁ c hnt₁).2 hδ₁
    have hβ₂a' : c'.IsFree a β₂ := (hta β₂).2 hβ₂a
    have hηb' : c'.IsFree b η := (htb η).2 hη
    have hs₁ : (c'.kempeGraph β₂ η).Reachable t₁ s₁ :=
      (kempeGraph_adj_of_col (Or.inl hf.ct₁s)).reachable
    have hu : (c'.kempeGraph β₂ η).Reachable t₁ u := reachable_of_col hs₁ (Or.inr hf.cs₁u)
    have hnr' : ∀ {x}, (c'.kempeGraph β₂ η).Reachable t₁ x →
        ¬ (c'.kempeGraph β₂ η).Reachable a x := fun hx =>
      ksAB_not_reach hG hf.cm hβ₂a' hηb' (Or.inr hηt₁) hd.at₁.symm hd.bt₁.symm hx
    have hf' := hf.of_swapAB hG hd hβ₂a' hηb' (h.αβ₂ hd)
      (kcol_keep c' hf.cbu (Or.inl ⟨h.αβ₂ hd, hαη⟩)) (kcol_keep c' hf.cus₁ (Or.inr (hnr' hu)))
      (kcol_keep c' hf.cus₂ (Or.inr (hnr' hu)))
      (by rw [PEC.col_symm]; exact kcol_keep c' hf.ct₁s (Or.inr (hnr' (Reachable.refl t₁))))
      (kcol_keep c' hf.cst₂ (Or.inl ⟨(h.β₂γ₂ hd).symm, h4⟩))
    obtain ⟨δ'', hδ''⟩ := case24_delta hH hf'
    exact case24_b5 hG hd hH hY hZ hf' hγ₂α hδ'' (ksAB_free_b hG hf.cm hβ₂a' hηb')

end Overfull
