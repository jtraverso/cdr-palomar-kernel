/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.ForkBasic

/-!
# Fork lemma, Claim 5.6: Cases 1 and 3 (`γ₁ = α`)

Cao–Chen (2020), proof of Claim 5.6, items (a1)–(a5). The hypothesis `hX` is what the earlier
cases provide: a fork with the same `α, β₁, β₂, γ₂` and `γ₁ = δ ∉ {α, β₁, β₂}` is impossible
(rainbow in Case 1, Case 2 with the indices exchanged in Case 3).
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b u s₁ s₂ t₁ t₂ : V} {α β₁ β₂ γ₂ : Fin G.maxDegree}

/-- (a1): a delta-colour is missing at `a`. -/
theorem case13_a1 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hX : ∀ (c' : PEC G (Fin G.maxDegree)) (δ' : Fin G.maxDegree),
      IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ δ' γ₂ → δ' ≠ α → δ' ≠ β₁ → δ' ≠ β₂ → False)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂)
    {δ : Fin G.maxDegree} (hδA : InA c a b δ) (hδ₁ : c.IsFree t₁ δ) (hδ₂ : c.IsFree t₂ δ)
    (hδα : δ ≠ α) (hδβ₁ : δ ≠ β₁) (hδβ₂ : δ ≠ β₂) : c.IsFree a δ := by
  by_contra hδa
  have hδb : c.IsFree b δ := hδA.resolve_left hδa
  have hlink := ksAB_link hG h.cm h.αa hδb
  have hbr : ¬ (c.kempeGraph α δ).Reachable t₁ b := fun r =>
    ksAB_not_reach hG h.cm h.αa hδb (Or.inr hδ₁) hd.at₁.symm hd.bt₁.symm r hlink
  have hγ₂α : γ₂ ≠ α := h.γ₁γ₂.symm
  have hγ₂δ : γ₂ ≠ δ := fun e => h.not_free_t₂ (e ▸ hδ₂)
  have ht₂ : ¬ (c.kempeGraph α δ).Reachable t₁ t₂ := fun r =>
    hd.t₁t₂ (eq_of_reachable_of_free_both c h.γ₁t₂ hδ₂ r.symm)
  have hkeep := fun (z : V) (hz : z = a ∨ z = b) =>
    kempeSwap_keeps_ab hG h.cm (Or.inl h.αa) hδA (Or.inr hδ₁) hd.at₁.symm hd.bt₁.symm hz
  have hA := inA_kempeSwap_keeps hG h.cm (Or.inl h.αa) hδA (Or.inr hδ₁) hd.at₁.symm hd.bt₁.symm
  refine hX (c.kempeSwap α δ t₁) δ ⟨h.cm.kempeSwap α δ t₁, kcol_keep c h.cbu (Or.inr hbr),
    kcol_keep c h.cus₁ (Or.inl ⟨(h.αβ₁ hd).symm, hδβ₁.symm⟩),
    kcol_keep c h.cus₂ (Or.inl ⟨(h.αβ₂ hd).symm, hδβ₂.symm⟩), ?_,
    kcol_keep c h.cst₂ (Or.inl ⟨hγ₂α, hγ₂δ⟩), (hkeep a (Or.inl rfl) α).2 h.αa, (hA β₁).2 h.β₁A,
    (hA β₂).2 h.β₂A, (hA δ).2 hδA, (hA γ₂).2 h.γ₂A, (kfree_off c ht₂ δ).2 hδ₂,
    (kfree_of_ne c hγ₂α hγ₂δ).2 h.γ₂t₁⟩ hδα hδβ₁ hδβ₂
  rw [PEC.col_symm]
  exact kcol_flip₁ c h.ct₁s (Reachable.refl t₁)

/-- (a2): for `η ∈ φ̄(b)`, the chain `P_a(δ, η)` passes along `us₁` or `us₂`. -/
theorem case13_a2 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hX : ∀ (c' : PEC G (Fin G.maxDegree)) (δ' : Fin G.maxDegree),
      IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ δ' γ₂ → δ' ≠ α → δ' ≠ β₁ → δ' ≠ β₂ → False)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂)
    {δ : Fin G.maxDegree} (hδA : InA c a b δ) (hδ₁ : c.IsFree t₁ δ) (hδ₂ : c.IsFree t₂ δ)
    (hδα : δ ≠ α) (hδβ₁ : δ ≠ β₁) (hδβ₂ : δ ≠ β₂) {η : Fin G.maxDegree} (hηb : c.IsFree b η)
    (h₁ : η ≠ β₁ ∨ ¬ (c.kempeGraph δ η).Reachable a s₁)
    (h₂ : η ≠ β₂ ∨ ¬ (c.kempeGraph δ η).Reachable a s₂) : False := by
  have hδa := case13_a1 hG hd hX h hδA hδ₁ hδ₂ hδα hδβ₁ hδβ₂
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have hαη : α ≠ η := fun e => hdis α h.αa (e ▸ hηb)
  have hαδ : α ≠ δ := hδα.symm
  have hnr₂ : ¬ (c.kempeGraph δ η).Reachable a t₂ :=
    ksAB_not_reach hG h.cm hδa hηb (Or.inl hδ₂) hd.at₂.symm hd.bt₂.symm (Reachable.refl t₂)
  have hfork : IsFork (c.kempeSwap δ η a) a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂ := by
    refine ⟨h.cm.kempeSwap δ η a, kcol_keep c h.cbu (Or.inl ⟨hαδ, hαη⟩), ?_, ?_,
      kcol_keep c h.cst₁ (Or.inl ⟨hαδ, hαη⟩), ?_,
      (ksAB_free_a_of_ne hG h.cm hδa hηb hαδ hαη).2 h.αa, (ksAB_inA hG h.cm hδa hηb β₁).2 h.β₁A,
      (ksAB_inA hG h.cm hδa hηb β₂).2 h.β₂A, (ksAB_inA hG h.cm hδa hηb α).2 h.γ₁A,
      (ksAB_inA hG h.cm hδa hηb γ₂).2 h.γ₂A,
      (ksAB_free_other hG h.cm hδa hηb hd.at₂.symm hd.bt₂.symm α).2 h.γ₁t₂,
      (ksAB_free_other hG h.cm hδa hηb hd.at₁.symm hd.bt₁.symm γ₂).2 h.γ₂t₁⟩
    · rw [PEC.col_symm]
      exact kcol_keep c h.cs₁u (h₁.elim (fun hne => Or.inl ⟨hδβ₁.symm, hne.symm⟩) Or.inr)
    · rw [PEC.col_symm]
      exact kcol_keep c h.cs₂u (h₂.elim (fun hne => Or.inl ⟨hδβ₂.symm, hne.symm⟩) Or.inr)
    · rw [PEC.col_symm]
      exact kcol_keep c h.ct₂s (Or.inr hnr₂)
  have hδa' := case13_a1 hG hd hX hfork ((ksAB_inA hG h.cm hδa hηb δ).2 hδA)
    ((ksAB_free_other hG h.cm hδa hηb hd.at₁.symm hd.bt₁.symm δ).2 hδ₁)
    ((ksAB_free_other hG h.cm hδa hηb hd.at₂.symm hd.bt₂.symm δ).2 hδ₂) hδα hδβ₁ hδβ₂
  exact (hfork.cm.ab_facts hG).1 δ hδa' (ksAB_free_b hG h.cm hδa hηb)

/-- (a3): `β₁` is not missing at both `b` and `t₁`. -/
theorem case13_a3 (hd : Distinct7 a b u s₁ s₂ t₁ t₂) (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂)
    (hb : c.IsFree b β₁) (ht : c.IsFree t₁ β₁) : False := by
  have hl := ksAB_link hG h.cm h.αa hb
  have r1 := reachable_of_col hl (Or.inl h.cbu)
  have r2 := reachable_of_col r1 (Or.inr h.cus₁)
  have r3 := reachable_of_col r2 (Or.inl h.cst₁)
  exact not_three_linked c h.cm.adj.ne hd.at₁ hd.bt₁ (Or.inl h.αa) (Or.inr hb) (Or.inr ht) hl r3

/-- (a4): `β₁ ∈ φ̄(b) ∖ φ̄(t₁)` with `P_a(δ, β₁)` through `s₁` is impossible. -/
theorem case13_a4 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hX : ∀ (c' : PEC G (Fin G.maxDegree)) (δ' : Fin G.maxDegree),
      IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ δ' γ₂ → δ' ≠ α → δ' ≠ β₁ → δ' ≠ β₂ → False)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂)
    {δ : Fin G.maxDegree} (hδA : InA c a b δ) (hδ₁ : c.IsFree t₁ δ) (hδ₂ : c.IsFree t₂ δ)
    (hδα : δ ≠ α) (hδβ₁ : δ ≠ β₁) (hδβ₂ : δ ≠ β₂) (hb : c.IsFree b β₁) (ht : ¬ c.IsFree t₁ β₁)
    (hpass : (c.kempeGraph δ β₁).Reachable a s₁) : False := by
  have hδa := case13_a1 hG hd hX h hδA hδ₁ hδ₂ hδα hδβ₁ hδβ₂
  have hs₁ : ¬ (c.kempeGraph δ β₁).Reachable t₁ s₁ := fun r =>
    ksAB_not_reach hG h.cm hδa hb (Or.inl hδ₁) hd.at₁.symm hd.bt₁.symm r hpass
  have hγ₂β₁ : γ₂ ≠ β₁ := fun e => ht (e ▸ h.γ₂t₁)
  have hγ₂δ : γ₂ ≠ δ := fun e => h.not_free_t₂ (e ▸ hδ₂)
  have hαδ : α ≠ δ := hδα.symm
  have hαβ₁ : α ≠ β₁ := h.αβ₁ hd
  have hkeep := fun (z : V) (hz : z = a ∨ z = b) =>
    kempeSwap_keeps_ab hG h.cm hδA (Or.inr hb) (Or.inl hδ₁) hd.at₁.symm hd.bt₁.symm hz
  have hA := inA_kempeSwap_keeps hG h.cm hδA (Or.inr hb) (Or.inl hδ₁) hd.at₁.symm hd.bt₁.symm
  have hfork : IsFork (c.kempeSwap δ β₁ t₁) a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂ := by
    refine ⟨h.cm.kempeSwap δ β₁ t₁, kcol_keep c h.cbu (Or.inl ⟨hαδ, hαβ₁⟩), ?_,
      kcol_keep c h.cus₂ (Or.inl ⟨hδβ₂.symm, (h.β₁β₂ hd).symm⟩),
      kcol_keep c h.cst₁ (Or.inl ⟨hαδ, hαβ₁⟩), kcol_keep c h.cst₂ (Or.inl ⟨hγ₂δ, hγ₂β₁⟩),
      (hkeep a (Or.inl rfl) α).2 h.αa, (hA β₁).2 h.β₁A, (hA β₂).2 h.β₂A, (hA α).2 h.γ₁A,
      (hA γ₂).2 h.γ₂A, (kfree_of_ne c hαδ hαβ₁).2 h.γ₁t₂, (kfree_of_ne c hγ₂δ hγ₂β₁).2 h.γ₂t₁⟩
    rw [PEC.col_symm]
    exact kcol_keep c h.cs₁u (Or.inr hs₁)
  exact case13_a3 hd hG hfork ((hkeep b (Or.inr rfl) β₁).2 hb)
    ((kfree_flip₁ c (Reachable.refl t₁)).2 hδ₁)

/-- **Claim 5.6, Cases 1 and 3.** A fork with `γ₁ = α` is impossible, given `hX`. -/
theorem case13 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    (hH : ForkHyp G a b t₁ t₂)
    (hX : ∀ (c' : PEC G (Fin G.maxDegree)) (δ' : Fin G.maxDegree),
      IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ δ' γ₂ → δ' ≠ α → δ' ≠ β₁ → δ' ≠ β₂ → False)
    {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂) : False := by
  -- a delta-colour for any such fork
  have hdelta : ∀ {c' : PEC G (Fin G.maxDegree)},
      IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂ → ∃ δ, InA c' a b δ ∧ c'.IsFree t₁ δ ∧
        c'.IsFree t₂ δ ∧ δ ≠ α ∧ δ ≠ β₁ ∧ δ ≠ β₂ := by
    intro c' h'
    obtain ⟨δ, h1, h2, hA, ht₁, ht₂⟩ := (hH c' h'.cm).1 β₁ β₂
    exact ⟨δ, hA, ht₁, ht₂, fun e => h'.not_free_t₁ (e ▸ ht₁), h1, h2⟩
  obtain ⟨δ, hδA, hδ₁, hδ₂, hδα, hδβ₁, hδβ₂⟩ := hdelta h
  have hδa := case13_a1 hG hd hX h hδA hδ₁ hδ₂ hδα hδβ₁ hδβ₂
  have hβ₁₂ := h.β₁β₂ hd
  -- every colour missing at `b` is `β₂`
  have hall : ∀ η, c.IsFree b η → η = β₂ := by
    intro η hη
    by_contra hne
    by_cases h1 : η = β₁
    · subst h1
      by_cases hp : (c.kempeGraph δ η).Reachable a s₁
      · by_cases ht : c.IsFree t₁ η
        · exact case13_a3 hd hG h hη ht
        · exact case13_a4 hG hd hX h hδA hδ₁ hδ₂ hδα hδβ₁ hδβ₂ hη ht hp
      · exact case13_a2 hG hd hX h hδA hδ₁ hδ₂ hδα hδβ₁ hδβ₂ hη (Or.inr hp) (Or.inl hne)
    · exact case13_a2 hG hd hX h hδA hδ₁ hδ₂ hδα hδβ₁ hδβ₂ hη (Or.inl h1) (Or.inl hne)
  obtain ⟨η, hη⟩ := h.cm.exists_free_right
  have hβ₂b : c.IsFree b β₂ := hall η hη ▸ hη
  have hpass₂ : (c.kempeGraph δ β₂).Reachable a s₂ := by
    by_contra hp
    exact case13_a2 hG hd hX h hδA hδ₁ hδ₂ hδα hδβ₁ hδβ₂ hβ₂b (Or.inl hβ₁₂.symm) (Or.inr hp)
  have hγ₂a : c.IsFree a γ₂ :=
    h.γ₂A.resolve_right fun hb => (h.β₂γ₂ hd) (hall γ₂ hb).symm
  -- switch `δ, β₂` on all chains except `P_a(δ, β₂)`
  have hl := ksAB_link hG h.cm hδa hβ₂b
  have hnr : ∀ {w}, (c.IsFree w δ ∨ c.IsFree w β₂) → w ≠ a → w ≠ b →
      ¬ (c.kempeGraph δ β₂).Reachable a w := fun hw hwa hwb =>
    ksAB_not_reach hG h.cm hδa hβ₂b hw hwa hwb (Reachable.refl _)
  have hta := fun ε => kempeSwapCompl_isFree_of_reachable c δ β₂ (Reachable.refl a) ε
  have htb := fun ε => kempeSwapCompl_isFree_of_reachable c δ β₂ hl ε
  have hA' : ∀ ε, InA (kempeSwapCompl c δ β₂ a) a b ε ↔ InA c a b ε := by
    intro ε; unfold InA; rw [hta, htb]
  have hαδ : α ≠ δ := hδα.symm
  have hαβ₂ : α ≠ β₂ := h.αβ₂ hd
  have hγ₂δ : γ₂ ≠ δ := fun e => h.not_free_t₂ (e ▸ hδ₂)
  have hγ₂β₂ : γ₂ ≠ β₂ := (h.β₂γ₂ hd).symm
  have hγ₂α : γ₂ ≠ α := h.γ₁γ₂.symm
  set c' := kempeSwapCompl c δ β₂ a with hc'
  have hβ₂t₁ : c'.IsFree t₁ β₂ := (cfree_flip₁ c (hnr (Or.inl hδ₁) hd.at₁.symm hd.bt₁.symm)).2 hδ₁
  have hβ₂t₂ : c'.IsFree t₂ β₂ := (cfree_flip₁ c (hnr (Or.inl hδ₂) hd.at₂.symm hd.bt₂.symm)).2 hδ₂
  have hf' : IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂ := by
    refine ⟨h.cm.kempeSwapCompl δ β₂ a, ccol_keep c h.cbu (Or.inl ⟨hαδ, hαβ₂⟩),
      ccol_keep c h.cus₁ (Or.inl ⟨hδβ₁.symm, hβ₁₂⟩), ?_, ccol_keep c h.cst₁ (Or.inl ⟨hαδ, hαβ₂⟩),
      ccol_keep c h.cst₂ (Or.inl ⟨hγ₂δ, hγ₂β₂⟩), (hta α).2 h.αa, (hA' β₁).2 h.β₁A,
      (hA' β₂).2 h.β₂A, (hA' α).2 h.γ₁A, (hA' γ₂).2 h.γ₂A, (cfree_of_ne c hαδ hαβ₂).2 h.γ₁t₂,
      (cfree_of_ne c hγ₂δ hγ₂β₂).2 h.γ₂t₁⟩
    rw [PEC.col_symm]
    exact ccol_keep c h.cs₂u (Or.inr hpass₂)
  -- swap the F-avoiding chain `P_a(γ₂, β₂)`
  have hγ₂a' : c'.IsFree a γ₂ := (hta γ₂).2 hγ₂a
  have hβ₂b' : c'.IsFree b β₂ := (htb β₂).2 hβ₂b
  have hs₂r : (c'.kempeGraph γ₂ β₂).Reachable t₂ s₂ :=
    (kempeGraph_adj_of_col (Or.inl hf'.ct₂s)).reachable
  have hur : (c'.kempeGraph γ₂ β₂).Reachable t₂ u := reachable_of_col hs₂r (Or.inr hf'.cs₂u)
  have hnu : ¬ (c'.kempeGraph γ₂ β₂).Reachable a u :=
    ksAB_not_reach hG hf'.cm hγ₂a' hβ₂b' (Or.inr hβ₂t₂) hd.at₂.symm hd.bt₂.symm hur
  have hns₂ : ¬ (c'.kempeGraph γ₂ β₂).Reachable a s₂ :=
    ksAB_not_reach hG hf'.cm hγ₂a' hβ₂b' (Or.inr hβ₂t₂) hd.at₂.symm hd.bt₂.symm hs₂r
  have hf'' : IsFork (c'.kempeSwap γ₂ β₂ a) a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂ := by
    refine ⟨hf'.cm.kempeSwap γ₂ β₂ a, ?_, kcol_keep c' hf'.cus₁ (Or.inr hnu),
      kcol_keep c' hf'.cus₂ (Or.inr hnu), kcol_keep c' hf'.cst₁ (Or.inl ⟨hγ₂α.symm, hαβ₂⟩),
      kcol_keep c' hf'.cst₂ (Or.inr hns₂),
      (ksAB_free_a_of_ne hG hf'.cm hγ₂a' hβ₂b' hγ₂α.symm hαβ₂).2 hf'.αa,
      (ksAB_inA hG hf'.cm hγ₂a' hβ₂b' β₁).2 hf'.β₁A, (ksAB_inA hG hf'.cm hγ₂a' hβ₂b' β₂).2 hf'.β₂A,
      (ksAB_inA hG hf'.cm hγ₂a' hβ₂b' α).2 hf'.γ₁A, (ksAB_inA hG hf'.cm hγ₂a' hβ₂b' γ₂).2 hf'.γ₂A,
      (ksAB_free_other hG hf'.cm hγ₂a' hβ₂b' hd.at₂.symm hd.bt₂.symm α).2 hf'.γ₁t₂,
      (ksAB_free_other hG hf'.cm hγ₂a' hβ₂b' hd.at₁.symm hd.bt₁.symm γ₂).2 hf'.γ₂t₁⟩
    rw [PEC.col_symm]
    exact kcol_keep c' hf'.cub (Or.inr hnu)
  have hγ₂b'' : (c'.kempeSwap γ₂ β₂ a).IsFree b γ₂ := ksAB_free_b hG hf'.cm hγ₂a' hβ₂b'
  by_cases hγ₂β₁ : γ₂ = β₁
  · subst hγ₂β₁
    exact case13_a3 hd hG hf'' hγ₂b'' hf''.γ₂t₁
  · obtain ⟨δ'', hA'', h₁'', h₂'', hα'', hβ₁'', hβ₂''⟩ := hdelta hf''
    exact case13_a2 hG hd hX hf'' hA'' h₁'' h₂'' hα'' hβ₁'' hβ₂'' hγ₂b'' (Or.inl hγ₂β₁)
      (Or.inl hγ₂β₂)

end Overfull
