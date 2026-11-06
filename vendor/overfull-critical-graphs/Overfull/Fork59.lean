/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.ForkFinal2

/-!
# Fork lemma, Claim 5.9

From a rainbow fork with `{α, β₁, β₂} ⊆ φ̄(t₁) ∩ φ̄(t₂)` and `γ₁ ∈ φ̄(b)`, reach the final
configuration `FinalCfg` (the colouring `φ₂` of Cao–Chen).
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b u s₁ s₂ t₁ t₂ : V}

/-- After recolouring `s₁t₁` by `α` (Claim 5.9 (a), first step). -/
structure Mid0 {k : ℕ} (c : PEC G (Fin k)) (a b u s₁ s₂ t₁ t₂ : V) (α β₁ β₂ γ₂ : Fin k) :
    Prop where
  cm : IsColMinus c a b
  cbu : c.col b u = some α
  cus₁ : c.col u s₁ = some β₁
  cus₂ : c.col u s₂ = some β₂
  cst₁ : c.col s₁ t₁ = some α
  cst₂ : c.col s₂ t₂ = some γ₂
  αa : c.IsFree a α
  β₁A : InA c a b β₁
  β₂A : InA c a b β₂
  γ₂A : InA c a b γ₂
  t₁β₁ : c.IsFree t₁ β₁
  t₁β₂ : c.IsFree t₁ β₂
  t₁γ₂ : c.IsFree t₁ γ₂
  t₂α : c.IsFree t₂ α
  t₂β₁ : c.IsFree t₂ β₁
  t₂β₂ : c.IsFree t₂ β₂

/-- Claim 5.9 (a), first step: swap `P_{t₁}(α, γ₁)`. -/
theorem mid0_of_fork (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    {c : PEC G (Fin G.maxDegree)} {α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree}
    (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) (hr : Rainbow α β₁ β₂ γ₁ γ₂)
    (hT : TFull c t₁ t₂ α β₁ β₂) (hγ₁b : c.IsFree b γ₁) :
    ∃ d : PEC G (Fin G.maxDegree), Mid0 d a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₂ ∧ d.IsFree b γ₁ ∧
      d.IsFree t₂ γ₁ := by
  have hl := ksAB_link hG h.cm h.αa hγ₁b
  have hau := reachable_of_col hl (Or.inl h.cbu)
  have hnr : ∀ {x}, (c.kempeGraph α γ₁).Reachable t₁ x → ¬ (c.kempeGraph α γ₁).Reachable a x :=
    fun hx => ksAB_not_reach hG h.cm h.αa hγ₁b (Or.inl hT.1.1) hd.at₁.symm hd.bt₁.symm hx
  have hnu : ¬ (c.kempeGraph α γ₁).Reachable t₁ u := fun r => hnr r hau
  have hnt₂ : ¬ (c.kempeGraph α γ₁).Reachable t₁ t₂ := fun r =>
    hd.t₁t₂ (eq_of_reachable_of_free_both c hT.1.2 h.γ₁t₂ r.symm)
  have hkeep := fun (z : V) (hz : z = a ∨ z = b) =>
    kempeSwap_keeps_ab hG h.cm (Or.inl h.αa) (Or.inr hγ₁b) (Or.inl hT.1.1) hd.at₁.symm
      hd.bt₁.symm hz
  have hA := inA_kempeSwap_keeps hG h.cm (Or.inl h.αa) (Or.inr hγ₁b) (Or.inl hT.1.1)
    hd.at₁.symm hd.bt₁.symm
  have hβ₁γ₁ := h.β₁γ₁ hd
  have hβ₂γ₁ : β₂ ≠ γ₁ := hr.2.1.symm
  have hγ₂γ₁ : γ₂ ≠ γ₁ := h.γ₁γ₂.symm
  refine ⟨c.kempeSwap α γ₁ t₁, ⟨h.cm.kempeSwap α γ₁ t₁, ?_, kcol_keep c h.cus₁ (Or.inr hnu),
    kcol_keep c h.cus₂ (Or.inl ⟨(h.αβ₂ hd).symm, hβ₂γ₁⟩), ?_,
    kcol_keep c h.cst₂ (Or.inl ⟨hr.2.2.1, hγ₂γ₁⟩), (hkeep a (Or.inl rfl) α).2 h.αa,
    (hA β₁).2 h.β₁A, (hA β₂).2 h.β₂A, (hA γ₂).2 h.γ₂A,
    (kfree_of_ne c (h.αβ₁ hd).symm hβ₁γ₁).2 hT.2.1.1,
    (kfree_of_ne c (h.αβ₂ hd).symm hβ₂γ₁).2 hT.2.2.1,
    (kfree_of_ne c hr.2.2.1 hγ₂γ₁).2 h.γ₂t₁, (kfree_off c hnt₂ α).2 hT.1.2,
    (kfree_off c hnt₂ β₁).2 hT.2.1.2, (kfree_off c hnt₂ β₂).2 hT.2.2.2⟩,
    (hkeep b (Or.inr rfl) γ₁).2 hγ₁b, (kfree_off c hnt₂ γ₁).2 h.γ₁t₂⟩
  · rw [PEC.col_symm]; exact kcol_keep c h.cub (Or.inr hnu)
  · rw [PEC.col_symm]; exact kcol_flip₂ c h.ct₁s (Reachable.refl t₁)

/-- Claim 5.9 (a), rest: move `β₂` to `b`. -/
theorem mid1_of_mid0 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    {d : PEC G (Fin G.maxDegree)} {α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree}
    (h : Mid0 d a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₂) (hγ₁b : d.IsFree b γ₁) (hγ₁t₂ : d.IsFree t₂ γ₁)
    (hαγ₂ : α ≠ γ₂) (hβ₁γ₂ : β₁ ≠ γ₂) (hαγ₁ : α ≠ γ₁) (hβ₁γ₁ : β₁ ≠ γ₁) (hβ₂γ₁ : β₂ ≠ γ₁)
    (hγ₂γ₁ : γ₂ ≠ γ₁) :
    ∃ d' : PEC G (Fin G.maxDegree), Mid0 d' a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₂ ∧ d'.IsFree b β₂ := by
  by_cases hβ₂b : d.IsFree b β₂
  · exact ⟨d, h, hβ₂b⟩
  have hβ₂a : d.IsFree a β₂ := h.β₂A.resolve_right hβ₂b
  have hub : d.col u b = some α := by rw [d.col_symm]; exact h.cbu
  have hαβ₂ : α ≠ β₂ := by rintro rfl; exact hd.bs₂ (d.col_proper hub h.cus₂)
  have hβ₁β₂ : β₁ ≠ β₂ := by rintro rfl; exact hd.s₁s₂ (d.col_proper h.cus₁ h.cus₂)
  have hβ₂γ₂ : β₂ ≠ γ₂ := by
    rintro rfl
    have : d.col s₂ u = some β₂ := by rw [d.col_symm]; exact h.cus₂
    exact hd.ut₂ (d.col_proper this h.cst₂)
  -- first get `γ₂ ∈ φ̄(b)`, keeping `β₂ ∈ φ̄(a)`
  have step : ∃ d₂ : PEC G (Fin G.maxDegree), Mid0 d₂ a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₂ ∧
      d₂.IsFree b γ₂ ∧ d₂.IsFree a β₂ := by
    by_cases hγ₂b : d.IsFree b γ₂
    · exact ⟨d, h, hγ₂b, hβ₂a⟩
    have hγ₂a : d.IsFree a γ₂ := h.γ₂A.resolve_right hγ₂b
    have hnt₂ : ¬ (d.kempeGraph γ₂ γ₁).Reachable a t₂ :=
      ksAB_not_reach hG h.cm hγ₂a hγ₁b (Or.inr hγ₁t₂) hd.at₂.symm hd.bt₂.symm (Reachable.refl t₂)
    have hfo := fun {w} (hwa : w ≠ a) (hwb : w ≠ b) ε =>
      ksAB_free_other hG h.cm hγ₂a hγ₁b hwa hwb ε
    refine ⟨d.kempeSwap γ₂ γ₁ a, ⟨h.cm.kempeSwap γ₂ γ₁ a,
      kcol_keep d h.cbu (Or.inl ⟨hαγ₂, hαγ₁⟩), kcol_keep d h.cus₁ (Or.inl ⟨hβ₁γ₂, hβ₁γ₁⟩),
      kcol_keep d h.cus₂ (Or.inl ⟨hβ₂γ₂, hβ₂γ₁⟩), kcol_keep d h.cst₁ (Or.inl ⟨hαγ₂, hαγ₁⟩),
      ?_, (ksAB_free_a_of_ne hG h.cm hγ₂a hγ₁b hαγ₂ hαγ₁).2 h.αa,
      (ksAB_inA hG h.cm hγ₂a hγ₁b β₁).2 h.β₁A, (ksAB_inA hG h.cm hγ₂a hγ₁b β₂).2 h.β₂A,
      (ksAB_inA hG h.cm hγ₂a hγ₁b γ₂).2 h.γ₂A,
      (hfo hd.at₁.symm hd.bt₁.symm β₁).2 h.t₁β₁, (hfo hd.at₁.symm hd.bt₁.symm β₂).2 h.t₁β₂,
      (hfo hd.at₁.symm hd.bt₁.symm γ₂).2 h.t₁γ₂, (hfo hd.at₂.symm hd.bt₂.symm α).2 h.t₂α,
      (hfo hd.at₂.symm hd.bt₂.symm β₁).2 h.t₂β₁, (hfo hd.at₂.symm hd.bt₂.symm β₂).2 h.t₂β₂⟩,
      ksAB_free_b hG h.cm hγ₂a hγ₁b, (ksAB_free_a_of_ne hG h.cm hγ₂a hγ₁b hβ₂γ₂ hβ₂γ₁).2 hβ₂a⟩
    have : d.col t₂ s₂ = some γ₂ := by rw [d.col_symm]; exact h.cst₂
    rw [PEC.col_symm]; exact kcol_keep d this (Or.inr hnt₂)
  obtain ⟨d₂, h₂, hγ₂b₂, hβ₂a₂⟩ := step
  -- then swap the `F`-avoiding chain `P_a(β₂, γ₂)`
  have ht₂s₂ : d₂.col t₂ s₂ = some γ₂ := by rw [d₂.col_symm]; exact h₂.cst₂
  have hs₂u : d₂.col s₂ u = some β₂ := by rw [d₂.col_symm]; exact h₂.cus₂
  have hs₂ : (d₂.kempeGraph β₂ γ₂).Reachable t₂ s₂ :=
    (kempeGraph_adj_of_col (Or.inr ht₂s₂)).reachable
  have hu : (d₂.kempeGraph β₂ γ₂).Reachable t₂ u := reachable_of_col hs₂ (Or.inl hs₂u)
  have hnr : ∀ {x}, (d₂.kempeGraph β₂ γ₂).Reachable t₂ x → ¬ (d₂.kempeGraph β₂ γ₂).Reachable a x :=
    fun hx => ksAB_not_reach hG h₂.cm hβ₂a₂ hγ₂b₂ (Or.inl h₂.t₂β₂) hd.at₂.symm hd.bt₂.symm hx
  have hfo := fun {w} (hwa : w ≠ a) (hwb : w ≠ b) ε =>
    ksAB_free_other hG h₂.cm hβ₂a₂ hγ₂b₂ hwa hwb ε
  refine ⟨d₂.kempeSwap β₂ γ₂ a, ⟨h₂.cm.kempeSwap β₂ γ₂ a,
    kcol_keep d₂ h₂.cbu (Or.inl ⟨hαβ₂, hαγ₂⟩), kcol_keep d₂ h₂.cus₁ (Or.inl ⟨hβ₁β₂, hβ₁γ₂⟩),
    kcol_keep d₂ h₂.cus₂ (Or.inr (hnr hu)), kcol_keep d₂ h₂.cst₁ (Or.inl ⟨hαβ₂, hαγ₂⟩), ?_,
    (ksAB_free_a_of_ne hG h₂.cm hβ₂a₂ hγ₂b₂ hαβ₂ hαγ₂).2 h₂.αa,
    (ksAB_inA hG h₂.cm hβ₂a₂ hγ₂b₂ β₁).2 h₂.β₁A, (ksAB_inA hG h₂.cm hβ₂a₂ hγ₂b₂ β₂).2 h₂.β₂A,
    (ksAB_inA hG h₂.cm hβ₂a₂ hγ₂b₂ γ₂).2 h₂.γ₂A,
    (hfo hd.at₁.symm hd.bt₁.symm β₁).2 h₂.t₁β₁, (hfo hd.at₁.symm hd.bt₁.symm β₂).2 h₂.t₁β₂,
    (hfo hd.at₁.symm hd.bt₁.symm γ₂).2 h₂.t₁γ₂, (hfo hd.at₂.symm hd.bt₂.symm α).2 h₂.t₂α,
    (hfo hd.at₂.symm hd.bt₂.symm β₁).2 h₂.t₂β₁, (hfo hd.at₂.symm hd.bt₂.symm β₂).2 h₂.t₂β₂⟩,
    ksAB_free_b hG h₂.cm hβ₂a₂ hγ₂b₂⟩
  rw [PEC.col_symm]; exact kcol_keep d₂ ht₂s₂ (Or.inr (hnr (Reachable.refl t₂)))

/-- Claim 5.9 (b): recolour `s₁t₁` by `β₂` and move `β₁` to `b`. -/
theorem final_of_mid1 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    {d : PEC G (Fin G.maxDegree)} {α β₁ β₂ γ₂ : Fin G.maxDegree}
    (h : Mid0 d a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₂) (hβ₂b : d.IsFree b β₂) (hαγ₂ : α ≠ γ₂)
    (hβ₁γ₂ : β₁ ≠ γ₂) :
    ∃ d' : PEC G (Fin G.maxDegree), FinalCfg d' a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₂ := by
  have hub : d.col u b = some α := by rw [d.col_symm]; exact h.cbu
  have hαβ₁ : α ≠ β₁ := by rintro rfl; exact hd.bs₁ (d.col_proper hub h.cus₁)
  have hαβ₂ : α ≠ β₂ := by rintro rfl; exact hd.bs₂ (d.col_proper hub h.cus₂)
  have hβ₁β₂ : β₁ ≠ β₂ := by rintro rfl; exact hd.s₁s₂ (d.col_proper h.cus₁ h.cus₂)
  have hβ₂γ₂ : β₂ ≠ γ₂ := by
    rintro rfl
    have : d.col s₂ u = some β₂ := by rw [d.col_symm]; exact h.cus₂
    exact hd.ut₂ (d.col_proper this h.cst₂)
  have hl := ksAB_link hG h.cm h.αa hβ₂b
  have hau := reachable_of_col hl (Or.inl h.cbu)
  have hnr : ∀ {x}, (d.kempeGraph α β₂).Reachable t₁ x → ¬ (d.kempeGraph α β₂).Reachable a x :=
    fun hx => ksAB_not_reach hG h.cm h.αa hβ₂b (Or.inr h.t₁β₂) hd.at₁.symm hd.bt₁.symm hx
  have hnu : ¬ (d.kempeGraph α β₂).Reachable t₁ u := fun r => hnr r hau
  have hnt₂ : ¬ (d.kempeGraph α β₂).Reachable t₁ t₂ := fun r =>
    hd.t₁t₂ (eq_of_reachable_of_free_both d h.t₂α h.t₂β₂ r.symm)
  have hkeep := fun (z : V) (hz : z = a ∨ z = b) =>
    kempeSwap_keeps_ab hG h.cm (Or.inl h.αa) (Or.inr hβ₂b) (Or.inr h.t₁β₂) hd.at₁.symm
      hd.bt₁.symm hz
  have hA := inA_kempeSwap_keeps hG h.cm (Or.inl h.αa) (Or.inr hβ₂b) (Or.inr h.t₁β₂)
    hd.at₁.symm hd.bt₁.symm
  set d' := d.kempeSwap α β₂ t₁ with hd'
  have hcm' : IsColMinus d' a b := h.cm.kempeSwap α β₂ t₁
  have c'bu : d'.col b u = some α := by rw [d'.col_symm]; exact kcol_keep d hub (Or.inr hnu)
  have c'us₁ : d'.col u s₁ = some β₁ := kcol_keep d h.cus₁ (Or.inl ⟨hαβ₁.symm, hβ₁β₂⟩)
  have c'us₂ : d'.col u s₂ = some β₂ := kcol_keep d h.cus₂ (Or.inr hnu)
  have c'st₁ : d'.col s₁ t₁ = some β₂ := by
    have : d.col t₁ s₁ = some α := by rw [d.col_symm]; exact h.cst₁
    rw [d'.col_symm]; exact kcol_flip₁ d this (Reachable.refl t₁)
  have c'st₂ : d'.col s₂ t₂ = some γ₂ := kcol_keep d h.cst₂ (Or.inl ⟨hαγ₂.symm, hβ₂γ₂.symm⟩)
  have c'αa : d'.IsFree a α := (hkeep a (Or.inl rfl) α).2 h.αa
  have c't₁α : d'.IsFree t₁ α := (kfree_flip₂ d (Reachable.refl t₁)).2 h.t₁β₂
  have c't₁β₁ : d'.IsFree t₁ β₁ := (kfree_of_ne d hαβ₁.symm hβ₁β₂).2 h.t₁β₁
  have c't₁γ₂ : d'.IsFree t₁ γ₂ := (kfree_of_ne d hαγ₂.symm hβ₂γ₂.symm).2 h.t₁γ₂
  have c't₂α : d'.IsFree t₂ α := (kfree_off d hnt₂ α).2 h.t₂α
  have c't₂β₁ : d'.IsFree t₂ β₁ := (kfree_off d hnt₂ β₁).2 h.t₂β₁
  have c't₂β₂ : d'.IsFree t₂ β₂ := (kfree_off d hnt₂ β₂).2 h.t₂β₂
  have c'β₂b : d'.IsFree b β₂ := (hkeep b (Or.inr rfl) β₂).2 hβ₂b
  have c'β₁A : InA d' a b β₁ := (hA β₁).2 h.β₁A
  have c'γ₂A : InA d' a b γ₂ := (hA γ₂).2 h.γ₂A
  by_cases hβ₁b : d'.IsFree b β₁
  · exact ⟨d', hcm', c'bu, c'us₁, c'us₂, c'st₁, c'st₂, c'αa, hβ₁b, Or.inr c'β₂b, c'γ₂A, c't₁α,
      c't₁β₁, c't₁γ₂, c't₂α, c't₂β₁, c't₂β₂⟩
  have hβ₁a : d'.IsFree a β₁ := c'β₁A.resolve_right hβ₁b
  -- swap the `F`-avoiding chain `P_a(β₁, β₂)`
  have ht₁s₁ : d'.col t₁ s₁ = some β₂ := by rw [d'.col_symm]; exact c'st₁
  have hs₁u : d'.col s₁ u = some β₁ := by rw [d'.col_symm]; exact c'us₁
  have hs₁ : (d'.kempeGraph β₁ β₂).Reachable t₁ s₁ :=
    (kempeGraph_adj_of_col (Or.inr ht₁s₁)).reachable
  have hu : (d'.kempeGraph β₁ β₂).Reachable t₁ u := reachable_of_col hs₁ (Or.inl hs₁u)
  have hnr' : ∀ {x}, (d'.kempeGraph β₁ β₂).Reachable t₁ x →
      ¬ (d'.kempeGraph β₁ β₂).Reachable a x := fun hx =>
    ksAB_not_reach hG hcm' hβ₁a c'β₂b (Or.inl c't₁β₁) hd.at₁.symm hd.bt₁.symm hx
  have hfo := fun {w} (hwa : w ≠ a) (hwb : w ≠ b) ε =>
    ksAB_free_other hG hcm' hβ₁a c'β₂b hwa hwb ε
  refine ⟨d'.kempeSwap β₁ β₂ a, hcm'.kempeSwap β₁ β₂ a,
    kcol_keep d' c'bu (Or.inl ⟨hαβ₁, hαβ₂⟩), kcol_keep d' c'us₁ (Or.inr (hnr' hu)),
    kcol_keep d' c'us₂ (Or.inr (hnr' hu)), ?_, kcol_keep d' c'st₂ (Or.inl ⟨hβ₁γ₂.symm,
      hβ₂γ₂.symm⟩), (ksAB_free_a_of_ne hG hcm' hβ₁a c'β₂b hαβ₁ hαβ₂).2 c'αa,
    ksAB_free_b hG hcm' hβ₁a c'β₂b, (ksAB_inA hG hcm' hβ₁a c'β₂b β₂).2 (Or.inr c'β₂b),
    (ksAB_inA hG hcm' hβ₁a c'β₂b γ₂).2 c'γ₂A,
    (hfo hd.at₁.symm hd.bt₁.symm α).2 c't₁α, (hfo hd.at₁.symm hd.bt₁.symm β₁).2 c't₁β₁,
    (hfo hd.at₁.symm hd.bt₁.symm γ₂).2 c't₁γ₂, (hfo hd.at₂.symm hd.bt₂.symm α).2 c't₂α,
    (hfo hd.at₂.symm hd.bt₂.symm β₁).2 c't₂β₁, (hfo hd.at₂.symm hd.bt₂.symm β₂).2 c't₂β₂⟩
  rw [PEC.col_symm]; exact kcol_keep d' ht₁s₁ (Or.inr (hnr' (Reachable.refl t₁)))

/-- **Claim 5.9 and the end of the proof.** A rainbow fork with `T` full and `γ₁ ∈ φ̄(b)` is
impossible. -/
theorem claim59 (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    {c : PEC G (Fin G.maxDegree)} {α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree}
    (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) (hr : Rainbow α β₁ β₂ γ₁ γ₂)
    (hT : TFull c t₁ t₂ α β₁ β₂) (hγ₁b : c.IsFree b γ₁) : False := by
  obtain ⟨d, hm, hb, ht⟩ := mid0_of_fork hG hd h hr hT hγ₁b
  obtain ⟨d', hm', hβ₂b⟩ := mid1_of_mid0 hG hd hm hb ht hr.2.2.1.symm hr.2.2.2.symm hr.1.symm
    (h.β₁γ₁ hd) hr.2.1.symm h.γ₁γ₂.symm
  obtain ⟨d'', hf⟩ := final_of_mid1 hG hd hm' hβ₂b hr.2.2.1.symm hr.2.2.2.symm
  exact hf.contra hG hd hr.2.2.1 hr.2.2.2

end Overfull
