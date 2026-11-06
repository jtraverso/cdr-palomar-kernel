/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Fork57a

/-!
# Fork lemma, Claim 5.7: Case 2 and the induction on `t(φ)`

If no rainbow fork has `{α, β₁, β₂} ⊆ φ̄(t₁) ∩ φ̄(t₂)`, then no rainbow fork exists.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b u s₁ s₂ t₁ t₂ : V}

theorem both_swap {k : ℕ} {c : PEC G (Fin k)} {x : Fin k} : Both c t₂ t₁ x ↔ Both c t₁ t₂ x :=
  and_comm

theorem IsDelta.swap {k : ℕ} {c : PEC G (Fin k)} {α β₁ β₂ δ : Fin k}
    (h : IsDelta c a b t₁ t₂ α β₁ β₂ δ) : IsDelta c a b t₂ t₁ α β₂ β₁ δ :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

variable (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂) (hH : ForkHyp G a b t₁ t₂)
  {α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree} (hr : Rainbow α β₁ β₂ γ₁ γ₂) {k : ℕ}
  (hup : Up57 G a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ k)
include hG hd hH hr hup

/-- **Claim 5.7, Case 1.** `α ∉ T` is impossible. -/
theorem c57_case1 {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂)
    (hk : k ≤ tval c t₁ t₂ α β₁ β₂) (hαT : ¬ Both c t₁ t₂ α) : False := by
  obtain ⟨δ, hδ⟩ := delta57 hH h (fun hall => hαT hall.1)
  obtain ⟨η, hη⟩ := h.cm.exists_free_right
  by_cases h1 : η = β₁
  · subst h1
    exact c57_a3 hG hd hr hup h hH hk hαT hδ hη
  by_cases h2 : η = β₂
  · subst h2
    exact c57_a3 hG hd.swap hr.swap hup.swap h.swap hH.swap (by rw [tval_swap]; exact hk)
      (fun hb => hαT (both_swap.1 hb)) hδ.swap hη
  exact c57_a2 hG hd hr hup h hk hαT hδ hη (Or.inl h1) (Or.inl h2)

/-- Case 2 (b1): if `α ∈ T` and `β₁ ∉ T`, then `β₁ ∈ φ̄(a)`. -/
theorem c57_b1 {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂)
    (hk : k ≤ tval c t₁ t₂ α β₁ β₂) (hαT : Both c t₁ t₂ α) (hβ₁T : ¬ Both c t₁ t₂ β₁) :
    c.IsFree a β₁ := by
  by_contra hβ₁a
  have hβ₁b : c.IsFree b β₁ := h.β₁A.resolve_left hβ₁a
  have hl := ksAB_link hG h.cm h.αa hβ₁b
  have hu : (c.kempeGraph α β₁).Reachable a u := reachable_of_col hl (Or.inl h.cbu)
  have hnr : ∀ {w}, (c.IsFree w α ∨ c.IsFree w β₁) → w ≠ a → w ≠ b →
      ¬ (c.kempeGraph α β₁).Reachable a w := fun hw hwa hwb =>
    ksAB_not_reach hG h.cm h.αa hβ₁b hw hwa hwb (Reachable.refl _)
  have hnt₁ := hnr (Or.inl hαT.1) hd.at₁.symm hd.bt₁.symm
  have hnt₂ := hnr (Or.inl hαT.2) hd.at₂.symm hd.bt₂.symm
  have hta := fun ε => kempeSwapCompl_isFree_of_reachable c α β₁ (Reachable.refl a) ε
  have htb := fun ε => kempeSwapCompl_isFree_of_reachable c α β₁ hl ε
  have hA' : ∀ ε, InA (kempeSwapCompl c α β₁ a) a b ε ↔ InA c a b ε := by
    intro ε; unfold InA; rw [hta, htb]
  have hαβ₁ := h.αβ₁ hd
  have hβ₂α := (h.αβ₂ hd).symm
  have hβ₂β₁ := (h.β₁β₂ hd).symm
  have hγ₁β₁ := (h.β₁γ₁ hd).symm
  set c' := kempeSwapCompl c α β₁ a with hc'
  have hf : IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ :=
    ⟨h.cm.kempeSwapCompl α β₁ a, ccol_keep c h.cbu (Or.inr hl), ccol_keep c h.cus₁ (Or.inr hu),
      ccol_keep c h.cus₂ (Or.inl ⟨hβ₂α, hβ₂β₁⟩), ccol_keep c h.cst₁ (Or.inl ⟨hr.1, hγ₁β₁⟩),
      ccol_keep c h.cst₂ (Or.inl ⟨hr.2.2.1, hr.2.2.2⟩), (hta α).2 h.αa, (hA' β₁).2 h.β₁A,
      (hA' β₂).2 h.β₂A, (hA' γ₁).2 h.γ₁A, (hA' γ₂).2 h.γ₂A,
      (cfree_of_ne c hr.1 hγ₁β₁).2 h.γ₁t₂, (cfree_of_ne c hr.2.2.1 hr.2.2.2).2 h.γ₂t₁⟩
  have hbα : Both c' t₁ t₂ α ↔ Both c t₁ t₂ β₁ := by
    unfold Both; rw [cfree_flip₂ c hnt₁, cfree_flip₂ c hnt₂]
  have hbβ₁ : Both c' t₁ t₂ β₁ ↔ Both c t₁ t₂ α := by
    unfold Both; rw [cfree_flip₁ c hnt₁, cfree_flip₁ c hnt₂]
  have hbβ₂ : Both c' t₁ t₂ β₂ ↔ Both c t₁ t₂ β₂ := by
    unfold Both; rw [cfree_of_ne c hβ₂α hβ₂β₁, cfree_of_ne c hβ₂α hβ₂β₁]
  have heq := tval_exchange hαT (fun hb => hβ₁T (hbα.1 hb)) hβ₁T (hbβ₁.2 hαT) hbβ₂
  exact c57_case1 hG hd hH hr hup hf (by rw [heq]; exact hk) (fun hb => hβ₁T (hbα.1 hb))

/-- Case 2 (b2): a delta-colour is missing at `a`. -/
theorem c57_b2 {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂)
    (hk : k ≤ tval c t₁ t₂ α β₁ β₂) (hαT : Both c t₁ t₂ α) (hβ₁T : ¬ Both c t₁ t₂ β₁)
    {δ : Fin G.maxDegree} (hδ : IsDelta c a b t₁ t₂ α β₁ β₂ δ) : c.IsFree a δ := by
  have hβ₁a := c57_b1 hG hd hH hr hup h hk hαT hβ₁T
  have hδ' := hδ
  obtain ⟨hδA, hδ₁, hδ₂, hδα, hδβ₁, hδβ₂⟩ := hδ
  by_contra hδa
  have hδb : c.IsFree b δ := hδA.resolve_left hδa
  have hnr : ∀ {w}, (c.IsFree w β₁ ∨ c.IsFree w δ) → w ≠ a → w ≠ b →
      ¬ (c.kempeGraph β₁ δ).Reachable a w := fun hw hwa hwb =>
    ksAB_not_reach hG h.cm hβ₁a hδb hw hwa hwb (Reachable.refl _)
  have hnt₁ := hnr (Or.inr hδ₁) hd.at₁.symm hd.bt₁.symm
  have hnt₂ := hnr (Or.inr hδ₂) hd.at₂.symm hd.bt₂.symm
  have hαβ₁ := h.αβ₁ hd
  have hβ₂β₁ := (h.β₁β₂ hd).symm
  have hγ₁β₁ := (h.β₁γ₁ hd).symm
  have hγ₁δ : γ₁ ≠ δ := fun e => h.not_free_t₁ (e ▸ hδ₁)
  have hγ₂δ : γ₂ ≠ δ := fun e => h.not_free_t₂ (e ▸ hδ₂)
  by_cases hp : (c.kempeGraph β₁ δ).Reachable a s₁
  · -- switch `β₁, δ` on all other chains: `β₁` joins `T`
    have hl := ksAB_link hG h.cm hβ₁a hδb
    have hta := fun ε => kempeSwapCompl_isFree_of_reachable c β₁ δ (Reachable.refl a) ε
    have htb := fun ε => kempeSwapCompl_isFree_of_reachable c β₁ δ hl ε
    have hA' : ∀ ε, InA (kempeSwapCompl c β₁ δ a) a b ε ↔ InA c a b ε := by
      intro ε; unfold InA; rw [hta, htb]
    set c' := kempeSwapCompl c β₁ δ a with hc'
    have hf : IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ :=
      ⟨h.cm.kempeSwapCompl β₁ δ a, ccol_keep c h.cbu (Or.inl ⟨hαβ₁, hδα.symm⟩),
        by rw [PEC.col_symm]; exact ccol_keep c h.cs₁u (Or.inr hp),
        ccol_keep c h.cus₂ (Or.inl ⟨hβ₂β₁, hδβ₂.symm⟩),
        ccol_keep c h.cst₁ (Or.inl ⟨hγ₁β₁, hγ₁δ⟩), ccol_keep c h.cst₂ (Or.inl ⟨hr.2.2.2, hγ₂δ⟩),
        (hta α).2 h.αa, (hA' β₁).2 h.β₁A, (hA' β₂).2 h.β₂A, (hA' γ₁).2 h.γ₁A, (hA' γ₂).2 h.γ₂A,
        (cfree_of_ne c hγ₁β₁ hγ₁δ).2 h.γ₁t₂, (cfree_of_ne c hr.2.2.2 hγ₂δ).2 h.γ₂t₁⟩
    refine hup c' hf (lt_of_le_of_lt hk (tval_lt_β₁ (fun hb => ⟨?_, ?_⟩) hβ₁T
      ⟨(cfree_flip₂ c hnt₁).2 hδ₁, (cfree_flip₂ c hnt₂).2 hδ₂⟩ (fun hb => ⟨?_, ?_⟩)))
    · exact (cfree_of_ne c hαβ₁ hδα.symm).2 hb.1
    · exact (cfree_of_ne c hαβ₁ hδα.symm).2 hb.2
    · exact (cfree_of_ne c hβ₂β₁ hδβ₂.symm).2 hb.1
    · exact (cfree_of_ne c hβ₂β₁ hδβ₂.symm).2 hb.2
  · -- the chain `P_a(β₁, δ)` avoids `F`: swapping it puts `β₁` at `b`
    have hf := h.of_swapAB hG hd hβ₁a hδb hαβ₁ (kcol_keep c h.cbu (Or.inl ⟨hαβ₁, hδα.symm⟩))
      (by rw [PEC.col_symm]; exact kcol_keep c h.cs₁u (Or.inr hp))
      (kcol_keep c h.cus₂ (Or.inl ⟨hβ₂β₁, hδβ₂.symm⟩))
      (by rw [PEC.col_symm]; exact kcol_keep c h.ct₁s (Or.inr hnt₁))
      (by rw [PEC.col_symm]; exact kcol_keep c h.ct₂s (Or.inr hnt₂))
    have hfree := fun {w} (hwa : w ≠ a) (hwb : w ≠ b) ε =>
      ksAB_free_other hG h.cm hβ₁a hδb hwa hwb ε
    have hboth : ∀ x, Both (c.kempeSwap β₁ δ a) t₁ t₂ x ↔ Both c t₁ t₂ x := fun x => by
      unfold Both; rw [hfree hd.at₁.symm hd.bt₁.symm, hfree hd.at₂.symm hd.bt₂.symm]
    have := c57_b1 hG hd hH hr hup hf (by rw [tval_eq_of (hboth α) (hboth β₁) (hboth β₂)]; exact hk)
      ((hboth α).2 hαT) (fun hb => hβ₁T ((hboth β₁).1 hb))
    exact (hf.cm.ab_facts hG).1 β₁ this (ksAB_free_b hG h.cm hβ₁a hδb)

/-- Case 2 (b3): every colour missing at `b` is `β₂`. -/
theorem c57_b3 {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂)
    (hk : k ≤ tval c t₁ t₂ α β₁ β₂) (hαT : Both c t₁ t₂ α) (hβ₁T : ¬ Both c t₁ t₂ β₁)
    {η : Fin G.maxDegree} (hηb : c.IsFree b η) (hηβ₂ : η ≠ β₂) : False := by
  obtain ⟨δ, hδ⟩ := delta57 hH h (fun hall => hβ₁T hall.2.1)
  have hδa := c57_b2 hG hd hH hr hup h hk hαT hβ₁T hδ
  have hβ₁a := c57_b1 hG hd hH hr hup h hk hαT hβ₁T
  have hδ' := hδ
  obtain ⟨hδA, hδ₁, hδ₂, hδα, hδβ₁, hδβ₂⟩ := hδ
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have hαη : α ≠ η := fun e => hdis α h.αa (e ▸ hηb)
  have hβ₁η : β₁ ≠ η := fun e => hdis β₁ hβ₁a (e ▸ hηb)
  have hnr : ∀ {w}, (c.IsFree w δ ∨ c.IsFree w η) → w ≠ a → w ≠ b →
      ¬ (c.kempeGraph δ η).Reachable a w := fun hw hwa hwb =>
    ksAB_not_reach hG h.cm hδa hηb hw hwa hwb (Reachable.refl _)
  have hf := h.of_swapAB hG hd hδa hηb hδα.symm (kcol_keep c h.cbu (Or.inl ⟨hδα.symm, hαη⟩))
    (kcol_keep c h.cus₁ (Or.inl ⟨hδβ₁.symm, hβ₁η⟩))
    (kcol_keep c h.cus₂ (Or.inl ⟨hδβ₂.symm, hηβ₂.symm⟩))
    (by rw [PEC.col_symm]; exact kcol_keep c h.ct₁s (Or.inr (hnr (Or.inl hδ₁) hd.at₁.symm
      hd.bt₁.symm)))
    (by rw [PEC.col_symm]; exact kcol_keep c h.ct₂s (Or.inr (hnr (Or.inl hδ₂) hd.at₂.symm
      hd.bt₂.symm)))
  have hfree := fun {w} (hwa : w ≠ a) (hwb : w ≠ b) ε =>
    ksAB_free_other hG h.cm hδa hηb hwa hwb ε
  have hboth : ∀ x, Both (c.kempeSwap δ η a) t₁ t₂ x ↔ Both c t₁ t₂ x := fun x => by
    unfold Both; rw [hfree hd.at₁.symm hd.bt₁.symm, hfree hd.at₂.symm hd.bt₂.symm]
  have := c57_b2 hG hd hH hr hup hf (by rw [tval_eq_of (hboth α) (hboth β₁) (hboth β₂)]; exact hk)
    ((hboth α).2 hαT) (fun hb => hβ₁T ((hboth β₁).1 hb))
    (IsDelta.of_swapAB hG h.cm hd.at₁ hd.at₂ hd.bt₁ hd.bt₂ hδ' hδa hηb)
  exact (hf.cm.ab_facts hG).1 δ this (ksAB_free_b hG h.cm hδa hηb)

/-- **Claim 5.7, Case 2.** `α ∈ T` and `β₁ ∉ T` is impossible. -/
theorem c57_case2 {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂)
    (hk : k ≤ tval c t₁ t₂ α β₁ β₂) (hαT : Both c t₁ t₂ α) (hβ₁T : ¬ Both c t₁ t₂ β₁) :
    False := by
  obtain ⟨η, hη⟩ := h.cm.exists_free_right
  have hηβ₂ : η = β₂ := by
    by_contra hne
    exact c57_b3 hG hd hH hr hup h hk hαT hβ₁T hη hne
  subst hηβ₂
  have hγ₂a : c.IsFree a γ₂ := h.γ₂A.resolve_right fun hb =>
    c57_b3 hG hd hH hr hup h hk hαT hβ₁T hb (h.β₂γ₂ hd).symm
  have hβ₂T : Both c t₁ t₂ η := by
    by_contra hn
    have := c57_b1 hG hd.swap hH.swap hr.swap hup.swap h.swap (by rw [tval_swap]; exact hk)
      (both_swap.2 hαT) (fun hb => hn (both_swap.1 hb))
    exact (h.cm.ab_facts hG).1 η this hη
  -- swap the `F`-avoiding chain `P_a(γ₂, β₂)`
  have hs₂ : (c.kempeGraph γ₂ η).Reachable t₂ s₂ :=
    (kempeGraph_adj_of_col (Or.inl h.ct₂s)).reachable
  have hu : (c.kempeGraph γ₂ η).Reachable t₂ u := reachable_of_col hs₂ (Or.inr h.cs₂u)
  have hnr : ∀ {x}, (c.kempeGraph γ₂ η).Reachable t₂ x → ¬ (c.kempeGraph γ₂ η).Reachable a x :=
    fun hx => ksAB_not_reach hG h.cm hγ₂a hη (Or.inr hβ₂T.2) hd.at₂.symm hd.bt₂.symm hx
  have hαη := h.αβ₂ hd
  have hf := h.of_swapAB hG hd hγ₂a hη hr.2.2.1.symm
    (kcol_keep c h.cbu (Or.inl ⟨hr.2.2.1.symm, hαη⟩))
    (kcol_keep c h.cus₁ (Or.inl ⟨hr.2.2.2.symm, h.β₁β₂ hd⟩))
    (kcol_keep c h.cus₂ (Or.inr (hnr hu)))
    (kcol_keep c h.cst₁ (Or.inl ⟨h.γ₁γ₂, hr.2.1⟩))
    (by rw [PEC.col_symm]; exact kcol_keep c h.ct₂s (Or.inr (hnr (Reachable.refl t₂))))
  have hfree := fun {w} (hwa : w ≠ a) (hwb : w ≠ b) ε =>
    ksAB_free_other hG h.cm hγ₂a hη hwa hwb ε
  have hboth : ∀ x, Both (c.kempeSwap γ₂ η a) t₁ t₂ x ↔ Both c t₁ t₂ x := fun x => by
    unfold Both; rw [hfree hd.at₁.symm hd.bt₁.symm, hfree hd.at₂.symm hd.bt₂.symm]
  exact c57_b3 hG hd hH hr hup hf (by rw [tval_eq_of (hboth α) (hboth β₁) (hboth η)]; exact hk)
    ((hboth α).2 hαT) (fun hb => hβ₁T ((hboth β₁).1 hb)) (ksAB_free_b hG h.cm hγ₂a hη)
    (h.β₂γ₂ hd).symm

omit hup in
/-- **Claim 5.7.** If no rainbow fork (with these colours) has `{α, β₁, β₂} ⊆ T`, then no rainbow
fork with these colours exists. -/
theorem claim57
    (hT : ∀ c : PEC G (Fin G.maxDegree), IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ →
      Both c t₁ t₂ α → Both c t₁ t₂ β₁ → Both c t₁ t₂ β₂ → False)
    (c : PEC G (Fin G.maxDegree)) (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : False := by
  suffices key : ∀ n (c : PEC G (Fin G.maxDegree)), IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ →
      3 ≤ tval c t₁ t₂ α β₁ β₂ + n → False from key 3 c h (by omega)
  intro n
  induction n with
  | zero =>
    intro c h hc
    obtain ⟨h0, h1, h2⟩ := all_of_tval (by simpa using hc)
    exact hT c h h0 h1 h2
  | succ n ih =>
    intro c h hc
    have hup : Up57 G a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ (tval c t₁ t₂ α β₁ β₂) :=
      fun c' hf hlt => ih c' hf (by omega)
    by_cases h0 : Both c t₁ t₂ α
    · by_cases h1 : Both c t₁ t₂ β₁
      · by_cases h2 : Both c t₁ t₂ β₂
        · exact hT c h h0 h1 h2
        · exact c57_case2 hG hd.swap hH.swap hr.swap hup.swap h.swap
            (by rw [tval_swap]) (both_swap.2 h0) (fun hb => h2 (both_swap.1 hb))
      · exact c57_case2 hG hd hH hr hup h le_rfl h0 h1
    · exact c57_case1 hG hd hH hr hup h le_rfl h0

end Overfull
