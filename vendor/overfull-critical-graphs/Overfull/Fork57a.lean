/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Fork56

/-!
# Fork lemma, Claim 5.7: setup and Case 1 (`α ∉ T`)

`T(φ) = {α, β₁, β₂} ∩ φ̄(t₁) ∩ φ̄(t₂)` and `tval` is its size. Cao–Chen pick `φ` with `t(φ)`
maximal; here this is an induction: `Up57 … k` says that colourings with `t > k` are impossible.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b u s₁ s₂ t₁ t₂ : V}

/-- `x` is missing at both ends. -/
def Both {k : ℕ} (c : PEC G (Fin k)) (t₁ t₂ : V) (x : Fin k) : Prop :=
  c.IsFree t₁ x ∧ c.IsFree t₂ x

open Classical in
/-- `t(φ) = |{α, β₁, β₂} ∩ φ̄(t₁) ∩ φ̄(t₂)|`. -/
noncomputable def tval {k : ℕ} (c : PEC G (Fin k)) (t₁ t₂ : V) (α β₁ β₂ : Fin k) : ℕ :=
  (if Both c t₁ t₂ α then 1 else 0) + (if Both c t₁ t₂ β₁ then 1 else 0) +
    (if Both c t₁ t₂ β₂ then 1 else 0)

section tval

variable {k : ℕ} {c c' : PEC G (Fin k)} {α β₁ β₂ : Fin k}

open Classical

theorem ind_le {p q : Prop} (h : p → q) : (if p then 1 else 0) ≤ (if q then 1 else 0) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (h hp)]
  · rw [if_neg hp]; exact Nat.zero_le _

theorem ind_eq {p q : Prop} (h : p ↔ q) : (if p then 1 else 0) = (if q then 1 else 0) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (h.1 hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.2 hq))]

theorem tval_swap : tval c t₂ t₁ α β₂ β₁ = tval c t₁ t₂ α β₁ β₂ := by
  unfold tval Both
  rw [ind_eq (and_comm (a := c.IsFree t₂ α)), ind_eq (and_comm (a := c.IsFree t₂ β₂)),
    ind_eq (and_comm (a := c.IsFree t₂ β₁))]
  omega

theorem tval_le_of (h0 : Both c t₁ t₂ α → Both c' t₁ t₂ α)
    (h1 : Both c t₁ t₂ β₁ → Both c' t₁ t₂ β₁) (h2 : Both c t₁ t₂ β₂ → Both c' t₁ t₂ β₂) :
    tval c t₁ t₂ α β₁ β₂ ≤ tval c' t₁ t₂ α β₁ β₂ := by
  unfold tval
  have := ind_le h0
  have := ind_le h1
  have := ind_le h2
  omega

theorem tval_eq_of (h0 : Both c' t₁ t₂ α ↔ Both c t₁ t₂ α)
    (h1 : Both c' t₁ t₂ β₁ ↔ Both c t₁ t₂ β₁) (h2 : Both c' t₁ t₂ β₂ ↔ Both c t₁ t₂ β₂) :
    tval c' t₁ t₂ α β₁ β₂ = tval c t₁ t₂ α β₁ β₂ := by
  unfold tval
  rw [ind_eq h0, ind_eq h1, ind_eq h2]

theorem tval_lt_α (h0 : ¬ Both c t₁ t₂ α) (h0' : Both c' t₁ t₂ α)
    (h1 : Both c t₁ t₂ β₁ → Both c' t₁ t₂ β₁) (h2 : Both c t₁ t₂ β₂ → Both c' t₁ t₂ β₂) :
    tval c t₁ t₂ α β₁ β₂ < tval c' t₁ t₂ α β₁ β₂ := by
  unfold tval
  rw [if_neg h0, if_pos h0']
  have := ind_le h1
  have := ind_le h2
  omega

theorem tval_lt_β₁ (h0 : Both c t₁ t₂ α → Both c' t₁ t₂ α) (h1 : ¬ Both c t₁ t₂ β₁)
    (h1' : Both c' t₁ t₂ β₁) (h2 : Both c t₁ t₂ β₂ → Both c' t₁ t₂ β₂) :
    tval c t₁ t₂ α β₁ β₂ < tval c' t₁ t₂ α β₁ β₂ := by
  unfold tval
  rw [if_neg h1, if_pos h1']
  have := ind_le h0
  have := ind_le h2
  omega

theorem tval_exchange (h0 : Both c t₁ t₂ α) (h0' : ¬ Both c' t₁ t₂ α) (h1 : ¬ Both c t₁ t₂ β₁)
    (h1' : Both c' t₁ t₂ β₁) (h2 : Both c' t₁ t₂ β₂ ↔ Both c t₁ t₂ β₂) :
    tval c' t₁ t₂ α β₁ β₂ = tval c t₁ t₂ α β₁ β₂ := by
  unfold tval
  rw [if_pos h0, if_neg h0', if_neg h1, if_pos h1', ind_eq h2, Nat.zero_add]

theorem all_of_tval (h : 3 ≤ tval c t₁ t₂ α β₁ β₂) :
    Both c t₁ t₂ α ∧ Both c t₁ t₂ β₁ ∧ Both c t₁ t₂ β₂ := by
  unfold tval at h
  by_cases h0 : Both c t₁ t₂ α <;> by_cases h1 : Both c t₁ t₂ β₁ <;>
    by_cases h2 : Both c t₁ t₂ β₂ <;> simp only [h0, h1, h2, if_true, if_false] at h <;>
    first | exact ⟨h0, h1, h2⟩ | omega

end tval

/-- Colourings with the same fork colours and `t > k` are impossible. -/
def Up57 (G : SimpleGraph V) [DecidableRel G.Adj] (a b u s₁ s₂ t₁ t₂ : V)
    (α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree) (k : ℕ) : Prop :=
  ∀ c' : PEC G (Fin G.maxDegree), IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ →
    k < tval c' t₁ t₂ α β₁ β₂ → False

theorem Up57.swap {α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree} {k : ℕ}
    (h : Up57 G a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ k) :
    Up57 G a b u s₂ s₁ t₂ t₁ α β₂ β₁ γ₂ γ₁ k := fun c' hf hk =>
  h c' hf.swap (by rw [tval_swap] at hk; exact hk)

/-- A delta-colour exists as soon as one of `α, β₁, β₂` is not in `T`. -/
theorem delta57 (hH : ForkHyp G a b t₁ t₂) {c : PEC G (Fin G.maxDegree)}
    {α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂)
    (hn : ¬ (Both c t₁ t₂ α ∧ Both c t₁ t₂ β₁ ∧ Both c t₁ t₂ β₂)) :
    ∃ δ, IsDelta c a b t₁ t₂ α β₁ β₂ δ := by
  by_cases h0 : Both c t₁ t₂ α
  · by_cases h1 : Both c t₁ t₂ β₁
    · obtain ⟨δ, e1, e2, hA, ht₁, ht₂⟩ := (hH c h.cm).1 α β₁
      exact ⟨δ, hA, ht₁, ht₂, e1, e2, fun e => hn ⟨h0, h1, e ▸ ⟨ht₁, ht₂⟩⟩⟩
    · obtain ⟨δ, e1, e2, hA, ht₁, ht₂⟩ := (hH c h.cm).1 α β₂
      exact ⟨δ, hA, ht₁, ht₂, e1, fun e => h1 (e ▸ ⟨ht₁, ht₂⟩), e2⟩
  · obtain ⟨δ, e1, e2, hA, ht₁, ht₂⟩ := (hH c h.cm).1 β₁ β₂
    exact ⟨δ, hA, ht₁, ht₂, fun e => h0 (e ▸ ⟨ht₁, ht₂⟩), e1, e2⟩

variable (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
  {α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree} (hr : Rainbow α β₁ β₂ γ₁ γ₂) {k : ℕ}
  (hup : Up57 G a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ k)
include hG hd hr hup

/-- Case 1 (a1): if `α ∉ T`, a delta-colour is missing at `a`. -/
theorem c57_a1 {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂)
    (hk : k ≤ tval c t₁ t₂ α β₁ β₂) (hαT : ¬ Both c t₁ t₂ α) {δ : Fin G.maxDegree}
    (hδ : IsDelta c a b t₁ t₂ α β₁ β₂ δ) : c.IsFree a δ := by
  obtain ⟨hδA, hδ₁, hδ₂, hδα, hδβ₁, hδβ₂⟩ := hδ
  by_contra hδa
  have hδb : c.IsFree b δ := hδA.resolve_left hδa
  have hl := ksAB_link hG h.cm h.αa hδb
  have hnr : ∀ {w}, (c.IsFree w α ∨ c.IsFree w δ) → w ≠ a → w ≠ b →
      ¬ (c.kempeGraph α δ).Reachable a w := fun hw hwa hwb =>
    ksAB_not_reach hG h.cm h.αa hδb hw hwa hwb (Reachable.refl _)
  have hnt₁ := hnr (Or.inr hδ₁) hd.at₁.symm hd.bt₁.symm
  have hnt₂ := hnr (Or.inr hδ₂) hd.at₂.symm hd.bt₂.symm
  have hta := fun ε => kempeSwapCompl_isFree_of_reachable c α δ (Reachable.refl a) ε
  have htb := fun ε => kempeSwapCompl_isFree_of_reachable c α δ hl ε
  have hA' : ∀ ε, InA (kempeSwapCompl c α δ a) a b ε ↔ InA c a b ε := by
    intro ε; unfold InA; rw [hta, htb]
  have hγ₁δ : γ₁ ≠ δ := fun e => h.not_free_t₁ (e ▸ hδ₁)
  have hγ₂δ : γ₂ ≠ δ := fun e => h.not_free_t₂ (e ▸ hδ₂)
  have hβ₁α := (h.αβ₁ hd).symm
  have hβ₂α := (h.αβ₂ hd).symm
  set c' := kempeSwapCompl c α δ a with hc'
  have hf : IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ :=
    ⟨h.cm.kempeSwapCompl α δ a, ccol_keep c h.cbu (Or.inr hl),
      ccol_keep c h.cus₁ (Or.inl ⟨hβ₁α, hδβ₁.symm⟩), ccol_keep c h.cus₂ (Or.inl ⟨hβ₂α, hδβ₂.symm⟩),
      ccol_keep c h.cst₁ (Or.inl ⟨hr.1, hγ₁δ⟩), ccol_keep c h.cst₂ (Or.inl ⟨hr.2.2.1, hγ₂δ⟩),
      (hta α).2 h.αa, (hA' β₁).2 h.β₁A, (hA' β₂).2 h.β₂A, (hA' γ₁).2 h.γ₁A, (hA' γ₂).2 h.γ₂A,
      (cfree_of_ne c hr.1 hγ₁δ).2 h.γ₁t₂, (cfree_of_ne c hr.2.2.1 hγ₂δ).2 h.γ₂t₁⟩
  refine hup c' hf (lt_of_le_of_lt hk (tval_lt_α hαT ⟨(cfree_flip₂ c hnt₁).2 hδ₁,
    (cfree_flip₂ c hnt₂).2 hδ₂⟩ (fun hb => ?_) (fun hb => ?_)))
  · exact ⟨(cfree_of_ne c hβ₁α hδβ₁.symm).2 hb.1, (cfree_of_ne c hβ₁α hδβ₁.symm).2 hb.2⟩
  · exact ⟨(cfree_of_ne c hβ₂α hδβ₂.symm).2 hb.1, (cfree_of_ne c hβ₂α hδβ₂.symm).2 hb.2⟩

/-- Case 1 (a2): for `η ∈ φ̄(b)`, `P_a(δ, η)` passes along `us₁` or `us₂`. -/
theorem c57_a2 {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂)
    (hk : k ≤ tval c t₁ t₂ α β₁ β₂) (hαT : ¬ Both c t₁ t₂ α) {δ : Fin G.maxDegree}
    (hδ : IsDelta c a b t₁ t₂ α β₁ β₂ δ) {η : Fin G.maxDegree} (hηb : c.IsFree b η)
    (h₁ : η ≠ β₁ ∨ ¬ (c.kempeGraph δ η).Reachable a s₁)
    (h₂ : η ≠ β₂ ∨ ¬ (c.kempeGraph δ η).Reachable a s₂) : False := by
  have hδa := c57_a1 hG hd hr hup h hk hαT hδ
  have hδ' := hδ
  obtain ⟨hδA, hδ₁, hδ₂, hδα, hδβ₁, hδβ₂⟩ := hδ
  obtain ⟨hdis, -⟩ := h.cm.ab_facts hG
  have hαη : α ≠ η := fun e => hdis α h.αa (e ▸ hηb)
  have hnr : ∀ {w}, (c.IsFree w δ ∨ c.IsFree w η) → w ≠ a → w ≠ b →
      ¬ (c.kempeGraph δ η).Reachable a w := fun hw hwa hwb =>
    ksAB_not_reach hG h.cm hδa hηb hw hwa hwb (Reachable.refl _)
  have hf := h.of_swapAB hG hd hδa hηb hδα.symm (kcol_keep c h.cbu (Or.inl ⟨hδα.symm, hαη⟩))
    (by
      rw [PEC.col_symm]
      exact kcol_keep c h.cs₁u (h₁.elim (fun hne => Or.inl ⟨hδβ₁.symm, hne.symm⟩) Or.inr))
    (by
      rw [PEC.col_symm]
      exact kcol_keep c h.cs₂u (h₂.elim (fun hne => Or.inl ⟨hδβ₂.symm, hne.symm⟩) Or.inr))
    (by rw [PEC.col_symm]; exact kcol_keep c h.ct₁s (Or.inr (hnr (Or.inl hδ₁) hd.at₁.symm
      hd.bt₁.symm)))
    (by rw [PEC.col_symm]; exact kcol_keep c h.ct₂s (Or.inr (hnr (Or.inl hδ₂) hd.at₂.symm
      hd.bt₂.symm)))
  have hfree := fun {w} (hwa : w ≠ a) (hwb : w ≠ b) ε =>
    ksAB_free_other hG h.cm hδa hηb hwa hwb ε
  have hboth : ∀ x, Both (c.kempeSwap δ η a) t₁ t₂ x ↔ Both c t₁ t₂ x := fun x => by
    unfold Both; rw [hfree hd.at₁.symm hd.bt₁.symm, hfree hd.at₂.symm hd.bt₂.symm]
  have hδa' := c57_a1 hG hd hr hup hf
    (by rw [tval_eq_of (hboth α) (hboth β₁) (hboth β₂)]; exact hk)
    (fun hb => hαT ((hboth α).1 hb))
    (IsDelta.of_swapAB hG h.cm hd.at₁ hd.at₂ hd.bt₁ hd.bt₂ hδ' hδa hηb)
  exact (hf.cm.ab_facts hG).1 δ hδa' (ksAB_free_b hG h.cm hδa hηb)

/-- Case 1 (a3), with `β₁` missing at `b`. -/
theorem c57_a3 {c : PEC G (Fin G.maxDegree)} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂)
    (hH : ForkHyp G a b t₁ t₂) (hk : k ≤ tval c t₁ t₂ α β₁ β₂) (hαT : ¬ Both c t₁ t₂ α)
    {δ : Fin G.maxDegree} (hδ : IsDelta c a b t₁ t₂ α β₁ β₂ δ) (hβ₁b : c.IsFree b β₁) : False := by
  have hδa := c57_a1 hG hd hr hup h hk hαT hδ
  have hγ₁a : c.IsFree a γ₁ := h.γ₁A.resolve_right fun hb =>
    c57_a2 hG hd hr hup h hk hαT hδ hb (Or.inl (h.β₁γ₁ hd).symm) (Or.inl hr.2.1)
  have hpass : (c.kempeGraph δ β₁).Reachable a s₁ := by
    by_contra hp
    exact c57_a2 hG hd hr hup h hk hαT hδ hβ₁b (Or.inr hp) (Or.inl (h.β₁β₂ hd))
  obtain ⟨hδA, hδ₁, hδ₂, hδα, hδβ₁, hδβ₂⟩ := hδ
  -- switch `δ, β₁` on all chains except `P_a(δ, β₁)`
  have hl := ksAB_link hG h.cm hδa hβ₁b
  have hnr : ∀ {w}, (c.IsFree w δ ∨ c.IsFree w β₁) → w ≠ a → w ≠ b →
      ¬ (c.kempeGraph δ β₁).Reachable a w := fun hw hwa hwb =>
    ksAB_not_reach hG h.cm hδa hβ₁b hw hwa hwb (Reachable.refl _)
  have hnt₁ := hnr (Or.inl hδ₁) hd.at₁.symm hd.bt₁.symm
  have hnt₂ := hnr (Or.inl hδ₂) hd.at₂.symm hd.bt₂.symm
  have hta := fun ε => kempeSwapCompl_isFree_of_reachable c δ β₁ (Reachable.refl a) ε
  have htb := fun ε => kempeSwapCompl_isFree_of_reachable c δ β₁ hl ε
  have hA' : ∀ ε, InA (kempeSwapCompl c δ β₁ a) a b ε ↔ InA c a b ε := by
    intro ε; unfold InA; rw [hta, htb]
  have hγ₁δ : γ₁ ≠ δ := fun e => h.not_free_t₁ (e ▸ hδ₁)
  have hγ₂δ : γ₂ ≠ δ := fun e => h.not_free_t₂ (e ▸ hδ₂)
  have hαδ : α ≠ δ := hδα.symm
  have hαβ₁ := h.αβ₁ hd
  have hβ₂β₁ := (h.β₁β₂ hd).symm
  set c' := kempeSwapCompl c δ β₁ a with hc'
  have hf : IsFork c' a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ :=
    ⟨h.cm.kempeSwapCompl δ β₁ a, ccol_keep c h.cbu (Or.inl ⟨hαδ, hαβ₁⟩),
      by rw [PEC.col_symm]; exact ccol_keep c h.cs₁u (Or.inr hpass),
      ccol_keep c h.cus₂ (Or.inl ⟨hδβ₂.symm, hβ₂β₁⟩),
      ccol_keep c h.cst₁ (Or.inl ⟨hγ₁δ, (h.β₁γ₁ hd).symm⟩),
      ccol_keep c h.cst₂ (Or.inl ⟨hγ₂δ, hr.2.2.2⟩), (hta α).2 h.αa, (hA' β₁).2 h.β₁A,
      (hA' β₂).2 h.β₂A, (hA' γ₁).2 h.γ₁A, (hA' γ₂).2 h.γ₂A,
      (cfree_of_ne c hγ₁δ (h.β₁γ₁ hd).symm).2 h.γ₁t₂, (cfree_of_ne c hγ₂δ hr.2.2.2).2 h.γ₂t₁⟩
  have hβ₁t₁ : c'.IsFree t₁ β₁ := (cfree_flip₁ c hnt₁).2 hδ₁
  have hboth_α : Both c' t₁ t₂ α ↔ Both c t₁ t₂ α := by
    unfold Both; rw [cfree_of_ne c hαδ hαβ₁, cfree_of_ne c hαδ hαβ₁]
  have hboth_β₂ : Both c' t₁ t₂ β₂ ↔ Both c t₁ t₂ β₂ := by
    unfold Both; rw [cfree_of_ne c hδβ₂.symm hβ₂β₁, cfree_of_ne c hδβ₂.symm hβ₂β₁]
  have hk' : k ≤ tval c' t₁ t₂ α β₁ β₂ := le_trans hk (tval_le_of hboth_α.2
    (fun _ => ⟨hβ₁t₁, (cfree_flip₁ c hnt₂).2 hδ₂⟩) hboth_β₂.2)
  have hαT' : ¬ Both c' t₁ t₂ α := fun hb => hαT (hboth_α.1 hb)
  -- swap the `F`-avoiding chain `P_a(γ₁, β₁)`
  have hγ₁a' : c'.IsFree a γ₁ := (hta γ₁).2 hγ₁a
  have hβ₁b' : c'.IsFree b β₁ := (htb β₁).2 hβ₁b
  have hs₁ : (c'.kempeGraph γ₁ β₁).Reachable t₁ s₁ :=
    (kempeGraph_adj_of_col (Or.inl hf.ct₁s)).reachable
  have hu : (c'.kempeGraph γ₁ β₁).Reachable t₁ u := reachable_of_col hs₁ (Or.inr hf.cs₁u)
  have hnr' : ∀ {x}, (c'.kempeGraph γ₁ β₁).Reachable t₁ x →
      ¬ (c'.kempeGraph γ₁ β₁).Reachable a x := fun hx =>
    ksAB_not_reach hG hf.cm hγ₁a' hβ₁b' (Or.inr hβ₁t₁) hd.at₁.symm hd.bt₁.symm hx
  have hf' := hf.of_swapAB hG hd hγ₁a' hβ₁b' hr.1.symm
    (kcol_keep c' hf.cbu (Or.inl ⟨hr.1.symm, hαβ₁⟩)) (kcol_keep c' hf.cus₁ (Or.inr (hnr' hu)))
    (kcol_keep c' hf.cus₂ (Or.inl ⟨hr.2.1.symm, hβ₂β₁⟩))
    (by rw [PEC.col_symm]; exact kcol_keep c' hf.ct₁s (Or.inr (hnr' (Reachable.refl t₁))))
    (kcol_keep c' hf.cst₂ (Or.inl ⟨h.γ₁γ₂.symm, hr.2.2.2⟩))
  have hfree := fun {w} (hwa : w ≠ a) (hwb : w ≠ b) ε =>
    ksAB_free_other hG hf.cm hγ₁a' hβ₁b' hwa hwb ε
  have hboth : ∀ x, Both (c'.kempeSwap γ₁ β₁ a) t₁ t₂ x ↔ Both c' t₁ t₂ x := fun x => by
    unfold Both; rw [hfree hd.at₁.symm hd.bt₁.symm, hfree hd.at₂.symm hd.bt₂.symm]
  have hk'' : k ≤ tval (c'.kempeSwap γ₁ β₁ a) t₁ t₂ α β₁ β₂ := by
    rw [tval_eq_of (hboth α) (hboth β₁) (hboth β₂)]; exact hk'
  have hαT'' : ¬ Both (c'.kempeSwap γ₁ β₁ a) t₁ t₂ α := fun hb => hαT' ((hboth α).1 hb)
  obtain ⟨δ'', hδ''⟩ := delta57 hH hf' (fun hall => hαT'' hall.1)
  exact c57_a2 hG hd hr hup hf' hk'' hαT'' hδ'' (ksAB_free_b hG hf.cm hγ₁a' hβ₁b')
    (Or.inl (h.β₁γ₁ hd).symm) (Or.inl hr.2.1)

end Overfull
