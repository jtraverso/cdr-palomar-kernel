/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.ForkFinal

/-!
# Fork lemma: the final contradiction

Cao–Chen (2020), Claim 5.10 and the two final cases.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b u s₁ s₂ t₁ t₂ : V}

set_option maxHeartbeats 4000000 in
/-- **The final configuration is impossible.** -/
theorem FinalCfg.contra (hG : IsClassTwo G) (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    {c : PEC G (Fin G.maxDegree)} {α β₁ β₂ γ₂ : Fin G.maxDegree}
    (h : FinalCfg c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₂) (hγ₂α : γ₂ ≠ α) (hγ₂β₁ : γ₂ ≠ β₁) : False := by
  have hub : c.col u b = some α := by rw [c.col_symm]; exact h.cbu
  have hαβ₁ : α ≠ β₁ := by rintro rfl; exact hd.bs₁ (c.col_proper hub h.cus₁)
  have hαβ₂ : α ≠ β₂ := by rintro rfl; exact hd.bs₂ (c.col_proper hub h.cus₂)
  have hβ₁β₂ : β₁ ≠ β₂ := by rintro rfl; exact hd.s₁s₂ (c.col_proper h.cus₁ h.cus₂)
  have hβ₂γ₂ : β₂ ≠ γ₂ := by
    rintro rfl
    have : c.col s₂ u = some β₂ := by rw [c.col_symm]; exact h.cus₂
    exact hd.ut₂ (c.col_proper this h.cst₂)
  obtain ⟨ψ, hcm, hab, hbu, hus₂, hst₁, hst₂, hu, hs₁, ht₁, ht₂, hab'⟩ := h.exists_psi hd hαβ₁
  have ψt₁α := (ht₁ α).2 h.t₁α
  have ψt₁β₁ := (ht₁ β₁).2 h.t₁β₁
  have ψt₁γ₂ := (ht₁ γ₂).2 h.t₁γ₂
  have ψt₂α := (ht₂ α).2 h.t₂α
  have ψt₂β₁ := (ht₂ β₁).2 h.t₂β₁
  have ψt₂β₂ := (ht₂ β₂).2 h.t₂β₂
  have hβ₂ab : ψ.IsFree a β₂ ∨ ψ.IsFree b β₂ := by
    obtain ⟨h1, h2⟩ := hab' β₂ hαβ₂.symm hβ₁β₂.symm
    exact h.β₂A.elim (fun x => Or.inl (h1.2 x)) (fun x => Or.inr (h2.2 x))
  have hγ₂ab : ψ.IsFree a γ₂ ∨ ψ.IsFree b γ₂ := by
    obtain ⟨h1, h2⟩ := hab' γ₂ hγ₂α hγ₂β₁
    exact h.γ₂A.elim (fun x => Or.inl (h1.2 x)) (fun x => Or.inr (h2.2 x))
  -- Claim 5.10: `u` reaches `t₁` by an `(α, β₂)`-chain
  have hr10 : (ψ.kempeGraph α β₂).Reachable u t₁ :=
    reach_t₁ hG hcm hd.ut₁ hst₁ hβ₁β₂ hαβ₁.symm hu hs₁ ψt₁β₁
  have hlab : (ψ.kempeGraph α β₂).Reachable a b :=
    (kempeGraph_adj_of_col (Or.inl hab)).reachable
  have hnau : ¬ (ψ.kempeGraph α β₂).Reachable a u := by
    intro r
    rcases hβ₂ab with ha | hb
    · exact not_three_linked ψ hd.ut₁ hd.au.symm hd.at₁.symm (Or.inl hu) (Or.inl ψt₁α)
        (Or.inr ha) hr10 r.symm
    · exact not_three_linked ψ hd.ut₁ hd.bu.symm hd.bt₁.symm (Or.inl hu) (Or.inl ψt₁α)
        (Or.inr hb) hr10 (r.symm.trans hlab)
  -- `β₂` is missing at `a` (otherwise `G` gets coloured)
  have ha2 : ψ.IsFree a β₂ := by
    by_contra hna
    have hb := hβ₂ab.resolve_left hna
    exact close_bu hG (hcm.kempeSwap α β₂ a) hd.bs₁ (kcol_keep ψ hbu (Or.inl ⟨hαβ₁.symm, hβ₁β₂⟩))
      ((kfree_of_ne ψ hαβ₁.symm hβ₁β₂).2 hs₁) ((kfree_flip₂ ψ hlab).2 hb)
      ((kfree_off ψ hnau α).2 hu)
  -- `ψ₁`: swap the `(α, β₂)`-chain through `ab`
  have hnat₁ : ¬ (ψ.kempeGraph α β₂).Reachable a t₁ := fun r => hnau (r.trans hr10.symm)
  have hnas₁ : ¬ (ψ.kempeGraph α β₂).Reachable a s₁ := fun r =>
    hnat₁ (reachable_of_col r (Or.inr hst₁))
  have hnat₂ : ¬ (ψ.kempeGraph α β₂).Reachable a t₂ := fun r =>
    hd.at₂ (eq_of_reachable_of_free_both ψ ψt₂α ψt₂β₂ r.symm)
  set ψ1 := ψ.kempeSwap α β₂ a with hψ1
  have hcm1 : IsColMinus ψ1 u s₁ := hcm.kempeSwap α β₂ a
  have ψ1ab : ψ1.col a b = some β₂ := kcol_flip₁ ψ hab (Reachable.refl a)
  have ψ1bu : ψ1.col b u = some β₁ := kcol_keep ψ hbu (Or.inl ⟨hαβ₁.symm, hβ₁β₂⟩)
  have ψ1us₂ : ψ1.col u s₂ = some β₂ := kcol_keep ψ hus₂ (Or.inr hnau)
  have ψ1st₁ : ψ1.col s₁ t₁ = some β₂ := kcol_keep ψ hst₁ (Or.inr hnas₁)
  have ψ1st₂ : ψ1.col s₂ t₂ = some γ₂ := kcol_keep ψ hst₂ (Or.inl ⟨hγ₂α, hβ₂γ₂.symm⟩)
  have ψ1u : ψ1.IsFree u α := (kfree_off ψ hnau α).2 hu
  have ψ1s₁ : ψ1.IsFree s₁ β₁ := (kfree_of_ne ψ hαβ₁.symm hβ₁β₂).2 hs₁
  have ψ1t₁ := kfree_off ψ hnat₁
  have ψ1t₂ := kfree_off ψ hnat₂
  have ψ1aα : ψ1.IsFree a α := (kfree_flip₂ ψ (Reachable.refl a)).2 ha2
  have ψ1γ₂ : ψ1.IsFree a γ₂ ∨ ψ1.IsFree b γ₂ :=
    hγ₂ab.elim (fun x => Or.inl ((kfree_of_ne ψ hγ₂α hβ₂γ₂.symm).2 x))
      (fun x => Or.inr ((kfree_of_ne ψ hγ₂α hβ₂γ₂.symm).2 x))
  -- `ψ₂`: swap the `(α, β₁)`-chain of `a`
  have hl2 := (hcm1.ab_facts hG).2 α β₁ ψ1u ψ1s₁
  have hub2 : (ψ1.kempeGraph α β₁).Reachable u b :=
    (kempeGraph_adj_of_col (Or.inr (by rw [ψ1.col_symm]; exact ψ1bu))).reachable
  have hnau2 : ¬ (ψ1.kempeGraph α β₁).Reachable a u := fun r =>
    not_three_linked ψ1 hd.au hd.as₁ hd.us₁ (Or.inl ψ1aα) (Or.inl ψ1u) (Or.inr ψ1s₁) r
      (r.trans hl2)
  have hnab2 : ¬ (ψ1.kempeGraph α β₁).Reachable a b := fun r => hnau2 (r.trans hub2.symm)
  have hnas₁2 : ¬ (ψ1.kempeGraph α β₁).Reachable a s₁ := fun r => hnau2 (r.trans hl2.symm)
  have ψ1t₁α : ψ1.IsFree t₁ α := (ψ1t₁ α).2 ψt₁α
  have ψ1t₁β₁ : ψ1.IsFree t₁ β₁ := (ψ1t₁ β₁).2 ψt₁β₁
  have ψ1t₂α : ψ1.IsFree t₂ α := (ψ1t₂ α).2 ψt₂α
  have ψ1t₂β₁ : ψ1.IsFree t₂ β₁ := (ψ1t₂ β₁).2 ψt₂β₁
  have hnat₁2 : ¬ (ψ1.kempeGraph α β₁).Reachable a t₁ := fun r =>
    hd.at₁ (eq_of_reachable_of_free_both ψ1 ψ1t₁α ψ1t₁β₁ r.symm)
  have hnat₂2 : ¬ (ψ1.kempeGraph α β₁).Reachable a t₂ := fun r =>
    hd.at₂ (eq_of_reachable_of_free_both ψ1 ψ1t₂α ψ1t₂β₁ r.symm)
  set ψ2 := ψ1.kempeSwap α β₁ a with hψ2
  have hcm2 : IsColMinus ψ2 u s₁ := hcm1.kempeSwap α β₁ a
  have ψ2aβ₁ : ψ2.IsFree a β₁ := (kfree_flip₁ ψ1 (Reachable.refl a)).2 ψ1aα
  have ψ2ab : ψ2.col a b = some β₂ := kcol_keep ψ1 ψ1ab (Or.inl ⟨hαβ₂.symm, hβ₁β₂.symm⟩)
  have ψ2bu : ψ2.col b u = some β₁ := kcol_keep ψ1 ψ1bu (Or.inr hnab2)
  have ψ2us₂ : ψ2.col u s₂ = some β₂ := kcol_keep ψ1 ψ1us₂ (Or.inl ⟨hαβ₂.symm, hβ₁β₂.symm⟩)
  have ψ2st₁ : ψ2.col s₁ t₁ = some β₂ := kcol_keep ψ1 ψ1st₁ (Or.inl ⟨hαβ₂.symm, hβ₁β₂.symm⟩)
  have ψ2st₂ : ψ2.col s₂ t₂ = some γ₂ := kcol_keep ψ1 ψ1st₂ (Or.inl ⟨hγ₂α, hγ₂β₁⟩)
  have ψ2u : ψ2.IsFree u α := (kfree_off ψ1 hnau2 α).2 ψ1u
  have ψ2s₁ : ψ2.IsFree s₁ β₁ := (kfree_off ψ1 hnas₁2 β₁).2 ψ1s₁
  have ψ2t₁ := kfree_off ψ1 hnat₁2
  have ψ2t₂ := kfree_off ψ1 hnat₂2
  have ψ2t₁α : ψ2.IsFree t₁ α := (ψ2t₁ α).2 ψ1t₁α
  have ψ2t₁β₁ : ψ2.IsFree t₁ β₁ := (ψ2t₁ β₁).2 ψ1t₁β₁
  have ψ2t₁γ₂ : ψ2.IsFree t₁ γ₂ := (ψ2t₁ γ₂).2 ((ψ1t₁ γ₂).2 ψt₁γ₂)
  have ψ2t₂α : ψ2.IsFree t₂ α := (ψ2t₂ α).2 ψ1t₂α
  have ψ2t₂β₂ : ψ2.IsFree t₂ β₂ := (ψ2t₂ β₂).2 ((ψ1t₂ β₂).2 ψt₂β₂)
  have ψ2γ₂ : ψ2.IsFree a γ₂ ∨ ψ2.IsFree b γ₂ :=
    ψ1γ₂.elim (fun x => Or.inl ((kfree_of_ne ψ1 hγ₂α hγ₂β₁).2 x))
      (fun x => Or.inr ((kfree_of_ne ψ1 hγ₂α hγ₂β₁).2 x))
  by_cases hQ : ∃ z, (z = a ∨ z = b) ∧ (ψ2.kempeGraph α γ₂).Reachable u z ∧
      (ψ2.IsFree z α ∨ ψ2.IsFree z γ₂)
  · -- Case 2: the `(α, γ₂)`-chain of `u` ends at `a` or `b`
    obtain ⟨z, hz, hrz, hzf⟩ := hQ
    have hzu : z ≠ u := by rcases hz with rfl | rfl; exacts [hd.au, hd.bu]
    have hzt₂ : z ≠ t₂ := by rcases hz with rfl | rfl; exacts [hd.at₂, hd.bt₂]
    have hnut₂ : ¬ (ψ2.kempeGraph α γ₂).Reachable u t₂ := fun r =>
      not_three_linked ψ2 hzu.symm hd.ut₂ hzt₂ (Or.inl ψ2u) hzf (Or.inl ψ2t₂α) hrz r
    have ht₂s₂ : ψ2.col t₂ s₂ = some γ₂ := by rw [ψ2.col_symm]; exact ψ2st₂
    have hnt₁3 : ¬ (ψ2.kempeGraph α γ₂).Reachable t₂ t₁ := fun r =>
      hd.t₁t₂.symm (eq_of_reachable_of_free_both ψ2 ψ2t₁α ψ2t₁γ₂ r.symm)
    set ψ3 := ψ2.kempeSwap α γ₂ t₂ with hψ3
    have hcm3 : IsColMinus ψ3 u s₁ := hcm2.kempeSwap α γ₂ t₂
    have ψ3ts : ψ3.col t₂ s₂ = some α := kcol_flip₂ ψ2 ht₂s₂ (Reachable.refl t₂)
    have ψ3su : ψ3.col s₂ u = some β₂ := by
      rw [ψ3.col_symm]; exact kcol_keep ψ2 ψ2us₂ (Or.inl ⟨hαβ₂.symm, hβ₂γ₂⟩)
    have ψ3t₁s₁ : ψ3.col t₁ s₁ = some β₂ := by
      rw [ψ3.col_symm]; exact kcol_keep ψ2 ψ2st₁ (Or.inl ⟨hαβ₂.symm, hβ₂γ₂⟩)
    have ψ3u : ψ3.IsFree u α := (kfree_off ψ2 (fun r => hnut₂ r.symm) α).2 ψ2u
    have ψ3t₂β₂ : ψ3.IsFree t₂ β₂ := (kfree_of_ne ψ2 hαβ₂.symm hβ₂γ₂).2 ψ2t₂β₂
    have ψ3s₁ : ψ3.IsFree s₁ β₁ := (kfree_of_ne ψ2 hαβ₁.symm hγ₂β₁.symm).2 ψ2s₁
    have ψ3t₁β₁ : ψ3.IsFree t₁ β₁ := (kfree_of_ne ψ2 hαβ₁.symm hγ₂β₁.symm).2 ψ2t₁β₁
    have ψ3t₁α : ψ3.IsFree t₁ α := (kfree_off ψ2 hnt₁3 α).2 ψ2t₁α
    -- swap the path `t₂ s₂ u`
    have hts₂ : (ψ3.kempeGraph α β₂).Reachable t₂ s₂ :=
      (kempeGraph_adj_of_col (Or.inl ψ3ts)).reachable
    have htu : (ψ3.kempeGraph α β₂).Reachable t₂ u := reachable_of_col hts₂ (Or.inr ψ3su)
    have hnt₁ : ¬ (ψ3.kempeGraph α β₂).Reachable t₂ t₁ := fun r =>
      not_three_linked ψ3 hd.ut₂.symm hd.t₁t₂.symm hd.ut₁ (Or.inr ψ3t₂β₂) (Or.inl ψ3u)
        (Or.inl ψ3t₁α) htu r
    set ψ4 := ψ3.kempeSwap α β₂ t₂ with hψ4
    have hcm4 : IsColMinus ψ4 u s₁ := hcm3.kempeSwap α β₂ t₂
    have ψ4u : ψ4.IsFree u β₂ := (kfree_flip₁ ψ3 htu).2 ψ3u
    have ψ4st₁ : ψ4.col s₁ t₁ = some β₂ := by
      rw [ψ4.col_symm]; exact kcol_keep ψ3 ψ3t₁s₁ (Or.inr hnt₁)
    have ψ4s₁ : ψ4.IsFree s₁ β₁ := (kfree_of_ne ψ3 hαβ₁.symm hβ₁β₂).2 ψ3s₁
    have ψ4t₁ : ψ4.IsFree t₁ β₁ := (kfree_of_ne ψ3 hαβ₁.symm hβ₁β₂).2 ψ3t₁β₁
    -- recolour `s₁t₁` by `β₁` and colour `us₁` by `β₂`
    have hadj : G.Adj s₁ t₁ := ψ4.col_adj ψ4st₁
    set ψ5 := ψ4.setEdge β₁ hadj ψ4s₁ ψ4t₁
    have hcm5 : IsColMinus ψ5 u s₁ :=
      ⟨hcm4.adj, by
        rw [setEdge_col, updFun_of_ne _ (by have := hd.us₁; have := hd.ut₁; tauto)]
        exact hcm4.uncol,
        fun p q hpq hne => extends_setEdge ψ4 β₁ hadj ψ4s₁ ψ4t₁ p q (hcm4.total p q hpq hne)⟩
    exact close_uncol hG hcm5 ((isFree_setEdge_of_ne ψ4 β₁ hadj ψ4s₁ ψ4t₁ hd.us₁ hd.ut₁ β₂).2 ψ4u)
      (isFree_setEdge_old ψ4 β₁ hadj ψ4s₁ ψ4t₁ ψ4st₁)
  · -- Case 1: swap the `(α, γ₂)`-chain of `u`
    have hkeep : ∀ z, (z = a ∨ z = b) → ∀ ε,
        (ψ2.kempeSwap α γ₂ u).IsFree z ε ↔ ψ2.IsFree z ε := by
      intro z hz ε
      by_cases hr : (ψ2.kempeGraph α γ₂).Reachable u z
      · refine isFree_kempeSwap_of_neither ψ2 α γ₂ u (fun hf => hQ ⟨z, hz, hr, Or.inl hf⟩)
          (fun hf => hQ ⟨z, hz, hr, Or.inr hf⟩) ε
      · exact kfree_off ψ2 hr ε
    have hnut₁ : ¬ (ψ2.kempeGraph α γ₂).Reachable u t₁ := fun r =>
      hd.ut₁ (eq_of_reachable_of_free_both ψ2 ψ2t₁α ψ2t₁γ₂ r.symm)
    set ψ3 := ψ2.kempeSwap α γ₂ u with hψ3
    have hcm3 : IsColMinus ψ3 u s₁ := hcm2.kempeSwap α γ₂ u
    have ψ3u : ψ3.IsFree u γ₂ := (kfree_flip₁ ψ2 (Reachable.refl u)).2 ψ2u
    have ψ3t₁ := kfree_off ψ2 hnut₁
    have ψ3s₁ : ψ3.IsFree s₁ β₁ := (kfree_of_ne ψ2 hαβ₁.symm hγ₂β₁.symm).2 ψ2s₁
    have ψ3bu : ψ3.col b u = some β₁ := kcol_keep ψ2 ψ2bu (Or.inl ⟨hαβ₁.symm, hγ₂β₁.symm⟩)
    have ψ3ab : ψ3.col a b = some β₂ := kcol_keep ψ2 ψ2ab (Or.inl ⟨hαβ₂.symm, hβ₂γ₂⟩)
    have ψ3st₁ : ψ3.col s₁ t₁ = some β₂ := kcol_keep ψ2 ψ2st₁ (Or.inl ⟨hαβ₂.symm, hβ₂γ₂⟩)
    have ψ3aγ₂ : ψ3.IsFree a γ₂ := by
      by_contra hna
      have hb : ψ3.IsFree b γ₂ := by
        rcases ψ2γ₂ with x | x
        · exact absurd ((hkeep a (Or.inl rfl) γ₂).2 x) hna
        · exact (hkeep b (Or.inr rfl) γ₂).2 x
      exact close_bu hG hcm3 hd.bs₁ ψ3bu ψ3s₁ hb ψ3u
    have ψ3aβ₁ : ψ3.IsFree a β₁ := (hkeep a (Or.inl rfl) β₁).2 ψ2aβ₁
    have ψ3t₁β₁ : ψ3.IsFree t₁ β₁ := (ψ3t₁ β₁).2 ψ2t₁β₁
    have ψ3t₁γ₂ : ψ3.IsFree t₁ γ₂ := (ψ3t₁ γ₂).2 ψ2t₁γ₂
    -- as in Claim 5.10: `u` reaches `t₁` by a `(γ₂, β₂)`-chain
    have hr2 : (ψ3.kempeGraph γ₂ β₂).Reachable u t₁ :=
      reach_t₁ hG hcm3 hd.ut₁ ψ3st₁ hβ₁β₂ hγ₂β₁.symm ψ3u ψ3s₁ ψ3t₁β₁
    have hnau4 : ¬ (ψ3.kempeGraph γ₂ β₂).Reachable a u := fun r =>
      not_three_linked ψ3 hd.ut₁ hd.au.symm hd.at₁.symm (Or.inl ψ3u) (Or.inl ψ3t₁γ₂)
        (Or.inl ψ3aγ₂) hr2 r.symm
    set ψ4 := ψ3.kempeSwap γ₂ β₂ a with hψ4
    have hcm4 : IsColMinus ψ4 u s₁ := hcm3.kempeSwap γ₂ β₂ a
    have ψ4ab : ψ4.col a b = some γ₂ := kcol_flip₂ ψ3 ψ3ab (Reachable.refl a)
    have ψ4aβ₁ : ψ4.IsFree a β₁ := (kfree_of_ne ψ3 hγ₂β₁.symm hβ₁β₂).2 ψ3aβ₁
    have ψ4u : ψ4.IsFree u γ₂ := (kfree_off ψ3 hnau4 γ₂).2 ψ3u
    have ψ4bu : ψ4.col b u = some β₁ := kcol_keep ψ3 ψ3bu (Or.inl ⟨hγ₂β₁.symm, hβ₁β₂⟩)
    have ψ4s₁ : ψ4.IsFree s₁ β₁ := (kfree_of_ne ψ3 hγ₂β₁.symm hβ₁β₂).2 ψ3s₁
    -- switch `γ₂, β₁` on the path `a b u`, then colour `us₁` by `β₁`
    have hau5 : (ψ4.kempeGraph γ₂ β₁).Reachable a u :=
      reachable_of_col (kempeGraph_adj_of_col (Or.inl ψ4ab)).reachable (Or.inr ψ4bu)
    have ψ5u : (ψ4.kempeSwap γ₂ β₁ a).IsFree u β₁ := (kfree_flip₁ ψ4 hau5).2 ψ4u
    have hnas₁ : ¬ (ψ4.kempeGraph γ₂ β₁).Reachable a s₁ := fun r =>
      not_three_linked ψ4 hd.au hd.as₁ hd.us₁ (Or.inr ψ4aβ₁) (Or.inl ψ4u) (Or.inr ψ4s₁) hau5 r
    exact close_uncol hG (hcm4.kempeSwap γ₂ β₁ a) ψ5u ((kfree_off ψ4 hnas₁ β₁).2 ψ4s₁)

end Overfull
