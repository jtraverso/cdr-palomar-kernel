/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.BroomD

/-!
# Brooms with two leaves, part E

The case where `x` misses `β` (copied from `ShortKiteE` without the vertex `c`).
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace BNF

variable {c : PEC G (Fin G.maxDegree)} {a b u x y : V} {β δ γ σ : Fin G.maxDegree}

set_option maxHeartbeats 1600000 in
/-- **Case 2, end.** In the normal form `x` cannot miss `β`. -/
theorem case2_final (hG : IsClassTwo G) (h : BNF c a b u x y β δ γ σ)
    (hxβ : c.IsFree x β) : False := by
  have d5 := h.d5
  have hσγ := h.σγ_of_xβ hG hxβ
  have hσδ := h.σδ hG
  have hδγ := h.δγ
  have hδβ := h.δβ
  have hσβ := h.σβ
  have hγβ := h.γβ
  have hγa := h.γa
  -- swap the `a`–`b` chain `(γ, β)`
  have hxu : (c.kempeGraph γ β).Reachable x u :=
    (kempeGraph_adj_of_col (Or.inl (by rw [c.col_symm]; exact h.hux))).reachable
  have hnr : ∀ {z}, (c.kempeGraph γ β).Reachable x z → ¬ (c.kempeGraph γ β).Reachable a z :=
    fun hz => ksAB_not_reach hG h.cm hγa h.βb (Or.inr hxβ) d5.ax.symm d5.bx.symm hz
  have hnu := hnr hxu
  have hnx := hnr (Reachable.refl x)
  set c₁ := c.kempeSwap γ β a with hc₁
  have hcm1 : IsColMinus c₁ a b := h.cm.kempeSwap γ β a
  have c1bu : c₁.col b u = some δ := kcol_keep c h.hbu (Or.inl ⟨hδγ, hδβ⟩)
  have c1ux : c₁.col u x = some γ := kcol_keep c h.hux (Or.inr hnu)
  have c1uy : c₁.col u y = some β := kcol_keep c h.huy (Or.inr hnu)
  have f1bγ : c₁.IsFree b γ := ksAB_free_b hG h.cm hγa h.βb
  have f1aβ : c₁.IsFree a β := ksAB_free_a hG h.cm hγa h.βb
  have f1aδ : c₁.IsFree a δ := (ksAB_free_a_of_ne hG h.cm hγa h.βb hδγ hδβ).2 h.δa
  have f1aσ : c₁.IsFree a σ := (ksAB_free_a_of_ne hG h.cm hγa h.βb hσγ hσβ).2 h.σa
  have f1xβ : c₁.IsFree x β := (kfree_off c hnx β).2 hxβ
  have f1yσ : c₁.IsFree y σ :=
    (ksAB_free_other hG h.cm hγa h.βb d5.ay.symm d5.by_.symm σ).2 h.σy
  -- move the uncoloured edge to `ux`: ab := δ, bu := γ
  set e₁ := unsetEdge c₁ u x with he₁
  have e1bu : e₁.col b u = some δ := by
    rw [he₁, unsetEdge_col_of_ne c₁ (not_pair (Or.inl d5.bu) (Or.inl d5.bx))]; exact c1bu
  set e₂ := unsetEdge e₁ b u with he₂
  have e2bδ : e₂.IsFree b δ := (isFree_unsetEdge_left e₁ d5.bu e1bu δ).2 (Or.inl rfl)
  have e2bγ : e₂.IsFree b γ := (isFree_unsetEdge_left e₁ d5.bu e1bu γ).2
    (Or.inr ((isFree_unsetEdge_of_ne c₁ d5.bu d5.bx γ).2 f1bγ))
  have e2a : ∀ ε, e₂.IsFree a ε ↔ c₁.IsFree a ε := fun ε =>
    (isFree_unsetEdge_of_ne e₁ d5.ab d5.au ε).trans (isFree_unsetEdge_of_ne c₁ d5.au d5.ax ε)
  have e1uγ : e₁.IsFree u γ := (isFree_unsetEdge_left c₁ d5.ux c1ux γ).2 (Or.inl rfl)
  have e2uγ : e₂.IsFree u γ := (isFree_unsetEdge_right e₁ d5.bu e1bu γ).2 (Or.inr e1uγ)
  have e2uδ : e₂.IsFree u δ := (isFree_unsetEdge_right e₁ d5.bu e1bu δ).2 (Or.inl rfl)
  have hab : G.Adj a b := h.cm.adj
  set e₃ := e₂.setEdge δ hab ((e2a δ).2 f1aδ) e2bδ with he₃
  have e3bγ : e₃.IsFree b γ :=
    setEdge_isFree_right e₂ hab ((e2a δ).2 f1aδ) e2bδ hδγ.symm (fun w _ => e2bγ w)
  have e3uγ : e₃.IsFree u γ :=
    (isFree_setEdge_of_ne e₂ δ hab ((e2a δ).2 f1aδ) e2bδ d5.au.symm d5.bu.symm γ).2 e2uγ
  have hbu' : G.Adj b u := c.col_adj h.hbu
  set ψ := e₃.setEdge γ hbu' e3bγ e3uγ with hψ
  -- the colour function of ψ
  have hψcol : ∀ p q, ¬ ((p = b ∧ q = u) ∨ (p = u ∧ q = b)) →
      ¬ ((p = a ∧ q = b) ∨ (p = b ∧ q = a)) → ¬ ((p = u ∧ q = x) ∨ (p = x ∧ q = u)) →
      ψ.col p q = c₁.col p q := fun p q h1 h2 h3 => by
    rw [hψ, setEdge_col_off e₃ hbu' e3bγ e3uγ h1, he₃,
      setEdge_col_off e₂ hab ((e2a δ).2 f1aδ) e2bδ h2, he₂, unsetEdge_col_of_ne e₁ h1, he₁,
      unsetEdge_col_of_ne c₁ h3]
  have hψab : ψ.col a b = some δ := by
    rw [hψ, setEdge_col_off e₃ hbu' e3bγ e3uγ (not_pair (Or.inl d5.ab) (Or.inl d5.au)), he₃,
      setEdge_col_self]
  have hψbu : ψ.col b u = some γ := by rw [hψ, setEdge_col_self]
  have hψuy : ψ.col u y = some β := by
    rw [hψcol u y (not_pair (Or.inl d5.bu.symm) (Or.inr d5.by_.symm))
      (not_pair (Or.inl d5.au.symm) (Or.inl d5.bu.symm))
      (not_pair (Or.inr d5.xy.symm) (Or.inl d5.ux))]
    exact c1uy
  have hcmψ : IsColMinus ψ u x := by
    refine ⟨c.col_adj h.hux, ?_, fun p q hpq hne => ?_⟩
    · rw [hψ, setEdge_col_off e₃ hbu' e3bγ e3uγ (not_pair (Or.inl d5.bu.symm)
          (Or.inr d5.bx.symm)), he₃,
        setEdge_col_off e₂ hab ((e2a δ).2 f1aδ) e2bδ (not_pair (Or.inl d5.au.symm)
          (Or.inl d5.bu.symm)), he₂,
        unsetEdge_col_of_ne e₁ (not_pair (Or.inl d5.bu.symm) (Or.inr d5.bx.symm)), he₁]
      exact unsetEdge_col_self c₁ u x
    · by_cases h1 : (p = b ∧ q = u) ∨ (p = u ∧ q = b)
      · rw [hψ, setEdge_col, updFun, if_pos h1]; exact Option.some_ne_none _
      by_cases h2 : (p = a ∧ q = b) ∨ (p = b ∧ q = a)
      · rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hψab]; exact Option.some_ne_none _
        · rw [ψ.col_symm, hψab]; exact Option.some_ne_none _
      have h3 : ¬ ((p = u ∧ q = x) ∨ (p = x ∧ q = u)) := fun h3 => hne (by
        rcases h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap)
      rw [hψcol p q h1 h2 h3]
      exact hcm1.total p q hpq fun he => h2 (by
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩)
  have ψuδ : ψ.IsFree u δ :=
    setEdge_isFree_right e₃ hbu' e3bγ e3uγ hδγ (fun w _ => by
      rw [he₃, setEdge_col_off e₂ hab ((e2a δ).2 f1aδ) e2bδ
        (not_pair (Or.inl d5.au.symm) (Or.inl d5.bu.symm))]
      exact e2uδ w)
  have ψother : ∀ {w}, w ≠ a → w ≠ b → w ≠ u → w ≠ x → ∀ ε, ψ.IsFree w ε ↔ c₁.IsFree w ε := by
    intro w hwa hwb hwu hwx ε
    constructor <;> intro hf q hq
    · exact hf q (by
        rw [hψcol w q (not_pair (Or.inl hwb) (Or.inl hwu)) (not_pair (Or.inl hwa) (Or.inl hwb))
          (not_pair (Or.inl hwu) (Or.inl hwx))]; exact hq)
    · rw [hψcol w q (not_pair (Or.inl hwb) (Or.inl hwu)) (not_pair (Or.inl hwa) (Or.inl hwb))
        (not_pair (Or.inl hwu) (Or.inl hwx))] at hq; exact hf q hq
  have ψyσ : ψ.IsFree y σ := (ψother d5.ay.symm d5.by_.symm d5.uy.symm d5.xy.symm σ).2 f1yσ
  have ψx : ∀ ε, ε = γ ∨ c₁.IsFree x ε → ψ.IsFree x ε := by
    intro ε hε q hq
    by_cases hqu : q = u
    · subst hqu
      rw [ψ.col_symm, hcmψ.uncol] at hq; cases hq
    rw [hψcol x q (not_pair (Or.inl d5.bx.symm) (Or.inl d5.ux.symm))
      (not_pair (Or.inl d5.ax.symm) (Or.inl d5.bx.symm))
      (not_pair (Or.inl d5.ux.symm) (Or.inr hqu))] at hq
    rcases hε with rfl | hf
    · exact hqu (c₁.col_proper hq (by rw [c₁.col_symm]; exact c1ux))
    · exact hf q hq
  have ψxγ := ψx γ (Or.inl rfl)
  have ψxβ := ψx β (Or.inr f1xβ)
  have ψa : ∀ ε, ε ≠ δ → c₁.IsFree a ε → ψ.IsFree a ε := by
    intro ε hε hf q hq
    by_cases hqb : q = b
    · subst hqb; rw [hψab] at hq; exact hε (Option.some_injective _ hq).symm
    rw [hψcol a q (not_pair (Or.inl d5.ab) (Or.inl d5.au))
      (not_pair (Or.inr hqb) (Or.inl d5.ab)) (not_pair (Or.inl d5.au) (Or.inl d5.ax))] at hq
    exact hf q hq
  have ψaβ := ψa β hδβ.symm f1aβ
  have ψaσ := ψa σ hσδ f1aσ
  -- four Kempe swaps at `a`
  -- w1: (δ, σ)
  have L1 := fan2_link hG hcmψ hψuy ψxβ d5.xy ψuδ ψyσ
  have hn1 : ¬ (ψ.kempeGraph δ σ).Reachable a u := fun r =>
    not_three_linked ψ d5.uy d5.au.symm d5.ay.symm (Or.inl ψuδ) (Or.inr ψyσ) (Or.inr ψaσ) L1
      r.symm
  have hn1y : ¬ (ψ.kempeGraph δ σ).Reachable a y := fun r => hn1 (r.trans L1.symm)
  set ψ₁ := ψ.kempeSwap δ σ a with hψ₁
  have hcm₁ : IsColMinus ψ₁ u x := hcmψ.kempeSwap δ σ a
  have p1ab : ψ₁.col a b = some σ := kcol_flip₁ ψ hψab (Reachable.refl a)
  have p1bu : ψ₁.col b u = some γ := kcol_keep ψ hψbu (Or.inl ⟨hδγ.symm, hσγ.symm⟩)
  have p1uy : ψ₁.col u y = some β := kcol_keep ψ hψuy (Or.inr hn1)
  have p1uδ : ψ₁.IsFree u δ := (kfree_off ψ hn1 δ).2 ψuδ
  have p1xγ : ψ₁.IsFree x γ := (kfree_of_ne ψ hδγ.symm hσγ.symm).2 ψxγ
  have p1xβ : ψ₁.IsFree x β := (kfree_of_ne ψ hδβ.symm hσβ.symm).2 ψxβ
  have p1yσ : ψ₁.IsFree y σ := (kfree_off ψ hn1y σ).2 ψyσ
  have p1aδ : ψ₁.IsFree a δ := (kfree_flip₂ ψ (Reachable.refl a)).2 ψaσ
  have p1aβ : ψ₁.IsFree a β := (kfree_of_ne ψ hδβ.symm hσβ.symm).2 ψaβ
  -- w2: (δ, γ)
  have L2 : (ψ₁.kempeGraph δ γ).Reachable u x := (hcm₁.ab_facts hG).2 δ γ p1uδ p1xγ
  have hn2 : ¬ (ψ₁.kempeGraph δ γ).Reachable a u := fun r =>
    not_three_linked ψ₁ d5.ux d5.au.symm d5.ax.symm (Or.inl p1uδ) (Or.inr p1xγ) (Or.inl p1aδ) L2
      r.symm
  have hn2x : ¬ (ψ₁.kempeGraph δ γ).Reachable a x := fun r => hn2 (r.trans L2.symm)
  set ψ₂ := ψ₁.kempeSwap δ γ a with hψ₂
  have hcm₂ : IsColMinus ψ₂ u x := hcm₁.kempeSwap δ γ a
  have p2ab : ψ₂.col a b = some σ := kcol_keep ψ₁ p1ab (Or.inl ⟨hσδ, hσγ⟩)
  have p2bu : ψ₂.col b u = some γ := by
    rw [ψ₂.col_symm]; exact kcol_keep ψ₁ (by rw [ψ₁.col_symm]; exact p1bu) (Or.inr hn2)
  have p2uy : ψ₂.col u y = some β := kcol_keep ψ₁ p1uy (Or.inr hn2)
  have p2uδ : ψ₂.IsFree u δ := (kfree_off ψ₁ hn2 δ).2 p1uδ
  have p2xγ : ψ₂.IsFree x γ := (kfree_off ψ₁ hn2x γ).2 p1xγ
  have p2xβ : ψ₂.IsFree x β := (kfree_of_ne ψ₁ hδβ.symm hγβ.symm).2 p1xβ
  have p2yσ : ψ₂.IsFree y σ := (kfree_of_ne ψ₁ hσδ hσγ).2 p1yσ
  have p2aγ : ψ₂.IsFree a γ := (kfree_flip₁ ψ₁ (Reachable.refl a)).2 p1aδ
  have p2aβ : ψ₂.IsFree a β := (kfree_of_ne ψ₁ hδβ.symm hγβ.symm).2 p1aβ
  -- w3: (β, δ)
  have L3 : (ψ₂.kempeGraph β δ).Reachable u x := by
    rw [kempeGraph_comm]; exact (hcm₂.ab_facts hG).2 δ β p2uδ p2xβ
  have hn3 : ¬ (ψ₂.kempeGraph β δ).Reachable a u := fun r =>
    not_three_linked ψ₂ d5.ux d5.au.symm d5.ax.symm (Or.inr p2uδ) (Or.inl p2xβ) (Or.inl p2aβ) L3
      r.symm
  have hn3x : ¬ (ψ₂.kempeGraph β δ).Reachable a x := fun r => hn3 (r.trans L3.symm)
  set ψ₃ := ψ₂.kempeSwap β δ a with hψ₃
  have hcm₃ : IsColMinus ψ₃ u x := hcm₂.kempeSwap β δ a
  have p3ab : ψ₃.col a b = some σ := kcol_keep ψ₂ p2ab (Or.inl ⟨hσβ, hσδ⟩)
  have p3bu : ψ₃.col b u = some γ := kcol_keep ψ₂ p2bu (Or.inl ⟨hγβ, hδγ.symm⟩)
  have p3uy : ψ₃.col u y = some β := kcol_keep ψ₂ p2uy (Or.inr hn3)
  have p3uδ : ψ₃.IsFree u δ := (kfree_off ψ₂ hn3 δ).2 p2uδ
  have p3xγ : ψ₃.IsFree x γ := (kfree_of_ne ψ₂ hγβ hδγ.symm).2 p2xγ
  have p3xβ : ψ₃.IsFree x β := (kfree_off ψ₂ hn3x β).2 p2xβ
  have p3yσ : ψ₃.IsFree y σ := (kfree_of_ne ψ₂ hσβ hσδ).2 p2yσ
  have p3aδ : ψ₃.IsFree a δ := (kfree_flip₁ ψ₂ (Reachable.refl a)).2 p2aβ
  have p3aγ : ψ₃.IsFree a γ := (kfree_of_ne ψ₂ hγβ hδγ.symm).2 p2aγ
  -- w4: (δ, σ)
  have L4 := fan2_link hG hcm₃ p3uy p3xβ d5.xy p3uδ p3yσ
  have hn4 : ¬ (ψ₃.kempeGraph δ σ).Reachable a u := fun r =>
    not_three_linked ψ₃ d5.uy d5.au.symm d5.ay.symm (Or.inl p3uδ) (Or.inr p3yσ) (Or.inl p3aδ) L4
      r.symm
  set ψ₄ := ψ₃.kempeSwap δ σ a with hψ₄
  have hcm₄ : IsColMinus ψ₄ u x := hcm₃.kempeSwap δ σ a
  have p4ab : ψ₄.col a b = some δ := kcol_flip₂ ψ₃ p3ab (Reachable.refl a)
  have p4bu : ψ₄.col b u = some γ := kcol_keep ψ₃ p3bu (Or.inl ⟨hδγ.symm, hσγ.symm⟩)
  have p4uδ : ψ₄.IsFree u δ := (kfree_off ψ₃ hn4 δ).2 p3uδ
  have p4xγ : ψ₄.IsFree x γ := (kfree_of_ne ψ₃ hδγ.symm hσγ.symm).2 p3xγ
  have p4aγ : ψ₄.IsFree a γ := (kfree_of_ne ψ₃ hδγ.symm hσγ.symm).2 p3aγ
  -- the chain `u b a` and the linkage of `u` and `x`
  have r : (ψ₄.kempeGraph δ γ).Reachable u a :=
    reachable_of_col (kempeGraph_adj_of_col (Or.inr (by rw [ψ₄.col_symm]; exact p4bu))).reachable
      (Or.inl (by rw [ψ₄.col_symm]; exact p4ab))
  have L5 : (ψ₄.kempeGraph δ γ).Reachable u x := (hcm₄.ab_facts hG).2 δ γ p4uδ p4xγ
  exact not_three_linked ψ₄ d5.ux d5.au.symm d5.ax.symm (Or.inl p4uδ) (Or.inr p4xγ)
    (Or.inr p4aγ) L5 r

end BNF

end Overfull
