/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.BroomA

/-!
# Brooms with two leaves, part B

The core of the case where `x` and `y` miss the same colour `σ` (copied from
`ShortKiteB` without the vertex `c`).
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace BNF

variable {c : PEC G (Fin G.maxDegree)} {a b u x y : V} {β δ γ σ : Fin G.maxDegree}

/-- `σ ≠ δ`: otherwise the `(δ, β)`-chain `b u y` would end at `y`. -/
theorem σδ (hG : IsClassTwo G) (h : BNF c a b u x y β δ γ σ) : σ ≠ δ := by
  rintro rfl
  have hl := ksAB_link hG h.cm h.δa h.βb
  have r1 := reachable_of_col hl (Or.inl h.hbu)
  have r2 := reachable_of_col r1 (Or.inr h.huy)
  exact not_three_linked c h.d5.ab h.d5.ay h.d5.by_ (Or.inl h.δa) (Or.inr h.βb) (Or.inl h.σy) hl r2

theorem δγ (h : BNF c a b u x y β δ γ σ) : δ ≠ γ := by
  rintro rfl
  have : c.col u b = some δ := by rw [c.col_symm]; exact h.hbu
  exact h.d5.bx (c.col_proper this h.hux)

theorem δβ (h : BNF c a b u x y β δ γ σ) : δ ≠ β := by
  rintro rfl
  exact h.βb u h.hbu

theorem σβ (h : BNF c a b u x y β δ γ σ) : σ ≠ β := by
  rintro rfl
  exact h.σy u (by rw [c.col_symm]; exact h.huy)

/-- **Case 1 core.** -/
theorem case1_core (hG : IsClassTwo G) (h : BNF c a b u x y β δ γ σ)
    (hxσ : c.IsFree x σ)
    (hR : ¬ ((unsetEdge c u x).kempeGraph β γ).Reachable u b) : False := by
  have d5 := h.d5
  have hσγ : σ ≠ γ := fun e => hxσ u (by rw [c.col_symm, e]; exact h.hux)
  have hσδ := h.σδ hG
  have hδγ := h.δγ
  have hδβ := h.δβ
  have hσβ := h.σβ
  have hγβ := h.γβ
  have hγa := h.γa
  -- the shift along `bu` and the linkage of `u` and `y`
  obtain ⟨ψ, hcmψ, hψab, hoff, hψb, hψu, hψw⟩ := exists_shift h.cm h.hbu h.δa d5.au
  have hψuy : ψ.col u y = some β := by
    rw [hoff u y (by have := d5.au; have := d5.bu; tauto) (by have := d5.bu; have := d5.by_; tauto)]
    exact h.huy
  have hF : IsMultifan ψ u 2 (fun i => if i = 0 then b else y) := by
    refine ⟨by omega, by simp only [if_true]; exact hcmψ.uncol, fun i hi => ?_,
      fun i hi j hj hij => ?_, fun i hi0 hi => ?_⟩
    · split_ifs
      · exact (c.col_adj h.hbu).symm
      · exact c.col_adj h.huy
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rfl
      · exact absurd hij (by simpa using d5.by_)
      · exact absurd hij (by simpa using d5.by_.symm)
      · rfl
    · refine ⟨0, hi0, β, ?_, by simpa using (hψb β).2 h.βb⟩
      simp only [show i ≠ 0 by omega, if_false]
      exact hψuy
  obtain ⟨-, -, hB⟩ := multifan_elementary hG 2 ψ u _ hcmψ hF
  have hψy : ψ.IsFree y σ := (hψw y d5.ay.symm d5.by_.symm d5.uy.symm σ).2 h.σy
  have hlinkψ : (ψ.kempeGraph δ σ).Reachable u y := by
    simpa using hB 1 (by omega) δ σ hψu (by simpa using hψy)
  -- the colourings φ₁ (ux uncoloured) and φ₂ (also bu uncoloured)
  set φ₁ := unsetEdge c u x with hφ₁
  have hφ₁bu : φ₁.col b u = some δ := by
    rw [hφ₁, unsetEdge_col_of_ne c (by have := d5.bu; have := d5.bx; tauto)]; exact h.hbu
  set φ₂ := unsetEdge φ₁ b u with hφ₂
  have hcol₂ : ∀ p q, ¬ ((p = u ∧ q = x) ∨ (p = x ∧ q = u)) → ¬ ((p = b ∧ q = u) ∨ (p = u ∧ q = b)) →
      φ₂.col p q = c.col p q := fun p q h1 h2 => by
    rw [hφ₂, unsetEdge_col_of_ne _ h2, hφ₁, unsetEdge_col_of_ne _ h1]
  have f₁ : ∀ {w} (hwu : w ≠ u) (hwx : w ≠ x) ε, φ₁.IsFree w ε ↔ c.IsFree w ε :=
    fun hwu hwx ε => isFree_unsetEdge_of_ne c hwu hwx ε
  have f₂ : ∀ {w} (hwb : w ≠ b) (hwu : w ≠ u) ε, φ₂.IsFree w ε ↔ φ₁.IsFree w ε :=
    fun hwb hwu ε => isFree_unsetEdge_of_ne φ₁ hwb hwu ε
  have f2uδ : φ₂.IsFree u δ := (isFree_unsetEdge_right φ₁ d5.bu hφ₁bu δ).2 (Or.inl rfl)
  have f1uγ : φ₁.IsFree u γ := (isFree_unsetEdge_left c d5.ux h.hux γ).2 (Or.inl rfl)
  have f2uγ : φ₂.IsFree u γ := (isFree_unsetEdge_right φ₁ d5.bu hφ₁bu γ).2 (Or.inr f1uγ)
  have f1xσ : φ₁.IsFree x σ := (isFree_unsetEdge_right c d5.ux h.hux σ).2 (Or.inr hxσ)
  have f2xσ : φ₂.IsFree x σ := (f₂ d5.bx.symm d5.ux.symm σ).2 f1xσ
  have f2yσ : φ₂.IsFree y σ :=
    (f₂ d5.by_.symm d5.uy.symm σ).2 ((f₁ d5.uy.symm d5.xy.symm σ).2 h.σy)
  have f2bδ : φ₂.IsFree b δ := (isFree_unsetEdge_left φ₁ d5.bu hφ₁bu δ).2 (Or.inl rfl)
  have f2bβ : φ₂.IsFree b β := (isFree_unsetEdge_left φ₁ d5.bu hφ₁bu β).2
    (Or.inr ((f₁ d5.bu d5.bx β).2 h.βb))
  have f2a : ∀ ε, φ₂.IsFree a ε ↔ c.IsFree a ε := fun ε =>
    (f₂ d5.ab d5.au ε).trans (f₁ d5.au d5.ax ε)
  -- `u` and `y` are `(σ, δ)`-linked in φ₂ (pendant lemma: `a` is isolated)
  have hlink₂ : (φ₂.kempeGraph σ δ).Reachable y u := by
    rw [kempeGraph_comm]
    refine (reach_of_pendant (a := a) (w := b) (H' := ψ.kempeGraph δ σ) (fun p q hpq => ?_)
      (fun q hq => ?_) d5.ab.symm d5.au.symm d5.ay.symm hlinkψ).symm
    · obtain ⟨hne, hc⟩ := hpq
      by_cases hab : (p = a ∧ q = b) ∨ (p = b ∧ q = a)
      · right
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      by_cases hbu : (p = b ∧ q = u) ∨ (p = u ∧ q = b)
      · exfalso
        have : ψ.col p q = none := by
          rcases hbu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [ψ.col_symm]; exact hcmψ.uncol
          · exact hcmψ.uncol
        rw [this] at hc
        rcases hc with hc | hc <;> cases hc
      rw [hoff p q hab hbu] at hc
      by_cases hux : (p = u ∧ q = x) ∨ (p = x ∧ q = u)
      · exfalso
        have : c.col p q = some γ := by
          rcases hux with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h.hux
          · rw [c.col_symm]; exact h.hux
        rw [this] at hc
        rcases hc with hc | hc <;> simp only [Option.some.injEq] at hc
        · exact hδγ hc.symm
        · exact hσγ hc.symm
      left
      exact ⟨hne, by rw [hcol₂ p q hux hbu]; exact hc⟩
    · obtain ⟨-, hc⟩ := hq
      have hfa : ∀ ε, φ₂.IsFree a ε → φ₂.col a q ≠ some ε := fun ε hf => hf q
      rcases hc with hc | hc
      · exact hfa δ ((f2a δ).2 h.δa) hc
      · exact hfa σ ((f2a σ).2 h.σa) hc
  -- swap the `(σ, δ)`-chain of `y`
  have hny : ∀ {z}, (φ₂.IsFree z σ ∨ φ₂.IsFree z δ) → z ≠ y → z ≠ u →
      ¬ (φ₂.kempeGraph σ δ).Reachable y z := fun hz hzy hzu r =>
    not_three_linked φ₂ d5.uy.symm (Ne.symm hzy) (Ne.symm hzu |> fun h' => by
      intro e; exact hzu e.symm) (Or.inl f2yσ) (Or.inr f2uδ) hz hlink₂ r
  have hnx := hny (Or.inl f2xσ) d5.xy d5.ux.symm
  have hnb := hny (Or.inr f2bδ) d5.by_ d5.bu
  have hna : ¬ (φ₂.kempeGraph σ δ).Reachable y a := fun r =>
    d5.ay (eq_of_reachable_of_free_both φ₂ ((f2a σ).2 h.σa) ((f2a δ).2 h.δa) r.symm).symm
  set φ₃ := φ₂.kempeSwap σ δ y with hφ₃
  have f3uσ : φ₃.IsFree u σ := (kfree_flip₂ φ₂ hlink₂).2 f2uδ
  have f3xσ : φ₃.IsFree x σ := (kfree_off φ₂ hnx σ).2 f2xσ
  have f3uγ : φ₃.IsFree u γ := (kfree_of_ne φ₂ hσγ.symm hδγ.symm).2 f2uγ
  have f3b := kfree_off φ₂ hnb
  have f3a := kfree_off φ₂ hna
  have hadjux : G.Adj u x := c.col_adj h.hux
  set φ₄ := φ₃.setEdge σ hadjux f3uσ f3xσ with hφ₄
  have f4uγ : φ₄.IsFree u γ := setEdge_isFree_left φ₃ hadjux f3uσ f3xσ hσγ.symm
    (fun w _ => f3uγ w)
  have f4b : ∀ ε, φ₄.IsFree b ε ↔ φ₃.IsFree b ε := fun ε =>
    isFree_setEdge_of_ne φ₃ σ hadjux f3uσ f3xσ d5.bu d5.bx ε
  have f4a : ∀ ε, φ₄.IsFree a ε ↔ φ₃.IsFree a ε := fun ε =>
    isFree_setEdge_of_ne φ₃ σ hadjux f3uσ f3xσ d5.au d5.ax ε
  -- the `(β, γ)`-chain of `u` in φ₄ does not reach `b`
  have hR4 : ¬ (φ₄.kempeGraph β γ).Reachable u b := by
    intro r
    refine hR (reachable_mono_of_agree (fun p q hpq => ?_) r)
    by_cases hux : (p = u ∧ q = x) ∨ (p = x ∧ q = u)
    · exfalso
      rw [hφ₄, setEdge_col] at hpq
      unfold updFun at hpq
      rw [if_pos hux] at hpq
      rcases hpq with e | e <;> simp only [Option.some.injEq] at e
      · exact hσβ e
      · exact hσγ e
    rw [hφ₄, setEdge_col_off φ₃ hadjux f3uσ f3xσ hux] at hpq ⊢
    by_cases hbu : (p = b ∧ q = u) ∨ (p = u ∧ q = b)
    · exfalso
      have : φ₂.col p q = none := by
        rcases hbu with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rw [hp, hq]
        · exact unsetEdge_col_self φ₁ b u
        · rw [φ₂.col_symm]; exact unsetEdge_col_self φ₁ b u
      rcases hpq with e | e
      · rw [hφ₃, kcol_eq_iff_of_ne φ₂ y p q hσβ.symm hδβ.symm, this] at e; cases e
      · rw [hφ₃, kcol_eq_iff_of_ne φ₂ y p q hσγ.symm hδγ.symm, this] at e; cases e
    have h₂₁ : φ₂.col p q = φ₁.col p q := by
      rw [hφ₂, unsetEdge_col_of_ne _ hbu]
    rcases hpq with e | e
    · rw [hφ₃] at e
      rw [kcol_eq_iff_of_ne φ₂ y p q hσβ.symm hδβ.symm, h₂₁] at e
      rw [e]; symm; rw [hφ₃, kcol_eq_iff_of_ne φ₂ y p q hσβ.symm hδβ.symm, h₂₁]; exact e
    · rw [hφ₃] at e
      rw [kcol_eq_iff_of_ne φ₂ y p q hσγ.symm hδγ.symm, h₂₁] at e
      rw [e]; symm; rw [hφ₃, kcol_eq_iff_of_ne φ₂ y p q hσγ.symm hδγ.symm, h₂₁]; exact e
  -- swap it, colour `bu` by `β` and `ab` by `δ`
  have hnb4 : ¬ (φ₄.kempeGraph β γ).Reachable u b := hR4
  set φ₅ := φ₄.kempeSwap β γ u with hφ₅
  have f5uβ : φ₅.IsFree u β := (kfree_flip₂ φ₄ (Reachable.refl u)).2 f4uγ
  have f5bβ : φ₅.IsFree b β :=
    (kfree_off φ₄ hnb4 β).2 ((f4b β).2 ((f3b β).2 f2bβ))
  have f5bδ : φ₅.IsFree b δ :=
    (kfree_off φ₄ hnb4 δ).2 ((f4b δ).2 ((f3b δ).2 f2bδ))
  have f5aδ : φ₅.IsFree a δ :=
    (kfree_of_ne φ₄ hδβ hδγ).2 ((f4a δ).2 ((f3a δ).2 ((f2a δ).2 h.δa)))
  have hadjbu : G.Adj b u := c.col_adj h.hbu
  set φ₆ := φ₅.setEdge β hadjbu f5bβ f5uβ with hφ₆
  have f6bδ : φ₆.IsFree b δ := setEdge_isFree_left φ₅ hadjbu f5bβ f5uβ hδβ (fun w _ => f5bδ w)
  have f6aδ : φ₆.IsFree a δ := (isFree_setEdge_of_ne φ₅ β hadjbu f5bβ f5uβ d5.ab d5.au δ).2 f5aδ
  -- φ₆ is a colouring of `G − ab`
  have hext : Extends φ₄ φ₆ :=
    (extends_kempeSwap φ₄ β γ u).trans (extends_setEdge φ₅ β hadjbu f5bβ f5uβ)
  have hcm6 : IsColMinus φ₆ a b := by
    refine ⟨h.cm.adj, ?_, fun p q hpq hne => ?_⟩
    · rw [hφ₆, setEdge_col_off φ₅ hadjbu f5bβ f5uβ (by have := d5.ab; have := d5.au; tauto),
        hφ₅]
      refine kempeSwap_col_none φ₄ β γ u ?_
      rw [hφ₄, setEdge_col_off φ₃ hadjux f3uσ f3xσ (by have := d5.au; have := d5.ax; tauto), hφ₃]
      refine kempeSwap_col_none φ₂ σ δ y ?_
      rw [hcol₂ a b (by have := d5.au; have := d5.ax; tauto)
        (by have := d5.ab; have := d5.au; tauto)]
      exact h.cm.uncol
    · by_cases hbu : (p = b ∧ q = u) ∨ (p = u ∧ q = b)
      · rw [hφ₆, setEdge_col, updFun, if_pos hbu]; exact Option.some_ne_none _
      refine hext p q ?_
      by_cases hux : (p = u ∧ q = x) ∨ (p = x ∧ q = u)
      · rw [hφ₄, setEdge_col, updFun, if_pos hux]; exact Option.some_ne_none _
      rw [hφ₄, setEdge_col_off φ₃ hadjux f3uσ f3xσ hux, hφ₃]
      refine extends_kempeSwap φ₂ σ δ y p q ?_
      rw [hcol₂ p q hux hbu]
      exact h.cm.total p q hpq hne
  exact close_uncol hG hcm6 f6aδ f6bδ

end BNF

end Overfull
