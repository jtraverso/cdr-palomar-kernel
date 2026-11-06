/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.KiteA

/-!
# Kites, part B: the closing recolouring

In the normal form of a kite (`φ(bu) = α`, `φ(us₂) = δ ∈ φ̄(a)`, `φ(s₂t₂) = γ ∈ φ̄(a)`, `t₂` missing
`α, β, δ`), suppose that after uncolouring `bu` the `(α, γ)`-chain of `t₁` reaches `u`, and that
after uncolouring `us₂` the `(β, δ)`-chain of `u` ends at `a`. Then `G` is `Δ`-colourable:
uncolour `bu`, swap the `(α, γ)`-chain of `t₁`, uncolour `us₂`, swap the `(β, δ)`-chain of `u`,
colour `bu` by `β`, recolour `s₂t₂` by `δ`, colour `us₂` by `γ` and `ab` by `α`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

set_option maxHeartbeats 1600000 in
/-- **The closing recolouring.** -/
theorem y_close (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u s₁ s₂ t₁ t₂ : V}
    (hd : Distinct7 a b u s₁ s₂ t₁ t₂) (cm : IsColMinus c a b) {α β δ γ : Fin G.maxDegree}
    (βb : c.IsFree b β) (hbu : c.col b u = some α) (αa : c.IsFree a α)
    (hus₂ : c.col u s₂ = some δ) (δa : c.IsFree a δ) (hst₁ : c.col s₁ t₁ = some γ)
    (hst₂ : c.col s₂ t₂ = some γ) (γa : c.IsFree a γ) (α₁ : c.IsFree t₁ α)
    (α₂ : c.IsFree t₂ α) (β₂ : c.IsFree t₂ β) (δ₂ : c.IsFree t₂ δ)
    (hX : ((unsetEdge c b u).kempeGraph α γ).Reachable t₁ u)
    (hU : ((unsetEdge c u s₂).kempeGraph β δ).Reachable u a) : False := by
  obtain ⟨hdis, -⟩ := cm.ab_facts hG
  have hαβ : α ≠ β := fun e => hdis α αa (e ▸ βb)
  have hγβ : γ ≠ β := fun e => hdis γ γa (e ▸ βb)
  have hδβ : δ ≠ β := fun e => hdis δ δa (e ▸ βb)
  have hαγ : α ≠ γ := fun e => α₁ s₁ (by rw [c.col_symm, hst₁, e])
  have hαδ : α ≠ δ := fun e => hd.bs₂ (c.col_proper (by rw [c.col_symm]; exact hbu) (e ▸ hus₂))
  have hδγ : δ ≠ γ := fun e => hd.ut₂ (c.col_proper (by rw [c.col_symm]; exact hus₂)
    (by rw [e]; exact hst₂))
  have hadjbu : G.Adj b u := c.col_adj hbu
  have hadjus : G.Adj u s₂ := c.col_adj hus₂
  have hadjst : G.Adj s₂ t₂ := c.col_adj hst₂
  -- φ₀: uncolour `bu`
  set φ₀ := unsetEdge c b u with hφ₀
  have f0 : ∀ {w}, w ≠ b → w ≠ u → ∀ ε, φ₀.IsFree w ε ↔ c.IsFree w ε :=
    fun h1 h2 ε => isFree_unsetEdge_of_ne c h1 h2 ε
  have f0bα : φ₀.IsFree b α := (isFree_unsetEdge_left c hd.bu hbu α).2 (Or.inl rfl)
  have f0bβ : φ₀.IsFree b β := (isFree_unsetEdge_left c hd.bu hbu β).2 (Or.inr βb)
  have f0uα : φ₀.IsFree u α := (isFree_unsetEdge_right c hd.bu hbu α).2 (Or.inl rfl)
  have c0 : ∀ p q, ¬ ((p = b ∧ q = u) ∨ (p = u ∧ q = b)) → φ₀.col p q = c.col p q :=
    fun p q h => unsetEdge_col_of_ne c h
  have c0us : φ₀.col u s₂ = some δ := by
    rw [c0 u s₂ (not_pair (Or.inl hd.bu.symm) (Or.inr hd.bs₂.symm))]; exact hus₂
  have c0st : φ₀.col s₂ t₂ = some γ := by
    rw [c0 s₂ t₂ (not_pair (Or.inl hd.bs₂.symm) (Or.inl hd.us₂.symm))]; exact hst₂
  have c0ab : φ₀.col a b = none := by
    rw [c0 a b (not_pair (Or.inl hd.ab) (Or.inl hd.au))]; exact cm.uncol
  have f0t₁α := (f0 hd.bt₁.symm hd.ut₁.symm α).2 α₁
  have f0t₂α := (f0 hd.bt₂.symm hd.ut₂.symm α).2 α₂
  -- φ₁: swap the `(α, γ)`-chain of `t₁` (it ends at `u`)
  have hnb : ¬ (φ₀.kempeGraph α γ).Reachable t₁ b := fun r =>
    not_three_linked φ₀ hd.ut₁.symm hd.bt₁.symm hd.bu.symm (Or.inl f0t₁α) (Or.inl f0uα)
      (Or.inl f0bα) hX r
  have hnt : ¬ (φ₀.kempeGraph α γ).Reachable t₁ t₂ := fun r =>
    not_three_linked φ₀ hd.ut₁.symm hd.t₁t₂ hd.ut₂ (Or.inl f0t₁α) (Or.inl f0uα)
      (Or.inl f0t₂α) hX r
  have hns : ¬ (φ₀.kempeGraph α γ).Reachable t₁ s₂ := fun r => hnt (reachable_of_col r (Or.inr c0st))
  have hna : ¬ (φ₀.kempeGraph α γ).Reachable t₁ a := fun r =>
    hd.at₁ (eq_of_reachable_of_free_both φ₀ ((f0 hd.ab hd.au α).2 αa)
      ((f0 hd.ab hd.au γ).2 γa) r.symm).symm
  set φ₁ := φ₀.kempeSwap α γ t₁ with hφ₁
  have f1uγ : φ₁.IsFree u γ := (kfree_flip₁ φ₀ hX).2 f0uα
  have f1b := kfree_off φ₀ hnb
  have f1a := kfree_off φ₀ hna
  have f1t := kfree_off φ₀ hnt
  have c1us : φ₁.col u s₂ = some δ := kcol_keep φ₀ c0us (Or.inl ⟨hαδ.symm, hδγ⟩)
  have c1st : φ₁.col s₂ t₂ = some γ := kcol_keep φ₀ c0st (Or.inr hns)
  -- φ₂: uncolour `us₂`
  set φ₂ := unsetEdge φ₁ u s₂ with hφ₂
  have f2 : ∀ {w}, w ≠ u → w ≠ s₂ → ∀ ε, φ₂.IsFree w ε ↔ φ₁.IsFree w ε :=
    fun h1 h2 ε => isFree_unsetEdge_of_ne φ₁ h1 h2 ε
  have f2uγ : φ₂.IsFree u γ := (isFree_unsetEdge_left φ₁ hd.us₂ c1us γ).2 (Or.inr f1uγ)
  have f2uδ : φ₂.IsFree u δ := (isFree_unsetEdge_left φ₁ hd.us₂ c1us δ).2 (Or.inl rfl)
  have f2sδ : φ₂.IsFree s₂ δ := (isFree_unsetEdge_right φ₁ hd.us₂ c1us δ).2 (Or.inl rfl)
  have f2aδ : φ₂.IsFree a δ :=
    (f2 hd.au hd.as₂ δ).2 ((f1a δ).2 ((f0 hd.ab hd.au δ).2 δa))
  have f2aα : φ₂.IsFree a α :=
    (f2 hd.au hd.as₂ α).2 ((f1a α).2 ((f0 hd.ab hd.au α).2 αa))
  have f2bβ : φ₂.IsFree b β := (f2 hd.bu hd.bs₂ β).2 ((f1b β).2 f0bβ)
  have f2bα : φ₂.IsFree b α := (f2 hd.bu hd.bs₂ α).2 ((f1b α).2 f0bα)
  have f2tβ : φ₂.IsFree t₂ β :=
    (f2 hd.ut₂.symm hd.s₂t₂.symm β).2 ((f1t β).2 ((f0 hd.bt₂.symm hd.ut₂.symm β).2 β₂))
  have f2tδ : φ₂.IsFree t₂ δ :=
    (f2 hd.ut₂.symm hd.s₂t₂.symm δ).2 ((f1t δ).2 ((f0 hd.bt₂.symm hd.ut₂.symm δ).2 δ₂))
  have c2st : φ₂.col s₂ t₂ = some γ := by
    rw [hφ₂, unsetEdge_col_of_ne φ₁ (not_pair (Or.inl hd.us₂.symm) (Or.inr hd.ut₂.symm))]
    exact c1st
  have c2ab : φ₂.col a b = none := by
    rw [hφ₂, unsetEdge_col_of_ne φ₁ (not_pair (Or.inl hd.au) (Or.inl hd.as₂)), hφ₁]
    exact kempeSwap_col_none φ₀ α γ t₁ c0ab
  -- the `(β, δ)`-chain of `u` in φ₂ ends at `a`
  have hU2 : (φ₂.kempeGraph β δ).Reachable u a := by
    refine reachable_mono_of_agree (fun x y hxy => ?_) hU
    by_cases e1 : (x = u ∧ y = s₂) ∨ (x = s₂ ∧ y = u)
    · exfalso
      have : (unsetEdge c u s₂).col x y = none := by
        rcases e1 with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy]
        · exact unsetEdge_col_self c u s₂
        · rw [PEC.col_symm]; exact unsetEdge_col_self c u s₂
      rw [this] at hxy
      rcases hxy with e | e <;> cases e
    rw [unsetEdge_col_of_ne c e1] at hxy ⊢
    rw [hφ₂, unsetEdge_col_of_ne φ₁ e1]
    by_cases e2 : (x = b ∧ y = u) ∨ (x = u ∧ y = b)
    · exfalso
      have : c.col x y = some α := by
        rcases e2 with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy]
        · exact hbu
        · rw [c.col_symm]; exact hbu
      rw [this] at hxy
      rcases hxy with e | e <;> simp only [Option.some.injEq] at e
      · exact hαβ e
      · exact hαδ e
    rcases hxy with e | e
    · rw [e, hφ₁, kcol_eq_iff_of_ne φ₀ t₁ x y hαβ.symm hγβ.symm, c0 x y e2]; exact e
    · rw [e, hφ₁, kcol_eq_iff_of_ne φ₀ t₁ x y hαδ.symm hδγ, c0 x y e2]; exact e
  have hnb3 : ¬ (φ₂.kempeGraph β δ).Reachable u b := fun r =>
    not_three_linked φ₂ hd.au.symm hd.bu.symm hd.ab (Or.inr f2uδ) (Or.inr f2aδ) (Or.inl f2bβ)
      hU2 r
  have hns3 : ¬ (φ₂.kempeGraph β δ).Reachable u s₂ := fun r =>
    not_three_linked φ₂ hd.au.symm hd.us₂ hd.as₂ (Or.inr f2uδ) (Or.inr f2aδ) (Or.inr f2sδ) hU2 r
  have hnt3 : ¬ (φ₂.kempeGraph β δ).Reachable u t₂ := fun r =>
    hd.ut₂ (eq_of_reachable_of_free_both φ₂ f2tβ f2tδ r.symm)
  -- φ₃: swap it
  set φ₃ := φ₂.kempeSwap β δ u with hφ₃
  have f3uβ : φ₃.IsFree u β := (kfree_flip₂ φ₂ (Reachable.refl u)).2 f2uδ
  have f3uγ : φ₃.IsFree u γ := (kfree_of_ne φ₂ hγβ hδγ.symm).2 f2uγ
  have f3b := kfree_off φ₂ hnb3
  have f3aα : φ₃.IsFree a α := (kfree_of_ne φ₂ hαβ hαδ).2 f2aα
  have f3sδ : φ₃.IsFree s₂ δ := (kfree_off φ₂ hns3 δ).2 f2sδ
  have f3tδ : φ₃.IsFree t₂ δ := (kfree_off φ₂ hnt3 δ).2 f2tδ
  have c3st : φ₃.col s₂ t₂ = some γ := kcol_keep φ₂ c2st (Or.inl ⟨hγβ, hδγ.symm⟩)
  -- φ₄: colour `bu` by `β`
  have f3bβ := (f3b β).2 f2bβ
  set φ₄ := φ₃.setEdge β hadjbu f3bβ f3uβ with hφ₄
  have f4 : ∀ {w}, w ≠ b → w ≠ u → ∀ ε, φ₄.IsFree w ε ↔ φ₃.IsFree w ε :=
    fun h1 h2 ε => isFree_setEdge_of_ne φ₃ β hadjbu f3bβ f3uβ h1 h2 ε
  have f4bα : φ₄.IsFree b α :=
    setEdge_isFree_left φ₃ hadjbu f3bβ f3uβ hαβ (fun x _ => (f3b α).2 f2bα x)
  have f4uγ : φ₄.IsFree u γ := setEdge_isFree_right φ₃ hadjbu f3bβ f3uβ hγβ (fun x _ => f3uγ x)
  have c4st : φ₄.col s₂ t₂ = some γ := by
    rw [hφ₄, setEdge_col_off φ₃ hadjbu f3bβ f3uβ
      (not_pair (Or.inl hd.bs₂.symm) (Or.inl hd.us₂.symm))]
    exact c3st
  -- φ₅, φ₆: recolour `s₂t₂` by `δ`
  set φ₅ := unsetEdge φ₄ s₂ t₂ with hφ₅
  have f5sδ : φ₅.IsFree s₂ δ := (isFree_unsetEdge_left φ₄ hd.s₂t₂ c4st δ).2
    (Or.inr ((f4 hd.bs₂.symm hd.us₂.symm δ).2 f3sδ))
  have f5sγ : φ₅.IsFree s₂ γ := (isFree_unsetEdge_left φ₄ hd.s₂t₂ c4st γ).2 (Or.inl rfl)
  have f5tδ : φ₅.IsFree t₂ δ := (isFree_unsetEdge_right φ₄ hd.s₂t₂ c4st δ).2
    (Or.inr ((f4 hd.bt₂.symm hd.ut₂.symm δ).2 f3tδ))
  have f5uγ : φ₅.IsFree u γ := (isFree_unsetEdge_of_ne φ₄ hd.us₂ hd.ut₂ γ).2 f4uγ
  set φ₆ := φ₅.setEdge δ hadjst f5sδ f5tδ with hφ₆
  have f6sγ : φ₆.IsFree s₂ γ :=
    setEdge_isFree_left φ₅ hadjst f5sδ f5tδ hδγ.symm (fun x _ => f5sγ x)
  have f6uγ : φ₆.IsFree u γ :=
    (isFree_setEdge_of_ne φ₅ δ hadjst f5sδ f5tδ hd.us₂ hd.ut₂ γ).2 f5uγ
  -- φ₇: colour `us₂` by `γ`
  set φ₇ := φ₆.setEdge γ hadjus f6uγ f6sγ with hφ₇
  have f74 : ∀ {w}, w ≠ u → w ≠ s₂ → w ≠ t₂ → ∀ ε, φ₄.IsFree w ε → φ₇.IsFree w ε :=
    fun h1 h2 h3 ε h =>
      (isFree_setEdge_of_ne φ₆ γ hadjus f6uγ f6sγ h1 h2 ε).2
        ((isFree_setEdge_of_ne φ₅ δ hadjst f5sδ f5tδ h2 h3 ε).2
          ((isFree_unsetEdge_of_ne φ₄ h2 h3 ε).2 h))
  have f7aα : φ₇.IsFree a α :=
    f74 hd.au hd.as₂ hd.at₂ α ((f4 hd.ab hd.au α).2 f3aα)
  have f7bα : φ₇.IsFree b α := f74 hd.bu hd.bs₂ hd.bt₂ α f4bα
  -- φ₇ is a colouring of `G − ab`
  have h73 : ∀ p q, ¬ ((p = u ∧ q = s₂) ∨ (p = s₂ ∧ q = u)) →
      ¬ ((p = s₂ ∧ q = t₂) ∨ (p = t₂ ∧ q = s₂)) → ¬ ((p = b ∧ q = u) ∨ (p = u ∧ q = b)) →
      φ₇.col p q = φ₃.col p q := fun p q e1 e2 e3 => by
    rw [hφ₇, setEdge_col_off φ₆ hadjus f6uγ f6sγ e1, hφ₆, setEdge_col_off φ₅ hadjst f5sδ f5tδ e2,
      hφ₅, unsetEdge_col_of_ne φ₄ e2, hφ₄, setEdge_col_off φ₃ hadjbu f3bβ f3uβ e3]
  have hcm7 : IsColMinus φ₇ a b := by
    refine ⟨cm.adj, ?_, fun p q hpq hne => ?_⟩
    · rw [h73 a b (not_pair (Or.inl hd.au) (Or.inl hd.as₂))
        (not_pair (Or.inl hd.as₂) (Or.inl hd.at₂)) (not_pair (Or.inl hd.ab) (Or.inl hd.au)), hφ₃]
      exact kempeSwap_col_none φ₂ β δ u c2ab
    · by_cases e1 : (p = u ∧ q = s₂) ∨ (p = s₂ ∧ q = u)
      · rw [hφ₇, setEdge_col, updFun, if_pos e1]; exact Option.some_ne_none _
      by_cases e2 : (p = s₂ ∧ q = t₂) ∨ (p = t₂ ∧ q = s₂)
      · rw [hφ₇, setEdge_col_off φ₆ hadjus f6uγ f6sγ e1, hφ₆, setEdge_col, updFun, if_pos e2]
        exact Option.some_ne_none _
      by_cases e3 : (p = b ∧ q = u) ∨ (p = u ∧ q = b)
      · rw [hφ₇, setEdge_col_off φ₆ hadjus f6uγ f6sγ e1, hφ₆, setEdge_col_off φ₅ hadjst f5sδ f5tδ e2,
          hφ₅, unsetEdge_col_of_ne φ₄ e2, hφ₄, setEdge_col, updFun, if_pos e3]
        exact Option.some_ne_none _
      rw [h73 p q e1 e2 e3, hφ₃]
      refine extends_kempeSwap φ₂ β δ u p q ?_
      rw [hφ₂, unsetEdge_col_of_ne φ₁ e1, hφ₁]
      refine extends_kempeSwap φ₀ α γ t₁ p q ?_
      rw [c0 p q e3]
      exact cm.total p q hpq hne
  exact close_uncol hG hcm7 f7aα f7bα

end Overfull
