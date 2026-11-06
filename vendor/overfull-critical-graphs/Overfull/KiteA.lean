/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.ShortKite

/-!
# Kites, part A: the first chain lemma

Setting of CCJS Lemma 2.8 in its normal form: `φ ∈ C^Δ(G − ab)`, `b` misses `β`, `φ(bu) = α`
with `α` missing at `a` and at `t`, `φ(us) = β`, `φ(st) = γ` with `γ` missing at `a`, and `t`
misses `β`.

`x_reach`: after uncolouring `bu`, the `(α, γ)`-chain of `t` reaches `u` (it does not avoid `bu`,
and it does not meet `b` before `u`). Otherwise either `a` and `b` are not `(α, β)`-linked, or the
recolouring `st → β`, swap of the chain to `b`, `us → α`, `bu → β`, `ab → γ` colours `G`.

`reach_split`: removing an edge `pq` from a graph, every vertex reachable from `p` stays reachable
from `p` or from `q`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Removing the edge `pq`: what `p` reached is reached from `p` or from `q`. -/
theorem reach_split {H H' : SimpleGraph V} {p q : V}
    (hsub : ∀ x y, H.Adj x y → H'.Adj x y ∨ s(x, y) = s(p, q)) {z : V} (h : H.Reachable p z) :
    H'.Reachable p z ∨ H'.Reachable q z := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl (Reachable.refl p)
  | tail _ hadj ih =>
    rename_i x y _
    rcases hsub x y hadj with h' | he
    · rcases ih with r | r
      · exact Or.inl (r.trans h'.reachable)
      · exact Or.inr (r.trans h'.reachable)
    · rcases Sym2.eq_iff.1 he with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr (Reachable.refl _)
      · exact Or.inl (Reachable.refl _)

/-- **The first chain lemma.** -/
theorem x_reach (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b u s t : V}
    (hab : a ≠ b) (hau : a ≠ u) (has : a ≠ s) (hat : a ≠ t) (hbu' : b ≠ u) (hbs : b ≠ s)
    (hbt : b ≠ t) (hus' : u ≠ s) (hut : u ≠ t) (hst' : s ≠ t) (cm : IsColMinus c a b)
    {α β γ : Fin G.maxDegree} (βb : c.IsFree b β) (hbu : c.col b u = some α)
    (αa : c.IsFree a α) (hus : c.col u s = some β) (hst : c.col s t = some γ)
    (γa : c.IsFree a γ) (αt : c.IsFree t α) (βt : c.IsFree t β) :
    ((unsetEdge c b u).kempeGraph α γ).Reachable t u := by
  obtain ⟨hdis, -⟩ := cm.ab_facts hG
  have hαβ : α ≠ β := fun e => hdis α αa (e ▸ βb)
  have hγβ : γ ≠ β := fun e => hdis γ γa (e ▸ βb)
  have hαγ : α ≠ γ := fun e => αt s (by rw [c.col_symm, hst, e])
  set φ₀ := unsetEdge c b u with hφ₀
  have f0 : ∀ {w}, w ≠ b → w ≠ u → ∀ ε, φ₀.IsFree w ε ↔ c.IsFree w ε :=
    fun h1 h2 ε => isFree_unsetEdge_of_ne c h1 h2 ε
  have f0bα : φ₀.IsFree b α := (isFree_unsetEdge_left c hbu' hbu α).2 (Or.inl rfl)
  have f0bβ : φ₀.IsFree b β := (isFree_unsetEdge_left c hbu' hbu β).2 (Or.inr βb)
  have f0uα : φ₀.IsFree u α := (isFree_unsetEdge_right c hbu' hbu α).2 (Or.inl rfl)
  have f0tβ := (f0 hbt.symm hut.symm β).2 βt
  have f0aα := (f0 hab hau α).2 αa
  have f0aγ := (f0 hab hau γ).2 γa
  have c0 : ∀ p q, ¬ ((p = b ∧ q = u) ∨ (p = u ∧ q = b)) → φ₀.col p q = c.col p q :=
    fun p q h => unsetEdge_col_of_ne c h
  have c0st : φ₀.col s t = some γ := by
    rw [c0 s t (not_pair (Or.inl hbs.symm) (Or.inl hus'.symm))]; exact hst
  have c0us : φ₀.col u s = some β := by
    rw [c0 u s (not_pair (Or.inl hbu'.symm) (Or.inr hbs.symm))]; exact hus
  have c0ab : φ₀.col a b = none := by
    rw [c0 a b (not_pair (Or.inl hab) (Or.inl hau))]; exact cm.uncol
  have hts : (φ₀.kempeGraph α γ).Reachable t s :=
    (kempeGraph_adj_of_col (Or.inr (by rw [φ₀.col_symm]; exact c0st))).reachable
  have hna : ¬ (φ₀.kempeGraph α γ).Reachable t a := fun r =>
    hat (eq_of_reachable_of_free_both φ₀ f0aα f0aγ r.symm).symm
  have hadjbu : G.Adj b u := c.col_adj hbu
  have hadjus : G.Adj u s := c.col_adj hus
  have hadjst : G.Adj s t := c.col_adj hst
  by_contra hr
  by_cases hb : (φ₀.kempeGraph α γ).Reachable t b
  · -- the chain meets `b` before `u`: colour `G`
    set φ₁ := φ₀.kempeSwap α γ t with hφ₁
    have f1bγ : φ₁.IsFree b γ := (kfree_flip₁ φ₀ hb).2 f0bα
    have f1bβ : φ₁.IsFree b β := (kfree_of_ne φ₀ hαβ.symm hγβ.symm).2 f0bβ
    have f1tβ : φ₁.IsFree t β := (kfree_of_ne φ₀ hαβ.symm hγβ.symm).2 f0tβ
    have f1uα : φ₁.IsFree u α := (kfree_off φ₀ hr α).2 f0uα
    have f1aγ : φ₁.IsFree a γ := (kfree_off φ₀ hna γ).2 f0aγ
    have c1st : φ₁.col s t = some α := kcol_flip₂ φ₀ c0st hts
    have c1us : φ₁.col u s = some β := kcol_keep φ₀ c0us (Or.inl ⟨hαβ.symm, hγβ.symm⟩)
    set φ₂ := unsetEdge φ₁ s t with hφ₂
    set φ₃ := unsetEdge φ₂ u s with hφ₃
    have c2us : φ₂.col u s = some β := by
      rw [hφ₂, unsetEdge_col_of_ne φ₁ (not_pair (Or.inl hus') (Or.inl hut))]; exact c1us
    have f3sβ : φ₃.IsFree s β := (isFree_unsetEdge_right φ₂ hus' c2us β).2 (Or.inl rfl)
    have f3tβ : φ₃.IsFree t β := (isFree_unsetEdge_of_ne φ₂ hut.symm hst'.symm β).2
      ((isFree_unsetEdge_right φ₁ hst' c1st β).2 (Or.inr f1tβ))
    set φ₄ := φ₃.setEdge β hadjst f3sβ f3tβ with hφ₄
    have f3sα : φ₃.IsFree s α := (isFree_unsetEdge_right φ₂ hus' c2us α).2
      (Or.inr ((isFree_unsetEdge_left φ₁ hst' c1st α).2 (Or.inl rfl)))
    have f4sα : φ₄.IsFree s α := setEdge_isFree_left φ₃ hadjst f3sβ f3tβ hαβ (fun w _ => f3sα w)
    have f3uα : φ₃.IsFree u α := (isFree_unsetEdge_left φ₂ hus' c2us α).2
      (Or.inr ((isFree_unsetEdge_of_ne φ₁ hus' hut α).2 f1uα))
    have f4uα : φ₄.IsFree u α := (isFree_setEdge_of_ne φ₃ β hadjst f3sβ f3tβ hus' hut α).2 f3uα
    set φ₅ := φ₄.setEdge α hadjus f4uα f4sα with hφ₅
    have f3uβ : φ₃.IsFree u β := (isFree_unsetEdge_left φ₂ hus' c2us β).2 (Or.inl rfl)
    have f4uβ := (isFree_setEdge_of_ne φ₃ β hadjst f3sβ f3tβ hus' hut β).2 f3uβ
    have f5uβ : φ₅.IsFree u β :=
      setEdge_isFree_left φ₄ hadjus f4uα f4sα hαβ.symm (fun w _ => f4uβ w)
    have fx : ∀ {x}, x ≠ s → x ≠ t → x ≠ u → ∀ ε, φ₁.IsFree x ε → φ₅.IsFree x ε :=
      fun h1 h2 h3 ε h =>
        (isFree_setEdge_of_ne φ₄ α hadjus f4uα f4sα h3 h1 ε).2
          ((isFree_setEdge_of_ne φ₃ β hadjst f3sβ f3tβ h1 h2 ε).2
            ((isFree_unsetEdge_of_ne φ₂ h3 h1 ε).2 ((isFree_unsetEdge_of_ne φ₁ h1 h2 ε).2 h)))
    have f5bβ := fx hbs hbt hbu' β f1bβ
    set φ₆ := φ₅.setEdge β hadjbu f5bβ f5uβ with hφ₆
    have f6bγ : φ₆.IsFree b γ :=
      setEdge_isFree_left φ₅ hadjbu f5bβ f5uβ hγβ (fun w _ => fx hbs hbt hbu' γ f1bγ w)
    have f6aγ : φ₆.IsFree a γ :=
      (isFree_setEdge_of_ne φ₅ β hadjbu f5bβ f5uβ hab hau γ).2 (fx has hat hau γ f1aγ)
    have h65 : ∀ p q, ¬ ((p = b ∧ q = u) ∨ (p = u ∧ q = b)) → φ₆.col p q = φ₅.col p q :=
      fun p q h => setEdge_col_off φ₅ hadjbu f5bβ f5uβ h
    have h54 : ∀ p q, ¬ ((p = u ∧ q = s) ∨ (p = s ∧ q = u)) → φ₅.col p q = φ₄.col p q :=
      fun p q h => setEdge_col_off φ₄ hadjus f4uα f4sα h
    have h41 : ∀ p q, ¬ ((p = s ∧ q = t) ∨ (p = t ∧ q = s)) →
        ¬ ((p = u ∧ q = s) ∨ (p = s ∧ q = u)) → φ₄.col p q = φ₁.col p q := fun p q h1 h2 => by
      rw [hφ₄, setEdge_col_off φ₃ hadjst f3sβ f3tβ h1, hφ₃, unsetEdge_col_of_ne φ₂ h2, hφ₂,
        unsetEdge_col_of_ne φ₁ h1]
    have hcm6 : IsColMinus φ₆ a b := by
      refine ⟨cm.adj, ?_, fun p q hpq hne => ?_⟩
      · rw [h65 a b (not_pair (Or.inl hab) (Or.inl hau)),
          h54 a b (not_pair (Or.inl hau) (Or.inl has)),
          h41 a b (not_pair (Or.inl has) (Or.inl hat)) (not_pair (Or.inl hau) (Or.inl has)), hφ₁]
        exact kempeSwap_col_none φ₀ α γ t c0ab
      · by_cases e1 : (p = b ∧ q = u) ∨ (p = u ∧ q = b)
        · rw [hφ₆, setEdge_col, updFun, if_pos e1]; exact Option.some_ne_none _
        rw [h65 p q e1]
        by_cases e2 : (p = u ∧ q = s) ∨ (p = s ∧ q = u)
        · rw [hφ₅, setEdge_col, updFun, if_pos e2]; exact Option.some_ne_none _
        rw [h54 p q e2]
        by_cases e3 : (p = s ∧ q = t) ∨ (p = t ∧ q = s)
        · rw [hφ₄, setEdge_col, updFun, if_pos e3]; exact Option.some_ne_none _
        rw [h41 p q e3 e2, hφ₁]
        refine extends_kempeSwap φ₀ α γ t p q ?_
        rw [c0 p q e1]
        exact cm.total p q hpq hne
    exact close_uncol hG hcm6 f6aγ f6bγ
  · -- the chain avoids `bu`: then `a` and `b` are not `(α, β)`-linked
    set φ₁ := φ₀.kempeSwap α γ t with hφ₁
    have f1bα := (kfree_off φ₀ hb α).2 f0bα
    have f1uα := (kfree_off φ₀ hr α).2 f0uα
    set φ₂ := φ₁.setEdge α hadjbu f1bα f1uα with hφ₂
    have h21 : ∀ p q, ¬ ((p = b ∧ q = u) ∨ (p = u ∧ q = b)) → φ₂.col p q = φ₁.col p q :=
      fun p q h => setEdge_col_off φ₁ hadjbu f1bα f1uα h
    have hcm2 : IsColMinus φ₂ a b := by
      refine ⟨cm.adj, ?_, fun p q hpq hne => ?_⟩
      · rw [h21 a b (not_pair (Or.inl hab) (Or.inl hau)), hφ₁]
        exact kempeSwap_col_none φ₀ α γ t c0ab
      · by_cases e1 : (p = b ∧ q = u) ∨ (p = u ∧ q = b)
        · rw [hφ₂, setEdge_col, updFun, if_pos e1]; exact Option.some_ne_none _
        rw [h21 p q e1, hφ₁]
        refine extends_kempeSwap φ₀ α γ t p q ?_
        rw [c0 p q e1]
        exact cm.total p q hpq hne
    have f2aα : φ₂.IsFree a α :=
      (isFree_setEdge_of_ne φ₁ α hadjbu f1bα f1uα hab hau α).2 ((kfree_off φ₀ hna α).2 f0aα)
    have f2bβ : φ₂.IsFree b β := setEdge_isFree_left φ₁ hadjbu f1bα f1uα hαβ.symm
      (fun x _ => (kfree_of_ne (w := t) φ₀ hαβ.symm hγβ.symm).2 f0bβ x)
    have f2tβ : φ₂.IsFree t β := (isFree_setEdge_of_ne φ₁ α hadjbu f1bα f1uα hbt.symm hut.symm
      β).2 ((kfree_of_ne φ₀ hαβ.symm hγβ.symm).2 f0tβ)
    have c2bu : φ₂.col b u = some α := setEdge_col_self φ₁ hadjbu f1bα f1uα
    have c2us : φ₂.col u s = some β := by
      rw [h21 u s (not_pair (Or.inl hbu'.symm) (Or.inr hbs.symm))]
      exact kcol_keep φ₀ c0us (Or.inl ⟨hαβ.symm, hγβ.symm⟩)
    have c2st : φ₂.col s t = some α := by
      rw [h21 s t (not_pair (Or.inl hbs.symm) (Or.inl hus'.symm))]
      exact kcol_flip₂ φ₀ c0st hts
    have hl := ksAB_link hG hcm2 f2aα f2bβ
    have r3 := reachable_of_col (reachable_of_col (reachable_of_col hl (Or.inl c2bu))
      (Or.inr c2us)) (Or.inl c2st)
    exact not_three_linked φ₂ hab hat hbt (Or.inl f2aα) (Or.inr f2bβ) (Or.inr f2tβ) hl r3

end Overfull
