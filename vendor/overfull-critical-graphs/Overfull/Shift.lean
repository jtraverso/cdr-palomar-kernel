/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Kierstead

/-!
# Moving the uncoloured edge

`unsetEdge c x y` uncolours the edge `x y`. Together with `setEdge` of the Vizing entry this moves
the uncoloured edge: from a colouring of `G − y₀y₁` in which `y₁y₂` has a colour `δ` missing at
`y₀`, uncolouring `y₁y₂` and colouring `y₀y₁` with `δ` gives a colouring of `G − y₁y₂`
(`shift`). The missing colours change only at the three vertices involved.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Uncolour the edge `x y`. -/
def unsetEdge {k : ℕ} (c : PEC G (Fin k)) (x y : V) : PEC G (Fin k) where
  col := updFun c.col x y none
  col_symm u v := by
    unfold updFun
    by_cases h : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
    · rw [if_pos h, if_pos (by tauto)]
    · rw [if_neg h, if_neg (by tauto), c.col_symm]
  col_adj := fun {u v γ} h => by
    unfold updFun at h
    split_ifs at h
    exact c.col_adj h
  col_proper := fun {u v w γ} h1 h2 => by
    unfold updFun at h1 h2
    split_ifs at h1 h2
    exact c.col_proper h1 h2

theorem unsetEdge_col_of_ne {k : ℕ} (c : PEC G (Fin k)) {x y u v : V}
    (h : ¬ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) : (unsetEdge c x y).col u v = c.col u v :=
  updFun_of_ne _ h

theorem unsetEdge_col_self {k : ℕ} (c : PEC G (Fin k)) (x y : V) :
    (unsetEdge c x y).col x y = none :=
  updFun_left _

/-- Vertices other than `x, y` keep their missing colours. -/
theorem isFree_unsetEdge_of_ne {k : ℕ} (c : PEC G (Fin k)) {x y w : V} (hwx : w ≠ x)
    (hwy : w ≠ y) (γ : Fin k) : (unsetEdge c x y).IsFree w γ ↔ c.IsFree w γ := by
  constructor <;> intro h u hu
  · exact h u (by rw [unsetEdge_col_of_ne c (by tauto)]; exact hu)
  · exact h u (by rw [unsetEdge_col_of_ne c (by tauto)] at hu; exact hu)

/-- At `x`, the old colour of `x y` becomes missing, the other missing colours are kept. -/
theorem isFree_unsetEdge_left {k : ℕ} (c : PEC G (Fin k)) {x y : V} (hxy : x ≠ y) {δ : Fin k}
    (hδ : c.col x y = some δ) (γ : Fin k) :
    (unsetEdge c x y).IsFree x γ ↔ γ = δ ∨ c.IsFree x γ := by
  constructor
  · intro h
    by_cases hγ : γ = δ
    · exact Or.inl hγ
    · refine Or.inr fun u hu => ?_
      by_cases huy : u = y
      · subst huy
        exact hγ (Option.some_injective _ (hu.symm.trans hδ))
      · exact h u (by rw [unsetEdge_col_of_ne c (by tauto)]; exact hu)
  · rintro (rfl | h) u hu
    · by_cases huy : u = y
      · subst huy
        rw [unsetEdge_col_self] at hu
        cases hu
      · rw [unsetEdge_col_of_ne c (by tauto)] at hu
        exact huy (c.col_proper hu hδ)
    · by_cases huy : u = y
      · subst huy
        rw [unsetEdge_col_self] at hu
        cases hu
      · rw [unsetEdge_col_of_ne c (by tauto)] at hu
        exact h u hu

theorem isFree_unsetEdge_right {k : ℕ} (c : PEC G (Fin k)) {x y : V} (hxy : x ≠ y) {δ : Fin k}
    (hδ : c.col x y = some δ) (γ : Fin k) :
    (unsetEdge c x y).IsFree y γ ↔ γ = δ ∨ c.IsFree y γ := by
  have h' : (unsetEdge c x y) = (unsetEdge c y x) := by
    cases c
    simp only [unsetEdge, PEC.mk.injEq]
    funext u v
    unfold updFun
    by_cases h : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
    · rw [if_pos h, if_pos (by tauto)]
    · rw [if_neg h, if_neg (by tauto)]
  rw [h']
  exact isFree_unsetEdge_left c hxy.symm (by rw [c.col_symm]; exact hδ) γ

end Overfull
