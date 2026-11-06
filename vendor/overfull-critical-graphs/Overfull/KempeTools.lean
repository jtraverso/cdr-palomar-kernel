/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Kierstead4

/-!
# Kempe-chain tools for the fork lemma

* `A c a b θ`: `θ` is missing at `a` or at `b`.
* Chains of a vertex missing both colours are trivial (`eq_of_reachable_of_free_both`).
* Swapping the chain of a vertex `w ∉ {a, b}` that misses `θ` or `η`, with `θ, η ∈ A`, keeps the
  missing colours of `a` and `b` (`kempeSwap_keeps_ab`).
* `kempeSwapCompl c θ η w`: exchange `θ` and `η` on every `(θ, η)`-chain except the one of `w`
  ("switch the colours on all other chains").
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `θ` belongs to `A(φ) = φ̄(a) ∪ φ̄(b)`. -/
def InA {k : ℕ} (c : PEC G (Fin k)) (a b : V) (θ : Fin k) : Prop := c.IsFree a θ ∨ c.IsFree b θ

/-- A vertex missing both colours is alone in its Kempe chain. -/
theorem eq_of_reachable_of_free_both {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w x : V}
    (hθ : c.IsFree w θ) (hη : c.IsFree w η) (h : (c.kempeGraph θ η).Reachable w x) : x = w := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ =>
    exfalso
    rcases hadj.2 with h | h
    · exact hθ _ h
    · exact hη _ h

/-- The chain of a vertex `w ∉ {a, b}` missing `θ` or `η` (`θ, η ∈ A`) does not contain `a` or
`b`, unless that vertex misses neither colour. -/
theorem chain_avoids_ab (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b : V}
    (hcm : IsColMinus c a b) {θ η : Fin G.maxDegree} (hθ : InA c a b θ) (hη : InA c a b η)
    {w : V} (hw : c.IsFree w θ ∨ c.IsFree w η) (hwa : w ≠ a) (hwb : w ≠ b) {z : V}
    (hz : z = a ∨ z = b) :
    ¬ (c.kempeGraph θ η).Reachable w z ∨ (¬ c.IsFree z θ ∧ ¬ c.IsFree z η) := by
  obtain ⟨hdis, hlink⟩ := hcm.ab_facts hG
  have hab := hcm.adj.ne
  -- both colours on the same side: that end is isolated, the other misses neither
  have same : ∀ {p q : V}, (p = a ∧ q = b ∨ p = b ∧ q = a) → c.IsFree p θ → c.IsFree p η →
      ¬ (c.kempeGraph θ η).Reachable w z ∨ (¬ c.IsFree z θ ∧ ¬ c.IsFree z η) := by
    intro p q hpq hpθ hpη
    have hqθ : ¬ c.IsFree q θ := by
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hdis θ hpθ
      · exact fun h => hdis θ h hpθ
    have hqη : ¬ c.IsFree q η := by
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hdis η hpη
      · exact fun h => hdis η h hpη
    by_cases hzp : z = p
    · subst hzp
      refine Or.inl fun r => ?_
      have := eq_of_reachable_of_free_both c hpθ hpη r.symm
      rcases hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hwa this
      · exact hwb this
    · have hzq : z = q := by
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
      subst hzq
      exact Or.inr ⟨hqθ, hqη⟩
  -- colours on different sides: `a` and `b` are linked, so `w` is not with them
  have split : (c.kempeGraph θ η).Reachable a b →
      (c.IsFree a θ ∨ c.IsFree a η) → (c.IsFree b θ ∨ c.IsFree b η) →
      ¬ (c.kempeGraph θ η).Reachable w z ∨ (¬ c.IsFree z θ ∧ ¬ c.IsFree z η) := by
    intro hl ha hb
    refine Or.inl fun r => ?_
    rcases hz with rfl | rfl
    · exact not_three_linked c hab hwa.symm hwb.symm ha hb hw hl r.symm
    · exact not_three_linked c hab hwa.symm hwb.symm ha hb hw hl (hl.trans r.symm)
  rcases hθ with hθa | hθb <;> rcases hη with hηa | hηb
  · exact same (Or.inl ⟨rfl, rfl⟩) hθa hηa
  · exact split (hlink θ η hθa hηb) (Or.inl hθa) (Or.inr hηb)
  · have hl := hlink η θ hηa hθb
    rw [kempeGraph_comm] at hl
    exact split hl (Or.inr hηa) (Or.inl hθb)
  · exact same (Or.inr ⟨rfl, rfl⟩) hθb hηb

/-- At a vertex missing neither colour, a Kempe swap keeps the missing colours. -/
theorem isFree_kempeSwap_of_neither {k : ℕ} (c : PEC G (Fin k)) (θ η : Fin k) (w : V) {z : V}
    (hθ : ¬ c.IsFree z θ) (hη : ¬ c.IsFree z η) (ε : Fin k) :
    (c.kempeSwap θ η w).IsFree z ε ↔ c.IsFree z ε := by
  by_cases hr : (c.kempeGraph θ η).Reachable w z
  · rw [isFree_kempeSwap_of_reachable c θ η hr]
    by_cases h1 : ε = θ
    · subst h1
      rw [Equiv.swap_apply_left]
      exact ⟨fun h => absurd h hη, fun h => absurd h hθ⟩
    by_cases h2 : ε = η
    · subst h2
      rw [Equiv.swap_apply_right]
      exact ⟨fun h => absurd h hθ, fun h => absurd h hη⟩
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  · exact isFree_kempeSwap_of_not_reachable c θ η hr ε

/-- Swapping the chain of `w ∉ {a, b}` (missing `θ` or `η`, both in `A`) keeps the missing colours
of `a` and `b`. -/
theorem kempeSwap_keeps_ab (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b : V}
    (hcm : IsColMinus c a b) {θ η : Fin G.maxDegree} (hθ : InA c a b θ) (hη : InA c a b η)
    {w : V} (hw : c.IsFree w θ ∨ c.IsFree w η) (hwa : w ≠ a) (hwb : w ≠ b) {z : V}
    (hz : z = a ∨ z = b) (ε : Fin G.maxDegree) :
    (c.kempeSwap θ η w).IsFree z ε ↔ c.IsFree z ε := by
  rcases chain_avoids_ab hG hcm hθ hη hw hwa hwb hz with h | ⟨h1, h2⟩
  · exact isFree_kempeSwap_of_not_reachable c θ η h ε
  · exact isFree_kempeSwap_of_neither c θ η w h1 h2 ε

theorem inA_kempeSwap_keeps (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b : V}
    (hcm : IsColMinus c a b) {θ η : Fin G.maxDegree} (hθ : InA c a b θ) (hη : InA c a b η)
    {w : V} (hw : c.IsFree w θ ∨ c.IsFree w η) (hwa : w ≠ a) (hwb : w ≠ b) (ε : Fin G.maxDegree) :
    InA (c.kempeSwap θ η w) a b ε ↔ InA c a b ε := by
  unfold InA
  rw [kempeSwap_keeps_ab hG hcm hθ hη hw hwa hwb (Or.inl rfl),
    kempeSwap_keeps_ab hG hcm hθ hη hw hwa hwb (Or.inr rfl)]

/-! ### Permuting colours -/

/-- Rename the colours by a permutation. -/
def permCol {k : ℕ} (c : PEC G (Fin k)) (σ : Equiv.Perm (Fin k)) : PEC G (Fin k) where
  col x y := (c.col x y).map σ
  col_symm x y := by rw [c.col_symm]
  col_adj := fun {x y γ} h => by
    cases hc : c.col x y with
    | none => rw [hc] at h; cases h
    | some ε => exact c.col_adj hc
  col_proper := fun {x y z γ} h1 h2 => by
    cases hc1 : c.col x y with
    | none => rw [hc1] at h1; cases h1
    | some ε₁ =>
      cases hc2 : c.col x z with
      | none => rw [hc2] at h2; cases h2
      | some ε₂ =>
        rw [hc1] at h1
        rw [hc2] at h2
        simp only [Option.map_some, Option.some.injEq] at h1 h2
        have : ε₁ = ε₂ := σ.injective (h1.trans h2.symm)
        subst this
        exact c.col_proper hc1 hc2

theorem permCol_col {k : ℕ} (c : PEC G (Fin k)) (σ : Equiv.Perm (Fin k)) (x y : V) :
    (permCol c σ).col x y = (c.col x y).map σ := rfl

theorem isFree_permCol {k : ℕ} (c : PEC G (Fin k)) (σ : Equiv.Perm (Fin k)) (v : V)
    (ε : Fin k) : (permCol c σ).IsFree v ε ↔ c.IsFree v (σ.symm ε) := by
  constructor
  · intro h x hx
    refine h x ?_
    rw [permCol_col, hx]
    simp
  · intro h x hx
    rw [permCol_col] at hx
    cases hc : c.col v x with
    | none => rw [hc] at hx; cases hx
    | some ζ =>
      rw [hc] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      refine h x ?_
      rw [hc, ← hx]
      simp

theorem kempeGraph_permCol_swap {k : ℕ} (c : PEC G (Fin k)) (θ η : Fin k) :
    (permCol c (Equiv.swap θ η)).kempeGraph θ η = c.kempeGraph θ η := by
  ext x y
  simp only [kempeGraph_adj, permCol_col]
  constructor <;> rintro ⟨hne, h⟩ <;> refine ⟨hne, ?_⟩
  · cases hc : c.col x y with
    | none => rw [hc] at h; simp at h
    | some ζ =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rcases h with h | h
      · right
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
        rw [h]
      · left
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        rw [h]
  · rcases h with h | h <;> rw [h] <;> simp

theorem IsColMinus.permCol {k : ℕ} {c : PEC G (Fin k)} {a b : V} (hcm : IsColMinus c a b)
    (σ : Equiv.Perm (Fin k)) : IsColMinus (permCol c σ) a b :=
  ⟨hcm.adj, by rw [permCol_col, hcm.uncol]; rfl, fun x y hxy hne => by
    rw [permCol_col]
    have := hcm.total x y hxy hne
    cases hc : c.col x y with
    | none => exact absurd hc this
    | some ζ => simp⟩

/-! ### Switching two colours on all chains but one -/

/-- Exchange `θ` and `η` on every `(θ, η)`-chain except the chain of `w`. -/
noncomputable def kempeSwapCompl {k : ℕ} (c : PEC G (Fin k)) (θ η : Fin k) (w : V) :
    PEC G (Fin k) :=
  (permCol c (Equiv.swap θ η)).kempeSwap θ η w

theorem kempeSwapCompl_col_of_reachable {k : ℕ} (c : PEC G (Fin k)) (θ η : Fin k) {w x : V}
    (hx : (c.kempeGraph θ η).Reachable w x) (y : V) :
    (kempeSwapCompl c θ η w).col x y = c.col x y := by
  unfold kempeSwapCompl
  rw [← kempeGraph_permCol_swap c θ η] at hx
  rw [kempeSwap_col, kempeSwapFun_of_reachable _ θ η hx y, permCol_col, Option.map_map]
  cases c.col x y <;> simp

theorem kempeSwapCompl_col_of_not_reachable {k : ℕ} (c : PEC G (Fin k)) (θ η : Fin k)
    {w x : V} (hx : ¬ (c.kempeGraph θ η).Reachable w x) (y : V) :
    (kempeSwapCompl c θ η w).col x y = (c.col x y).map (Equiv.swap θ η) := by
  unfold kempeSwapCompl
  rw [← kempeGraph_permCol_swap c θ η] at hx
  rw [kempeSwap_col, kempeSwapFun_of_not_reachable _ θ η hx y, permCol_col]

theorem kempeSwapCompl_isFree_of_reachable {k : ℕ} (c : PEC G (Fin k)) (θ η : Fin k) {w v : V}
    (hv : (c.kempeGraph θ η).Reachable w v) (ε : Fin k) :
    (kempeSwapCompl c θ η w).IsFree v ε ↔ c.IsFree v ε := by
  unfold kempeSwapCompl
  rw [← kempeGraph_permCol_swap c θ η] at hv
  rw [isFree_kempeSwap_of_reachable _ θ η hv, isFree_permCol, Equiv.symm_swap,
    Equiv.swap_apply_self]

theorem kempeSwapCompl_isFree_of_not_reachable {k : ℕ} (c : PEC G (Fin k)) (θ η : Fin k)
    {w v : V} (hv : ¬ (c.kempeGraph θ η).Reachable w v) (ε : Fin k) :
    (kempeSwapCompl c θ η w).IsFree v ε ↔ c.IsFree v (Equiv.swap θ η ε) := by
  unfold kempeSwapCompl
  rw [← kempeGraph_permCol_swap c θ η] at hv
  rw [isFree_kempeSwap_of_not_reachable _ θ η hv, isFree_permCol, Equiv.symm_swap]

theorem IsColMinus.kempeSwapCompl {k : ℕ} {c : PEC G (Fin k)} {a b : V} (hcm : IsColMinus c a b)
    (θ η : Fin k) (w : V) : IsColMinus (kempeSwapCompl c θ η w) a b :=
  (hcm.permCol (Equiv.swap θ η)).kempeSwap θ η w

end Overfull
