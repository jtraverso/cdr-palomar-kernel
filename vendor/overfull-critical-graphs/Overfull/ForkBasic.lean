/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.KempeTools

/-!
# Forks

A fork (Cao–Chen 2020, Definition 1; CCJS §2) on `a b u s₁ s₂ t₁ t₂` for a colouring `φ` of
`G − ab`: `φ(bu) = α ∈ φ̄(a)`, `φ(usᵢ) = βᵢ ∈ A`, `φ(sᵢtᵢ) = γᵢ ∈ A ∩ φ̄(t_{3−i})`, where
`A = φ̄(a) ∪ φ̄(b)`. This file sets up the definitions, the `1 ↔ 2` symmetry and the two kinds of
Kempe swaps that keep a fork.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Seven distinct vertices. -/
structure Distinct7 (a b u s₁ s₂ t₁ t₂ : V) : Prop where
  ab : a ≠ b
  au : a ≠ u
  as₁ : a ≠ s₁
  as₂ : a ≠ s₂
  at₁ : a ≠ t₁
  at₂ : a ≠ t₂
  bu : b ≠ u
  bs₁ : b ≠ s₁
  bs₂ : b ≠ s₂
  bt₁ : b ≠ t₁
  bt₂ : b ≠ t₂
  us₁ : u ≠ s₁
  us₂ : u ≠ s₂
  ut₁ : u ≠ t₁
  ut₂ : u ≠ t₂
  s₁s₂ : s₁ ≠ s₂
  s₁t₁ : s₁ ≠ t₁
  s₁t₂ : s₁ ≠ t₂
  s₂t₁ : s₂ ≠ t₁
  s₂t₂ : s₂ ≠ t₂
  t₁t₂ : t₁ ≠ t₂

theorem Distinct7.swap {a b u s₁ s₂ t₁ t₂ : V} (h : Distinct7 a b u s₁ s₂ t₁ t₂) :
    Distinct7 a b u s₂ s₁ t₂ t₁ :=
  ⟨h.ab, h.au, h.as₂, h.as₁, h.at₂, h.at₁, h.bu, h.bs₂, h.bs₁, h.bt₂, h.bt₁, h.us₂, h.us₁, h.ut₂,
    h.ut₁, h.s₁s₂.symm, h.s₂t₂, h.s₂t₁, h.s₁t₂, h.s₁t₁, h.t₁t₂.symm⟩

/-- A fork with colours `α = φ(bu)`, `βᵢ = φ(usᵢ)`, `γᵢ = φ(sᵢtᵢ)`. -/
structure IsFork {k : ℕ} (c : PEC G (Fin k)) (a b u s₁ s₂ t₁ t₂ : V)
    (α β₁ β₂ γ₁ γ₂ : Fin k) : Prop where
  cm : IsColMinus c a b
  cbu : c.col b u = some α
  cus₁ : c.col u s₁ = some β₁
  cus₂ : c.col u s₂ = some β₂
  cst₁ : c.col s₁ t₁ = some γ₁
  cst₂ : c.col s₂ t₂ = some γ₂
  αa : c.IsFree a α
  β₁A : InA c a b β₁
  β₂A : InA c a b β₂
  γ₁A : InA c a b γ₁
  γ₂A : InA c a b γ₂
  γ₁t₂ : c.IsFree t₂ γ₁
  γ₂t₁ : c.IsFree t₁ γ₂

/-- Rainbow fork: the five colours are distinct (the other inequalities are automatic). -/
def Rainbow {k : ℕ} (α β₁ β₂ γ₁ γ₂ : Fin k) : Prop :=
  γ₁ ≠ α ∧ γ₁ ≠ β₂ ∧ γ₂ ≠ α ∧ γ₂ ≠ β₁

/-- The hypothesis of the fork lemma, in the form used by the proof: for every colouring of
`G − ab`, `A ∩ φ̄(t₁) ∩ φ̄(t₂)` has at least three colours and each `A ∩ φ̄(tᵢ)` at least five. -/
def ForkHyp (G : SimpleGraph V) [DecidableRel G.Adj] (a b t₁ t₂ : V) : Prop :=
  ∀ c : PEC G (Fin G.maxDegree), IsColMinus c a b →
    (∀ x y, ∃ θ, θ ≠ x ∧ θ ≠ y ∧ InA c a b θ ∧ c.IsFree t₁ θ ∧ c.IsFree t₂ θ) ∧
    (∀ x y z w, ∃ θ, θ ≠ x ∧ θ ≠ y ∧ θ ≠ z ∧ θ ≠ w ∧ InA c a b θ ∧ c.IsFree t₁ θ) ∧
    (∀ x y z w, ∃ θ, θ ≠ x ∧ θ ≠ y ∧ θ ≠ z ∧ θ ≠ w ∧ InA c a b θ ∧ c.IsFree t₂ θ)

theorem ForkHyp.swap {a b t₁ t₂ : V} (h : ForkHyp G a b t₁ t₂) : ForkHyp G a b t₂ t₁ := by
  intro c hcm
  obtain ⟨h1, h2, h3⟩ := h c hcm
  refine ⟨fun x y => ?_, h3, h2⟩
  obtain ⟨θ, hx, hy, hA, h₁, h₂⟩ := h1 x y
  exact ⟨θ, hx, hy, hA, h₂, h₁⟩

namespace IsFork

variable {k : ℕ} {c : PEC G (Fin k)} {a b u s₁ s₂ t₁ t₂ : V} {α β₁ β₂ γ₁ γ₂ : Fin k}

theorem swap (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) :
    IsFork c a b u s₂ s₁ t₂ t₁ α β₂ β₁ γ₂ γ₁ :=
  ⟨h.cm, h.cbu, h.cus₂, h.cus₁, h.cst₂, h.cst₁, h.αa, h.β₂A, h.β₁A, h.γ₂A, h.γ₁A, h.γ₂t₁, h.γ₁t₂⟩

theorem cub (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : c.col u b = some α := by
  rw [c.col_symm]; exact h.cbu

theorem cs₁u (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : c.col s₁ u = some β₁ := by
  rw [c.col_symm]; exact h.cus₁

theorem cs₂u (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : c.col s₂ u = some β₂ := by
  rw [c.col_symm]; exact h.cus₂

theorem ct₁s (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : c.col t₁ s₁ = some γ₁ := by
  rw [c.col_symm]; exact h.cst₁

theorem ct₂s (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : c.col t₂ s₂ = some γ₂ := by
  rw [c.col_symm]; exact h.cst₂

variable (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
include hd

theorem αβ₁ (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : α ≠ β₁ := by
  rintro rfl
  exact hd.bs₁ (c.col_proper h.cub h.cus₁)

theorem αβ₂ (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : α ≠ β₂ := by
  rintro rfl
  exact hd.bs₂ (c.col_proper h.cub h.cus₂)

theorem β₁β₂ (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : β₁ ≠ β₂ := by
  rintro rfl
  exact hd.s₁s₂ (c.col_proper h.cus₁ h.cus₂)

theorem β₁γ₁ (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : β₁ ≠ γ₁ := by
  rintro rfl
  exact hd.ut₁ (c.col_proper h.cs₁u h.cst₁)

theorem β₂γ₂ (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : β₂ ≠ γ₂ := by
  rintro rfl
  exact hd.ut₂ (c.col_proper h.cs₂u h.cst₂)

end IsFork

theorem IsFork.γ₁γ₂ {k : ℕ} {c : PEC G (Fin k)} {a b u s₁ s₂ t₁ t₂ : V}
    {α β₁ β₂ γ₁ γ₂ : Fin k} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : γ₁ ≠ γ₂ := by
  rintro rfl
  exact h.γ₁t₂ s₂ h.ct₂s

theorem IsFork.not_free_t₁ {k : ℕ} {c : PEC G (Fin k)} {a b u s₁ s₂ t₁ t₂ : V}
    {α β₁ β₂ γ₁ γ₂ : Fin k} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : ¬ c.IsFree t₁ γ₁ :=
  fun ht => ht s₁ h.ct₁s

theorem IsFork.not_free_t₂ {k : ℕ} {c : PEC G (Fin k)} {a b u s₁ s₂ t₁ t₂ : V}
    {α β₁ β₂ γ₁ γ₂ : Fin k} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : ¬ c.IsFree t₂ γ₂ :=
  fun ht => ht s₂ h.ct₂s

/-! ### Edge colours under swaps -/

theorem kcol_keep {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w x y : V} {ε : Fin k}
    (hxy : c.col x y = some ε) (h : (ε ≠ θ ∧ ε ≠ η) ∨ ¬ (c.kempeGraph θ η).Reachable w x) :
    (c.kempeSwap θ η w).col x y = some ε := by
  rcases h with ⟨h1, h2⟩ | h
  · exact kempeSwap_col_of_ne c θ η w x y hxy h1 h2
  · rw [kempeSwap_col, kempeSwapFun_of_not_reachable c θ η h y, hxy]

theorem kcol_flip₁ {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w x y : V}
    (hxy : c.col x y = some θ) (h : (c.kempeGraph θ η).Reachable w x) :
    (c.kempeSwap θ η w).col x y = some η := by
  rw [kempeSwap_col, kempeSwapFun_of_reachable c θ η h y, hxy]
  simp

theorem kcol_flip₂ {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w x y : V}
    (hxy : c.col x y = some η) (h : (c.kempeGraph θ η).Reachable w x) :
    (c.kempeSwap θ η w).col x y = some θ := by
  rw [kempeSwap_col, kempeSwapFun_of_reachable c θ η h y, hxy]
  simp

theorem ccol_keep {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w x y : V} {ε : Fin k}
    (hxy : c.col x y = some ε) (h : (ε ≠ θ ∧ ε ≠ η) ∨ (c.kempeGraph θ η).Reachable w x) :
    (kempeSwapCompl c θ η w).col x y = some ε := by
  by_cases hr : (c.kempeGraph θ η).Reachable w x
  · rw [kempeSwapCompl_col_of_reachable c θ η hr, hxy]
  · rcases h with ⟨h1, h2⟩ | h
    · rw [kempeSwapCompl_col_of_not_reachable c θ η hr, hxy]
      simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · exact absurd h hr

theorem ccol_flip₁ {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w x y : V}
    (hxy : c.col x y = some θ) (h : ¬ (c.kempeGraph θ η).Reachable w x) :
    (kempeSwapCompl c θ η w).col x y = some η := by
  rw [kempeSwapCompl_col_of_not_reachable c θ η h, hxy]
  simp

theorem ccol_flip₂ {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w x y : V}
    (hxy : c.col x y = some η) (h : ¬ (c.kempeGraph θ η).Reachable w x) :
    (kempeSwapCompl c θ η w).col x y = some θ := by
  rw [kempeSwapCompl_col_of_not_reachable c θ η h, hxy]
  simp

/-- Off the kept chain, after the complementary switch, `w` misses `ε` iff it missed the swapped
colour. Specialised forms. -/
theorem cfree_of_ne {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w v : V} {ε : Fin k}
    (h1 : ε ≠ θ) (h2 : ε ≠ η) : (kempeSwapCompl c θ η w).IsFree v ε ↔ c.IsFree v ε := by
  by_cases hr : (c.kempeGraph θ η).Reachable w v
  · exact kempeSwapCompl_isFree_of_reachable c θ η hr ε
  · rw [kempeSwapCompl_isFree_of_not_reachable c θ η hr, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem cfree_flip₁ {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w v : V}
    (h : ¬ (c.kempeGraph θ η).Reachable w v) :
    (kempeSwapCompl c θ η w).IsFree v η ↔ c.IsFree v θ := by
  rw [kempeSwapCompl_isFree_of_not_reachable c θ η h, Equiv.swap_apply_right]

theorem cfree_flip₂ {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w v : V}
    (h : ¬ (c.kempeGraph θ η).Reachable w v) :
    (kempeSwapCompl c θ η w).IsFree v θ ↔ c.IsFree v η := by
  rw [kempeSwapCompl_isFree_of_not_reachable c θ η h, Equiv.swap_apply_left]

theorem kfree_of_ne {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w v : V} {ε : Fin k}
    (h1 : ε ≠ θ) (h2 : ε ≠ η) : (c.kempeSwap θ η w).IsFree v ε ↔ c.IsFree v ε :=
  kempeSwap_isFree_of_ne c θ η w v h1 h2

theorem kfree_flip₁ {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w v : V}
    (h : (c.kempeGraph θ η).Reachable w v) :
    (c.kempeSwap θ η w).IsFree v η ↔ c.IsFree v θ := by
  rw [isFree_kempeSwap_of_reachable c θ η h, Equiv.swap_apply_right]

theorem kfree_flip₂ {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w v : V}
    (h : (c.kempeGraph θ η).Reachable w v) :
    (c.kempeSwap θ η w).IsFree v θ ↔ c.IsFree v η := by
  rw [isFree_kempeSwap_of_reachable c θ η h, Equiv.swap_apply_left]

theorem kfree_off {k : ℕ} (c : PEC G (Fin k)) {θ η : Fin k} {w v : V}
    (h : ¬ (c.kempeGraph θ η).Reachable w v) (ε : Fin k) :
    (c.kempeSwap θ η w).IsFree v ε ↔ c.IsFree v ε :=
  isFree_kempeSwap_of_not_reachable c θ η h ε

/-! ### Swapping the `a`–`b` chain -/

section AB

variable (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)} {a b : V} (hcm : IsColMinus c a b)
  {θ η : Fin G.maxDegree} (hθ : c.IsFree a θ) (hη : c.IsFree b η)
include hG hcm hθ hη

theorem ksAB_link : (c.kempeGraph θ η).Reachable a b := (hcm.ab_facts hG).2 θ η hθ hη

theorem ksAB_free_b : (c.kempeSwap θ η a).IsFree b θ := by
  rw [kfree_flip₂ c (ksAB_link hG hcm hθ hη)]; exact hη

theorem ksAB_free_a : (c.kempeSwap θ η a).IsFree a η := by
  rw [kfree_flip₁ c (Reachable.refl a)]; exact hθ

theorem ksAB_free_other {w : V} (hwa : w ≠ a) (hwb : w ≠ b) (ε : Fin G.maxDegree) :
    (c.kempeSwap θ η a).IsFree w ε ↔ c.IsFree w ε :=
  isFree_kempeSwap_of_linked c (ksAB_link hG hcm hθ hη) (Or.inl hθ) (Or.inr hη) hwa hwb
    hcm.adj.ne ε

theorem ksAB_inA (ε : Fin G.maxDegree) : InA (c.kempeSwap θ η a) a b ε ↔ InA c a b ε := by
  unfold InA
  have hl := ksAB_link hG hcm hθ hη
  rw [isFree_kempeSwap_of_reachable c θ η (Reachable.refl a),
    isFree_kempeSwap_of_reachable c θ η hl]
  by_cases h1 : ε = θ
  · subst h1
    rw [Equiv.swap_apply_left]
    exact ⟨fun _ => Or.inl hθ, fun _ => Or.inr hη⟩
  by_cases h2 : ε = η
  · subst h2
    rw [Equiv.swap_apply_right]
    exact ⟨fun _ => Or.inr hη, fun _ => Or.inl hθ⟩
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem ksAB_free_a_of_ne {ε : Fin G.maxDegree} (h1 : ε ≠ θ) (h2 : ε ≠ η) :
    (c.kempeSwap θ η a).IsFree a ε ↔ c.IsFree a ε := kfree_of_ne c h1 h2

/-- A vertex `w ∉ {a, b}` missing `θ` or `η` is not on the `a`–`b` chain, nor is anything on its
chain. -/
theorem ksAB_not_reach {w x : V} (hw : c.IsFree w θ ∨ c.IsFree w η) (hwa : w ≠ a) (hwb : w ≠ b)
    (hx : (c.kempeGraph θ η).Reachable w x) : ¬ (c.kempeGraph θ η).Reachable a x := fun r =>
  not_three_linked c hcm.adj.ne hwa.symm hwb.symm (Or.inl hθ) (Or.inr hη) hw
    (ksAB_link hG hcm hθ hη) (r.trans hx.symm)

end AB

/-- A delta-colour: in `A ∩ φ̄(t₁) ∩ φ̄(t₂)` and different from `α, β₁, β₂`. -/
def IsDelta {k : ℕ} (c : PEC G (Fin k)) (a b t₁ t₂ : V) (α β₁ β₂ δ : Fin k) : Prop :=
  InA c a b δ ∧ c.IsFree t₁ δ ∧ c.IsFree t₂ δ ∧ δ ≠ α ∧ δ ≠ β₁ ∧ δ ≠ β₂

/-- Swapping an `F`-avoiding `a`–`b` chain keeps the fork with the same colours. -/
theorem IsFork.of_swapAB (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)}
    {a b u s₁ s₂ t₁ t₂ : V} (hd : Distinct7 a b u s₁ s₂ t₁ t₂)
    {α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂)
    {θ η : Fin G.maxDegree} (hθ : c.IsFree a θ) (hη : c.IsFree b η) (hαθ : α ≠ θ)
    (hbu : (c.kempeSwap θ η a).col b u = some α) (hus₁ : (c.kempeSwap θ η a).col u s₁ = some β₁)
    (hus₂ : (c.kempeSwap θ η a).col u s₂ = some β₂)
    (hst₁ : (c.kempeSwap θ η a).col s₁ t₁ = some γ₁)
    (hst₂ : (c.kempeSwap θ η a).col s₂ t₂ = some γ₂) :
    IsFork (c.kempeSwap θ η a) a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ := by
  have hαη : α ≠ η := fun e => (h.cm.ab_facts hG).1 α h.αa (e ▸ hη)
  exact ⟨h.cm.kempeSwap θ η a, hbu, hus₁, hus₂, hst₁, hst₂,
    (ksAB_free_a_of_ne hG h.cm hθ hη hαθ hαη).2 h.αa, (ksAB_inA hG h.cm hθ hη β₁).2 h.β₁A,
    (ksAB_inA hG h.cm hθ hη β₂).2 h.β₂A, (ksAB_inA hG h.cm hθ hη γ₁).2 h.γ₁A,
    (ksAB_inA hG h.cm hθ hη γ₂).2 h.γ₂A,
    (ksAB_free_other hG h.cm hθ hη hd.at₂.symm hd.bt₂.symm γ₁).2 h.γ₁t₂,
    (ksAB_free_other hG h.cm hθ hη hd.at₁.symm hd.bt₁.symm γ₂).2 h.γ₂t₁⟩

/-- The delta property survives swapping an `a`–`b` chain. -/
theorem IsDelta.of_swapAB (hG : IsClassTwo G) {c : PEC G (Fin G.maxDegree)}
    {a b t₁ t₂ : V} (hcm : IsColMinus c a b) (hat₁ : a ≠ t₁) (hat₂ : a ≠ t₂) (hbt₁ : b ≠ t₁)
    (hbt₂ : b ≠ t₂) {α β₁ β₂ δ : Fin G.maxDegree} (hδ : IsDelta c a b t₁ t₂ α β₁ β₂ δ)
    {θ η : Fin G.maxDegree} (hθ : c.IsFree a θ) (hη : c.IsFree b η) :
    IsDelta (c.kempeSwap θ η a) a b t₁ t₂ α β₁ β₂ δ := by
  obtain ⟨hA, h₁, h₂, h3, h4, h5⟩ := hδ
  exact ⟨(ksAB_inA hG hcm hθ hη δ).2 hA,
    (ksAB_free_other hG hcm hθ hη hat₁.symm hbt₁.symm δ).2 h₁,
    (ksAB_free_other hG hcm hθ hη hat₂.symm hbt₂.symm δ).2 h₂, h3, h4, h5⟩

end Overfull
