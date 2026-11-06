/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Fork58

/-!
# Fork lemma: the final configuration

Cao–Chen (2020), end of §5.3. From the colouring `φ₂` of Claim 5.9 (`FinalCfg`), colour `ab` by
`α`, `bu` by `β₁` and uncolour `us₁`; after a few Kempe changes the whole graph gets coloured with
`Δ` colours, which is impossible for a class-two graph.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b u s₁ s₂ t₁ t₂ : V}

/-- A colouring of `G − xy` with a colour missing at both `x` and `y` is impossible. -/
theorem close_uncol (hG : IsClassTwo G) {d : PEC G (Fin G.maxDegree)} {x y : V}
    (hcm : IsColMinus d x y) {θ : Fin G.maxDegree} (hx : d.IsFree x θ) (hy : d.IsFree y θ) :
    False := by
  refine not_total_of_classTwo hG (d.setEdge θ hcm.adj hx hy) fun p q hpq => ?_
  by_cases h : (p = x ∧ q = y) ∨ (p = y ∧ q = x)
  · rw [setEdge_col]
    unfold updFun
    rw [if_pos h]
    exact Option.some_ne_none _
  · refine extends_setEdge d θ hcm.adj hx hy p q (hcm.total p q hpq fun he => h ?_)
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

/-- Recolour `bu` (coloured `β`, with `β` missing at `s`) by a colour missing at `b` and `u`, then
colour `us` by `β`: impossible. -/
theorem close_bu (hG : IsClassTwo G) {d : PEC G (Fin G.maxDegree)} {b u s : V}
    (hcm : IsColMinus d u s) (hbs : b ≠ s) {β θ : Fin G.maxDegree} (hbu : d.col b u = some β)
    (hs : d.IsFree s β) (hb : d.IsFree b θ) (hu : d.IsFree u θ) : False := by
  have hadj : G.Adj u b := (d.col_adj hbu).symm
  have hub : d.col u b = some β := by rw [d.col_symm]; exact hbu
  set d' := d.setEdge θ hadj hu hb
  have hus : u ≠ s := hcm.adj.ne
  have hcm' : IsColMinus d' u s :=
    ⟨hcm.adj, by
      rw [setEdge_col, updFun_of_ne _ (by tauto)]
      exact hcm.uncol,
      fun p q hpq hne => extends_setEdge d θ hadj hu hb p q (hcm.total p q hpq hne)⟩
  exact close_uncol hG hcm' (isFree_setEdge_old d θ hadj hu hb hub)
    ((isFree_setEdge_of_ne d θ hadj hu hb hus.symm hbs.symm β).2 hs)

/-- Reachability passes to a colouring that agrees on all `α`/`β`-edges of the first one. -/
theorem reachable_mono_of_agree {k : ℕ} {d d' : PEC G (Fin k)} {α β : Fin k}
    (hag : ∀ x y, (d'.col x y = some α ∨ d'.col x y = some β) → d.col x y = d'.col x y) {p q : V}
    (h : (d'.kempeGraph α β).Reachable p q) : (d.kempeGraph α β).Reachable p q := by
  refine h.mono ?_
  intro x y hxy
  exact ⟨hxy.1, by rw [hag x y hxy.2]; exact hxy.2⟩

/-- **Claim 5.10 pattern.** For a colouring of `G − us₁` with `θ` missing at `u` and `β₁` missing at
`s₁` and `t₁`, and `s₁t₁` coloured `η`: `u` reaches `t₁` by a `(θ, η)`-chain. -/
theorem reach_t₁ (hG : IsClassTwo G) {d : PEC G (Fin G.maxDegree)} {u s₁ t₁ : V}
    (hcm : IsColMinus d u s₁) (hut₁ : u ≠ t₁) {θ η β : Fin G.maxDegree}
    (hst : d.col s₁ t₁ = some η) (hβη : β ≠ η) (hβθ : β ≠ θ) (hu : d.IsFree u θ)
    (hs : d.IsFree s₁ β) (ht : d.IsFree t₁ β) : (d.kempeGraph θ η).Reachable u t₁ := by
  have hadj : G.Adj s₁ t₁ := d.col_adj hst
  set d' := d.setEdge β hadj hs ht
  have hus : u ≠ s₁ := hcm.adj.ne
  have hcm' : IsColMinus d' u s₁ :=
    ⟨hcm.adj, by
      rw [setEdge_col, updFun_of_ne _ (by have := hadj.ne; tauto)]
      exact hcm.uncol,
      fun p q hpq hne => extends_setEdge d β hadj hs ht p q (hcm.total p q hpq hne)⟩
  have hu' : d'.IsFree u θ := (isFree_setEdge_of_ne d β hadj hs ht hus hut₁ θ).2 hu
  have hs' : d'.IsFree s₁ η := isFree_setEdge_old d β hadj hs ht hst
  have hl := (hcm'.ab_facts hG).2 θ η hu' hs'
  have hl' : (d.kempeGraph θ η).Reachable u s₁ := reachable_mono_of_agree (fun x y hxy => by
    by_cases hp : (x = s₁ ∧ y = t₁) ∨ (x = t₁ ∧ y = s₁)
    · exfalso
      rw [setEdge_col] at hxy
      unfold updFun at hxy
      rw [if_pos hp] at hxy
      rcases hxy with h | h <;> simp only [Option.some.injEq] at h
      · exact hβθ h
      · exact hβη h
    · rw [setEdge_col, updFun_of_ne _ hp]) hl
  exact reachable_of_col hl' (Or.inr hst)

/-- The colouring `φ₂` of Claim 5.9. -/
structure FinalCfg {k : ℕ} (c : PEC G (Fin k)) (a b u s₁ s₂ t₁ t₂ : V) (α β₁ β₂ γ₂ : Fin k) :
    Prop where
  cm : IsColMinus c a b
  cbu : c.col b u = some α
  cus₁ : c.col u s₁ = some β₁
  cus₂ : c.col u s₂ = some β₂
  cst₁ : c.col s₁ t₁ = some β₂
  cst₂ : c.col s₂ t₂ = some γ₂
  αa : c.IsFree a α
  β₁b : c.IsFree b β₁
  β₂A : InA c a b β₂
  γ₂A : InA c a b γ₂
  t₁α : c.IsFree t₁ α
  t₁β₁ : c.IsFree t₁ β₁
  t₁γ₂ : c.IsFree t₁ γ₂
  t₂α : c.IsFree t₂ α
  t₂β₁ : c.IsFree t₂ β₁
  t₂β₂ : c.IsFree t₂ β₂

set_option maxHeartbeats 1600000 in
/-- Moving the uncoloured edge: `ab := α`, `bu := β₁`, `us₁` uncoloured. -/
theorem FinalCfg.exists_psi {k : ℕ} {c : PEC G (Fin k)} {α β₁ β₂ γ₂ : Fin k}
    (hd : Distinct7 a b u s₁ s₂ t₁ t₂) (h : FinalCfg c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₂)
    (hαβ₁ : α ≠ β₁) :
    ∃ ψ : PEC G (Fin k), IsColMinus ψ u s₁ ∧ ψ.col a b = some α ∧ ψ.col b u = some β₁ ∧
      ψ.col u s₂ = some β₂ ∧ ψ.col s₁ t₁ = some β₂ ∧ ψ.col s₂ t₂ = some γ₂ ∧
      ψ.IsFree u α ∧ ψ.IsFree s₁ β₁ ∧ (∀ ε, ψ.IsFree t₁ ε ↔ c.IsFree t₁ ε) ∧
      (∀ ε, ψ.IsFree t₂ ε ↔ c.IsFree t₂ ε) ∧
      (∀ ε, ε ≠ α → ε ≠ β₁ → ((ψ.IsFree a ε ↔ c.IsFree a ε) ∧ (ψ.IsFree b ε ↔ c.IsFree b ε))) := by
  have hbu : b ≠ u := hd.bu
  have hus₁ : u ≠ s₁ := hd.us₁
  have hc1bu : (unsetEdge c u s₁).col b u = some α := by
    rw [unsetEdge_col_of_ne c (by have := hd.bs₁; tauto)]; exact h.cbu
  have ha2 : (unsetEdge (unsetEdge c u s₁) b u).IsFree a α :=
    (isFree_unsetEdge_of_ne _ hd.ab hd.au α).2 ((isFree_unsetEdge_of_ne c hd.au hd.as₁ α).2 h.αa)
  have hb2 : (unsetEdge (unsetEdge c u s₁) b u).IsFree b α :=
    (isFree_unsetEdge_left _ hbu hc1bu α).2 (Or.inl rfl)
  set c3 := (unsetEdge (unsetEdge c u s₁) b u).setEdge α h.cm.adj ha2 hb2
  have hb3 : c3.IsFree b β₁ := by
    intro w hw
    rw [setEdge_col] at hw
    unfold updFun at hw
    split_ifs at hw with hp
    · exact hαβ₁ (Option.some_injective _ hw)
    · have hb2' : (unsetEdge (unsetEdge c u s₁) b u).IsFree b β₁ :=
        (isFree_unsetEdge_left _ hbu hc1bu β₁).2
          (Or.inr ((isFree_unsetEdge_of_ne c hbu hd.bs₁ β₁).2 h.β₁b))
      exact hb2' w hw
  have hu3 : c3.IsFree u β₁ := by
    intro w hw
    rw [setEdge_col_of_ne_left _ α h.cm.adj ha2 hb2 hd.au.symm hbu.symm] at hw
    have hu1 : (unsetEdge c u s₁).IsFree u β₁ := (isFree_unsetEdge_left c hus₁ h.cus₁ β₁).2
      (Or.inl rfl)
    exact ((isFree_unsetEdge_right _ hbu hc1bu β₁).2 (Or.inr hu1)) w hw
  set ψ := c3.setEdge β₁ (c.col_adj h.cbu) hb3 hu3
  have hcol : ∀ x y, ψ.col x y = if (x = b ∧ y = u) ∨ (x = u ∧ y = b) then some β₁ else
      if (x = a ∧ y = b) ∨ (x = b ∧ y = a) then some α else
      if (x = b ∧ y = u) ∨ (x = u ∧ y = b) then none else
      if (x = u ∧ y = s₁) ∨ (x = s₁ ∧ y = u) then none else c.col x y := fun x y => rfl
  have hoff : ∀ x y, ¬ ((x = b ∧ y = u) ∨ (x = u ∧ y = b)) → ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) →
      ¬ ((x = u ∧ y = s₁) ∨ (x = s₁ ∧ y = u)) → ψ.col x y = c.col x y := by
    intro x y h1 h2 h3
    rw [hcol, if_neg h1, if_neg h2, if_neg h1, if_neg h3]
  have hd' := hd
  obtain ⟨ab, au, as₁, as₂, at₁, at₂, bu, bs₁, bs₂, bt₁, bt₂, us₁, us₂, ut₁, ut₂, s₁s₂, s₁t₁,
    s₁t₂, s₂t₁, s₂t₂, t₁t₂⟩ := hd'
  -- vertices other than `a, b, u, s₁` keep all their edges
  have hfar : ∀ w, w ≠ a → w ≠ b → w ≠ u → w ≠ s₁ → ∀ ε, ψ.IsFree w ε ↔ c.IsFree w ε := by
    intro w h1 h2 h3 h4 ε
    constructor <;> intro hw x hx
    · exact hw x (by rw [hoff w x (by tauto) (by tauto) (by tauto)]; exact hx)
    · rw [hoff w x (by tauto) (by tauto) (by tauto)] at hx
      exact hw x hx
  refine ⟨ψ, ⟨c.col_adj h.cus₁, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hfar t₁ at₁.symm bt₁.symm ut₁.symm s₁t₁.symm, hfar t₂ at₂.symm bt₂.symm ut₂.symm s₁t₂.symm, ?_⟩
  · rw [hcol, if_neg (by tauto), if_neg (by tauto), if_neg (by tauto), if_pos (Or.inl ⟨rfl, rfl⟩)]
  · intro x y hxy hne
    rw [hcol]
    split_ifs with h1 h2 h3
    · exact Option.some_ne_none _
    · exact Option.some_ne_none _
    · exact absurd (by rcases h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Sym2.eq_swap]) hne
    · refine h.cm.total x y hxy fun he => h2 ?_
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
  · rw [hcol, if_neg (by tauto), if_pos (Or.inl ⟨rfl, rfl⟩)]
  · rw [hcol, if_pos (Or.inl ⟨rfl, rfl⟩)]
  · rw [hoff u s₂ (by tauto) (by tauto) (by tauto)]; exact h.cus₂
  · rw [hoff s₁ t₁ (by tauto) (by tauto) (by tauto)]; exact h.cst₁
  · rw [hoff s₂ t₂ (by tauto) (by tauto) (by tauto)]; exact h.cst₂
  · intro w hw
    by_cases hwb : w = b
    · subst hwb
      rw [hcol, if_pos (Or.inr ⟨rfl, rfl⟩)] at hw
      exact hαβ₁ (Option.some_injective _ hw).symm
    by_cases hws : w = s₁
    · subst hws
      rw [hcol, if_neg (by tauto), if_neg (by tauto), if_neg (by tauto),
        if_pos (Or.inl ⟨rfl, rfl⟩)] at hw
      cases hw
    rw [hoff u w (by tauto) (by tauto) (by tauto)] at hw
    have hub : c.col u b = some α := by rw [c.col_symm]; exact h.cbu
    exact hwb (c.col_proper hw hub)
  · intro w hw
    by_cases hwu : w = u
    · subst hwu
      rw [hcol, if_neg (by tauto), if_neg (by tauto), if_neg (by tauto),
        if_pos (Or.inr ⟨rfl, rfl⟩)] at hw
      cases hw
    rw [hoff s₁ w (by tauto) (by tauto) (by tauto)] at hw
    have hsu : c.col s₁ u = some β₁ := by rw [c.col_symm]; exact h.cus₁
    exact hwu (c.col_proper hw hsu)
  · intro ε hεα hεβ₁
    constructor
    · constructor <;> intro hw x hx
      · by_cases hxb : x = b
        · subst hxb; rw [h.cm.uncol] at hx; cases hx
        · exact hw x (by rw [hoff a x (by tauto) (by tauto) (by tauto)]; exact hx)
      · by_cases hxb : x = b
        · subst hxb
          rw [hcol, if_neg (by tauto), if_pos (Or.inl ⟨rfl, rfl⟩)] at hx
          exact hεα (Option.some_injective _ hx).symm
        · rw [hoff a x (by tauto) (by tauto) (by tauto)] at hx
          exact hw x hx
    · constructor <;> intro hw x hx
      · by_cases hxu : x = u
        · subst hxu; rw [h.cbu] at hx; exact hεα (Option.some_injective _ hx).symm
        by_cases hxa : x = a
        · subst hxa; rw [c.col_symm, h.cm.uncol] at hx; cases hx
        exact hw x (by rw [hoff b x (by tauto) (by tauto) (by tauto)]; exact hx)
      · by_cases hxu : x = u
        · subst hxu
          rw [hcol, if_pos (Or.inl ⟨rfl, rfl⟩)] at hx
          exact hεβ₁ (Option.some_injective _ hx).symm
        by_cases hxa : x = a
        · subst hxa
          rw [hcol, if_neg (by tauto), if_pos (Or.inr ⟨rfl, rfl⟩)] at hx
          exact hεα (Option.some_injective _ hx).symm
        rw [hoff b x (by tauto) (by tauto) (by tauto)] at hx
        exact hw x hx

end Overfull
