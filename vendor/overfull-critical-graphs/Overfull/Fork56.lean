/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Fork56b

/-!
# Fork lemma, Claim 5.6

If no rainbow fork exists, then no fork exists (Cao–Chen 2020, Claim 5.6). The four cases are
proved in the order 1, 2, 3, 4, using the `1 ↔ 2` symmetry.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b u s₁ s₂ t₁ t₂ : V}

theorem Rainbow.swap {k : ℕ} {α β₁ β₂ γ₁ γ₂ : Fin k} (r : Rainbow α β₁ β₂ γ₁ γ₂) :
    Rainbow α β₂ β₁ γ₂ γ₁ :=
  ⟨r.2.2.1, r.2.2.2, r.1, r.2.1⟩

/-- No rainbow fork on `a b u s₁ s₂ t₁ t₂`. -/
def NoRainbow (G : SimpleGraph V) [DecidableRel G.Adj] (a b u s₁ s₂ t₁ t₂ : V) : Prop :=
  ∀ (c : PEC G (Fin G.maxDegree)) (α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree),
    IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂ → Rainbow α β₁ β₂ γ₁ γ₂ → False

theorem NoRainbow.swap (hR : NoRainbow G a b u s₁ s₂ t₁ t₂) : NoRainbow G a b u s₂ s₁ t₂ t₁ :=
  fun c _ _ _ _ _ h r => hR c _ _ _ _ _ h.swap r.swap

variable (hG : IsClassTwo G)
include hG

theorem fork_case1 (hd : Distinct7 a b u s₁ s₂ t₁ t₂) (hH : ForkHyp G a b t₁ t₂)
    (hR : NoRainbow G a b u s₁ s₂ t₁ t₂) {c : PEC G (Fin G.maxDegree)}
    {α β₁ β₂ γ₂ : Fin G.maxDegree} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ α γ₂)
    (hγ₂β₁ : γ₂ ≠ β₁) : False :=
  case13 hG hd hH (fun c' _ h' hα _ hβ₂ => hR c' _ _ _ _ _ h' ⟨hα, hβ₂, h.γ₁γ₂.symm, hγ₂β₁⟩) h

theorem fork_case2 (hd : Distinct7 a b u s₁ s₂ t₁ t₂) (hH : ForkHyp G a b t₁ t₂)
    (hR : NoRainbow G a b u s₁ s₂ t₁ t₂) {c : PEC G (Fin G.maxDegree)}
    {α β₁ β₂ γ₂ : Fin G.maxDegree} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ β₂ γ₂)
    (hγ₂α : γ₂ ≠ α) (hγ₂β₁ : γ₂ ≠ β₁) : False :=
  case24 hG hd hH (fun c' _ h' hα _ hβ₂ => hR c' _ _ _ _ _ h' ⟨hα, hβ₂, hγ₂α, hγ₂β₁⟩)
    (fun _ h' => fork_case1 hG hd hH hR h' hγ₂β₁) (fun e => absurd e hγ₂β₁) h hγ₂α

theorem fork_case3 (hd : Distinct7 a b u s₁ s₂ t₁ t₂) (hH : ForkHyp G a b t₁ t₂)
    (hR : NoRainbow G a b u s₁ s₂ t₁ t₂) {c : PEC G (Fin G.maxDegree)}
    {α β₁ β₂ : Fin G.maxDegree} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ α β₁) : False :=
  case13 hG hd hH
    (fun _ _ h' hα _ hβ₂ => fork_case2 hG hd.swap hH.swap hR.swap h'.swap hα hβ₂) h

theorem fork_case4 (hd : Distinct7 a b u s₁ s₂ t₁ t₂) (hH : ForkHyp G a b t₁ t₂)
    (hR : NoRainbow G a b u s₁ s₂ t₁ t₂) {c : PEC G (Fin G.maxDegree)}
    {α β₁ β₂ : Fin G.maxDegree} (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ β₂ β₁) : False :=
  case24 hG hd hH
    (fun _ _ h' hα _ hβ₂ => fork_case2 hG hd.swap hH.swap hR.swap h'.swap hα hβ₂)
    (fun _ h' => fork_case3 hG hd hH hR h')
    (fun _ _ _ h' hα hβ₁ _ => fork_case2 hG hd hH hR h' hα hβ₁) h (h.αβ₁ hd).symm

/-- **Claim 5.6.** If there is no rainbow fork, there is no fork. -/
theorem claim56 (hd : Distinct7 a b u s₁ s₂ t₁ t₂) (hH : ForkHyp G a b t₁ t₂)
    (hR : NoRainbow G a b u s₁ s₂ t₁ t₂) (c : PEC G (Fin G.maxDegree))
    (α β₁ β₂ γ₁ γ₂ : Fin G.maxDegree) (h : IsFork c a b u s₁ s₂ t₁ t₂ α β₁ β₂ γ₁ γ₂) : False := by
  by_cases h1 : γ₁ = α
  · subst h1
    by_cases h2 : γ₂ = β₁
    · subst h2
      exact fork_case3 hG hd hH hR h
    · exact fork_case1 hG hd hH hR h h2
  by_cases h2 : γ₁ = β₂
  · subst h2
    by_cases h3 : γ₂ = β₁
    · subst h3
      exact fork_case4 hG hd hH hR h
    by_cases h4 : γ₂ = α
    · subst h4
      exact fork_case3 hG hd.swap hH.swap hR.swap h.swap
    · exact fork_case2 hG hd hH hR h h4 h3
  by_cases h3 : γ₂ = α
  · subst h3
    exact fork_case1 hG hd.swap hH.swap hR.swap h.swap h2
  by_cases h4 : γ₂ = β₁
  · subst h4
    exact fork_case2 hG hd.swap hH.swap hR.swap h.swap h1 h2
  exact hR c _ _ _ _ _ h ⟨h1, h2, h3, h4⟩

end Overfull
