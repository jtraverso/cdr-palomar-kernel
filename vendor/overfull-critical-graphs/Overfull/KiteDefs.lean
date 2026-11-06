/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.Counting

/-!
# Statements of the kite lemmas

* `KiteProp G` — CCJS Lemma 2.8, in the form used by Theorem 1.2: there is no kite
  `a b c u s₁ s₂ t₁ t₂` (4-cycle `a b u c`, pendant paths `u s₁ t₁`, `u s₂ t₂`) such that
  `a b u s₁ t₁` and `b a c u s₂ t₂` are Kierstead paths for `ab` and `φ(s₁t₁) = φ(s₂t₂)`, when
  `d(b) = Δ` and, robustly (in every colouring of `G − ab`), at least seven colours missing at `a`
  are missing at both `t₁` and `t₂` (`Robust`).
* `ShortKiteProp G` — CCJS Lemma 2.7 (Cao–Chen–Shan): for a short kite `a b c u x y` such that
  `a b u x` and `b a c u y` are Kierstead paths and both `x` and `y` miss a colour of `A`,
  `max{d(x), d(y)} = Δ`.

All edges of the paths beyond the first two are required to have colours in `A`, the form used in
the proof of CCJS Theorem 1.2.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A robust supply of colours of `φ̄(a)` missing at both `t₁` and `t₂`: in every colouring of
`G − ab`, any six colours can be avoided. -/
def Robust (G : SimpleGraph V) [DecidableRel G.Adj] (a b t₁ t₂ : V) : Prop :=
  ∀ ψ : PEC G (Fin G.maxDegree), IsColMinus ψ a b → ∀ S : Finset (Fin G.maxDegree), #S ≤ 6 →
    ∃ θ, θ ∉ S ∧ ψ.IsFree a θ ∧ ψ.IsFree t₁ θ ∧ ψ.IsFree t₂ θ

/-- CCJS Lemma 2.8 (kites), in the form used by Theorem 1.2. -/
def KiteProp (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (c : PEC G (Fin G.maxDegree)) (a b cc u s₁ s₂ t₁ t₂ : V),
    [a, b, cc, u, s₁, s₂, t₁, t₂].Nodup → IsColMinus c a b →
    (∃ δ, c.col b u = some δ ∧ c.IsFree a δ) → Good c a b u s₁ → Good c a b s₁ t₁ →
    (∃ β, c.col a cc = some β ∧ c.IsFree b β) → Good c a b cc u → Good c a b u s₂ →
    Good c a b s₂ t₂ → c.col s₁ t₁ = c.col s₂ t₂ →
    G.degree b = G.maxDegree → Robust G a b t₁ t₂ → False

/-- CCJS Lemma 2.7 (short kites). -/
def ShortKiteProp (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (c : PEC G (Fin G.maxDegree)) (a b cc u x y : V),
    [a, b, cc, u, x, y].Nodup → IsColMinus c a b →
    (∃ δ, c.col b u = some δ ∧ c.IsFree a δ) → Good c a b u x →
    (∃ β, c.col a cc = some β ∧ c.IsFree b β) → Good c a b cc u → Good c a b u y →
    (∃ θ, InA c a b θ ∧ c.IsFree x θ) → (∃ θ, InA c a b θ ∧ c.IsFree y θ) →
    G.degree x < G.maxDegree → G.degree y < G.maxDegree → False

end Overfull
