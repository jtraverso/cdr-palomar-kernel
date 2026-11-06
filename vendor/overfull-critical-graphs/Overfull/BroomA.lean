/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Overfull.KiteG

/-!
# Brooms with two leaves, part A: the normal form

A *broom with two leaves* (Chen–Cao, arXiv:2512.07252, Lemma 3.1): `φ ∈ C^Δ(G − ab)`, `φ(bu) ∈ φ̄(a)`
and `φ(ux), φ(uy) ∈ A = φ̄(a) ∪ φ̄(b)`, i.e. `(a, b, u, x)` and `(a, b, u, y)` are Kierstead paths.
It is the short kite of CCJS without the vertex `c`.

`BNF c a b u x y β δ γ σ` is its normal form: `φ̄(b) = {β}`, `φ(bu) = δ ∈ φ̄(a)`, `φ(ux) = γ ∈ A`,
`φ(uy) = β`, `y` misses `σ ∈ φ̄(a)`, and `d(b) = d(u) = Δ`.
-/

@[expose] public section

namespace Overfull

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Five distinct vertices. -/
structure Distinct5 (a b u x y : V) : Prop where
  ab : a ≠ b
  au : a ≠ u
  ax : a ≠ x
  ay : a ≠ y
  bu : b ≠ u
  bx : b ≠ x
  by_ : b ≠ y
  ux : u ≠ x
  uy : u ≠ y
  xy : x ≠ y

/-- The normal form of a broom with two leaves. -/
structure BNF (c : PEC G (Fin G.maxDegree)) (a b u x y : V) (β δ γ σ : Fin G.maxDegree) :
    Prop where
  cm : IsColMinus c a b
  d5 : Distinct5 a b u x y
  db : G.degree b = G.maxDegree
  du : G.degree u = G.maxDegree
  βb : c.IsFree b β
  hbu : c.col b u = some δ
  δa : c.IsFree a δ
  hux : c.col u x = some γ
  γA : InA c a b γ
  huy : c.col u y = some β
  σy : c.IsFree y σ
  σa : c.IsFree a σ

namespace BNF

variable {c : PEC G (Fin G.maxDegree)} {a b u x y : V} {β δ γ σ : Fin G.maxDegree}
  (h : BNF c a b u x y β δ γ σ)
include h

theorem b_only {θ : Fin G.maxDegree} (hθ : c.IsFree b θ) : θ = β := h.cm.b_only h.db h.βb hθ

theorem free_a_of_inA {θ : Fin G.maxDegree} (hA : InA c a b θ) (hβ : θ ≠ β) : c.IsFree a θ :=
  hA.resolve_right fun hb => hβ (h.b_only hb)

theorem γβ : γ ≠ β := by
  rintro rfl
  exact h.d5.xy (c.col_proper h.hux h.huy)

theorem γa : c.IsFree a γ := h.free_a_of_inA h.γA h.γβ

end BNF

end Overfull
