/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Spreading a family over the elements of each class

`X` is a finite type with a class map `f : X → K` (any finite type `K` of classes). Given, for every class `r`, a family
`F r` indexed by `Fin (csize f r)`, `spread f F x` is the member of `F (f x)` attached to `x`
through a fixed enumeration of the class. Sums over `X` become sums over the families.

> Adapted from `jtraverso/forbidden-latin-squares` @ e174838 (`FLS/Spread.lean`), same author.
> Generalized from `ZMod 3` to an arbitrary finite class type `K`.
-/

@[expose] public section

namespace CDRBicolour.KBicolor.Hilton

open Finset

/-- The size of class `r`. -/
abbrev csize {X K : Type*} [Fintype X] [DecidableEq K] (f : X → K) (r : K) : ℕ :=
  Fintype.card {x // f x = r}

variable {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K] (f : X → K)

/-- The member of the family of its class attached to `x`. -/
noncomputable def spread {V : Type*} (F : ∀ r : K, Fin (csize f r) → V) (x : X) : V :=
  F (f x) (Fintype.equivFin {y // f y = f x} ⟨x, rfl⟩)

theorem spread_eq {V : Type*} (F : ∀ r : K, Fin (csize f r) → V) (x : X) (r : K)
    (hx : f x = r) : spread f F x = F r (Fintype.equivFin {y // f y = r} ⟨x, hx⟩) := by
  subst hx; rfl

theorem sum_spread_class {V M : Type*} [AddCommMonoid M] (F : ∀ r : K, Fin (csize f r) → V)
    (ψ : V → M) (r : K) :
    ∑ x ∈ univ.filter (fun x => f x = r), ψ (spread f F x) = ∑ t, ψ (F r t) := by
  classical
  rw [Finset.sum_subtype (univ.filter (fun x => f x = r)) (p := fun x => f x = r)
    (fun x => by simp)]
  rw [show (∑ x : {x // f x = r}, ψ (spread f F x.1)) =
      ∑ x : {x // f x = r}, ψ (F r (Fintype.equivFin {y // f y = r} x)) from
    Finset.sum_congr rfl fun x _ => by rw [spread_eq f F x.1 r x.2]]
  exact Fintype.sum_equiv (Fintype.equivFin {y // f y = r}) _ _ (fun _ => rfl)

theorem sum_spread {V M : Type*} [AddCommMonoid M] (F : ∀ r : K, Fin (csize f r) → V)
    (φ : K → V → M) :
    ∑ x, φ (f x) (spread f F x) = ∑ r, ∑ t, φ r (F r t) := by
  classical
  rw [← Finset.sum_fiberwise univ f (fun x => φ (f x) (spread f F x))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [show (∑ x ∈ univ.filter (fun x => f x = r), φ (f x) (spread f F x)) =
      ∑ x ∈ univ.filter (fun x => f x = r), φ r (spread f F x) from
    Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]]
  exact sum_spread_class f F (φ r) r

end CDRBicolour.KBicolor.Hilton
