/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# CDR Paper III: definitions and external inputs

Same definitions as `challenge/CDRPaperIIIChallenge.lean`. The two external theorems enter as
explicit propositions:

* `GaleInt` — Gale (1957), Feasibility Theorem, integer version (statement T1);
* `ThreeSquaresDense` — Duke–Schulze-Pillot (1990): representations of `n ≡ 3 (mod 8)` as sums
  of three squares near any prescribed direction, for large `n`.
-/

@[expose] public section

namespace CDRBicolour.PaperIII

open Finset

/-- A Steiner triple system on `Fin v`. -/
def IsSTS {v : ℕ} (B : Finset (Finset (Fin v))) : Prop :=
  (∀ b ∈ B, b.card = 3) ∧ ∀ x y : Fin v, x ≠ y → ∃! b, b ∈ B ∧ x ∈ b ∧ y ∈ b

/-- A bicolouring with exactly `m` colours: all colours used, every block exactly two colours. -/
def IsBicolouring {v m : ℕ} (B : Finset (Finset (Fin v))) (col : Fin v → Fin m) : Prop :=
  Function.Surjective col ∧ ∀ b ∈ B, (b.image col).card = 2

/-- There is an `m`-bicolourable STS(v). -/
def Bicolourable (v m : ℕ) : Prop :=
  ∃ (B : Finset (Finset (Fin v))) (col : Fin v → Fin m), IsSTS B ∧ IsBicolouring B col

/-- Admissible orders. -/
def Admissible (v : ℕ) : Prop := v % 6 = 1 ∨ v % 6 = 3

/-- **External input T1** (Gale 1957, Feasibility Theorem, integer version). -/
def GaleInt : Prop :=
  ∀ (N : Type) [Fintype N] [DecidableEq N] (c : N → N → ℤ), (∀ x y, 0 ≤ c x y) →
    ∀ (d : N → ℤ), ∑ x, d x = 0 →
    ((∃ f : N → N → ℤ, (∀ x y, f x y = -f y x) ∧ (∀ x y, f x y ≤ c x y) ∧
        ∀ x, ∑ y, f x y = d x) ↔
      ∀ S : Finset N, ∑ x ∈ S, d x ≤ ∑ x ∈ S, ∑ y ∈ Sᶜ, c x y)

/-- **External input** (Duke–Schulze-Pillot 1990, Theorem 3(ii) + Lemma 5(ii); Gauss). -/
def ThreeSquaresDense : Prop :=
  ∀ u : Fin 3 → ℝ, ∑ i, u i ^ 2 = 1 → ∀ ε > 0, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → n % 8 = 3 →
    ∃ x : Fin 3 → ℤ, ∑ i, x i ^ 2 = (n : ℤ) ∧
      ∀ i, |(x i : ℝ) - Real.sqrt n * u i| ≤ ε * Real.sqrt n

end CDRBicolour.PaperIII
