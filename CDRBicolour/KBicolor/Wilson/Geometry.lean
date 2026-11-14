/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.KBicolor.Wilson.ReserveHinge
public import CDRBicolour.KBicolor.Wilson.ReserveLattice
public import CDRBicolour.KBicolor.Wilson.NearFullReserve

/-!
# The geometric conditions H2, H3 and H4 of the Wilson residual

`reserveThreshold k δR = ceil(max(10,k+5)/δR)` is explicit. Beyond it, a reserve
of at least `δR*n` vertices per colour gives all three conditions with the common
constant `reserveAlpha δR`. Only the original parity and pair identity are used.
`residual_decomposition_of_seed` isolates the remaining H1 construction: it is
not an assertion that this diffuse seed has already been constructed.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.KBicolor.Wilson

open Finset TypedTriangle

def reserveAlpha (δR : ℝ) : ℝ := min (δR / 2) (δR ^ 2 / 4)

def reserveThreshold (k : ℕ) (δR : ℝ) : ℕ := ⌈max (10 : ℝ) (k + 5) / δR⌉₊

theorem reserveAlpha_pos {δR : ℝ} (hδ : 0 < δR) : 0 < reserveAlpha δR := by
  exact lt_min (by positivity) (by positivity)

theorem reserveThreshold_bound {k n : ℕ} {δR : ℝ} (hδ : 0 < δR)
    (hn : reserveThreshold k δR ≤ n) : max (10 : ℝ) (k + 5) ≤ δR * n := by
  have hncast : (reserveThreshold k δR : ℝ) ≤ n := by exact_mod_cast hn
  have hceil : max (10 : ℝ) ((k : ℝ) + 5) / δR ≤ n :=
    (Nat.le_ceil _).trans hncast
  have := (div_le_iff₀ hδ).mp hceil
  linarith

variable {A : Type*} [Fintype A] [DecidableEq A] {k n g t : ℕ}
variable {lab : Fin n → Fin k} {κ : A → Fin k}

theorem residual_H234 (h : Setup lab κ g t) (hk : 2 ≤ k)
    {S : Finset (Finset (Fin g))} (hS : _root_.STS.IsSTS S) (Λ : LFam A S t)
    {δR : ℝ} (hδ : 0 < δR) (hn : reserveThreshold k δR ≤ n)
    (hcls : ∀ X, δR * n ≤ #((reserve h).filter fun v => lab v = X))
    (hodd : Odd n) (heven : ∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y))
    (hdiv : 3 * ∑ X, ksz lab X * (ksz lab X - 1) = n * (n - 1)) :
    IsPhysical (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k)
      (edges (rHostK lab ((crossP h Λ).biUnion triEdges))) ∧
    CommonNbrCond (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) (reserveAlpha δR) ∧
    HingeCond (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) (reserveAlpha δR) 6 := by
  have hbound := reserveThreshold_bound hδ hn
  have h10 : 10 ≤ δR * n := le_trans (le_max_left _ _) hbound
  have hbig : ∀ X, k + 4 < #((reserve h).filter fun v => lab v = X) := by
    intro X
    have hright := le_trans (le_max_right _ _) hbound
    have hlt : (k : ℝ) + 4 < #((reserve h).filter fun v => lab v = X) := by
      linarith [hcls X]
    exact_mod_cast hlt
  refine ⟨residual_H2_of_reserve h hk hS Λ hbig hodd heven hdiv, ?_, ?_⟩
  · exact commonNbr_mono (residual_H3_of_reserve h hS Λ hcls (by linarith)) (min_le_left _ _)
  · exact hingeCond_mono (residual_H4_of_reserve h hS Λ hδ hcls h10) (min_le_right _ _)

/-- T supplies a residual decomposition once its diffuse seed H1 has been constructed. -/
theorem residual_decomposition_of_seed (k : ℕ) (hk : 2 ≤ k) {δR C : ℝ}
    (hδ : 0 < δR) (hC : 1 ≤ C) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (lab : Fin n → Fin k), n₀ ≤ n →
      ∀ (A : Type) [Fintype A] [DecidableEq A] (κ : A → Fin k) (g t : ℕ)
      (h : Setup lab κ g t) (S : Finset (Finset (Fin g))), _root_.STS.IsSTS S →
      ∀ Λ : LFam A S t,
      (∀ X, δR * n ≤ #((reserve h).filter fun v => lab v = X)) →
      Odd n → (∀ X Y, X ≠ Y → Even (ksz lab X * ksz lab Y)) →
      3 * ∑ X, ksz lab X * (ksz lab X - 1) = n * (n - 1) →
      ∀ μ : Finset (Fin n) → ℝ,
      IsDiffuseSeed (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k) C μ →
      ∃ D, IsDecomposition (rHostK lab ((crossP h Λ).biUnion triEdges)) (bicF k)
        (edges (rHostK lab ((crossP h Λ).biUnion triEdges))) D := by
  obtain ⟨nT, hT⟩ := Vortex.main_theorem_T (bicF k) (reserveAlpha δR) C 6
    (reserveAlpha_pos hδ) hC le_rfl
  refine ⟨max nT (reserveThreshold k δR), fun n lab hn A _ _ κ g t h S hS Λ hcls
    hodd heven hdiv μ hμ => ?_⟩
  obtain ⟨H2, H3, H4⟩ := residual_H234 h hk hS Λ hδ (le_of_max_le_right hn)
    hcls hodd heven hdiv
  exact hT _ (by rw [Fintype.card_fin]; exact le_of_max_le_left hn) ⟨μ, hμ⟩ H2 H3 H4

/-- An example of the geometric threshold only, not the final counting threshold. -/
example : reserveThreshold 5 (1 / 40000) = 400000 := by
  norm_num [reserveThreshold]

end CDRBicolour.KBicolor.Wilson
