/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Steiner triple systems and bicolourings

C. J. Colbourn, J. H. Dinitz, A. Rosa, *Bicoloring Steiner triple systems*, Electron. J.
Combin. 6 (1999) #R25.

A Steiner triple system on a finite type `X` (`IsSTS`) is a family of 3-subsets (blocks) such
that every pair of distinct points lies in exactly one block. A colouring `φ : X → κ` is a
*bicolouring* (`IsBicolouring`) if every block receives exactly two colours.
`Bicolourable3 v a b c`: some STS on `v` points has a bicolouring with colours `0, 1, 2`
whose classes have sizes `a, b, c`.

Counting (`six_mul_card_blocks`, `two_mul_card_blocks`): `6|B| = v(v − 1)` and
`2|B| = Σ_k c_k(c_k − 1)`, the blocks each covering six ordered pairs, two of them
monochromatic.
-/

@[expose] public section

namespace CDR

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A Steiner triple system on `X`: blocks of size three, every pair of distinct points in
exactly one block. -/
structure IsSTS (B : Finset (Finset X)) : Prop where
  card_eq : ∀ t ∈ B, #t = 3
  pair : ∀ x y, x ≠ y → ∃! t, t ∈ B ∧ x ∈ t ∧ y ∈ t

/-- `φ` is a bicolouring of the blocks `B`: every block receives exactly two colours. -/
def IsBicolouring {κ : Type*} [DecidableEq κ] (B : Finset (Finset X)) (φ : X → κ) : Prop :=
  ∀ t ∈ B, #(t.image φ) = 2

/-- The colour class of `k`. -/
def colourClass {κ : Type*} [DecidableEq κ] (φ : X → κ) (k : κ) : Finset X :=
  univ.filter fun x => φ x = k

/-- `Bicolourable3 v a b c`: there is an STS on `v` points with a bicolouring by the colours
`0, 1, 2` whose colour classes have sizes `a`, `b`, `c`. -/
def Bicolourable3 (v a b c : ℕ) : Prop :=
  ∃ (B : Finset (Finset (Fin v))) (φ : Fin v → Fin 3), IsSTS B ∧ IsBicolouring B φ ∧
    #(colourClass φ 0) = a ∧ #(colourClass φ 1) = b ∧ #(colourClass φ 2) = c

/-! ### Counting -/

theorem IsSTS.offDiag_eq_biUnion {B : Finset (Finset X)} (hB : IsSTS B) :
    (univ : Finset X).offDiag = B.biUnion fun t => t.offDiag := by
  ext ⟨x, y⟩
  simp only [mem_offDiag, mem_univ, true_and, mem_biUnion]
  constructor
  · intro hxy
    obtain ⟨t, ⟨ht, hx, hy⟩, -⟩ := hB.pair x y hxy
    exact ⟨t, ht, hx, hy, hxy⟩
  · rintro ⟨t, -, -, -, hxy⟩
    exact hxy

theorem IsSTS.pairwiseDisjoint_offDiag {B : Finset (Finset X)} (hB : IsSTS B) :
    (B : Set (Finset X)).PairwiseDisjoint fun t => t.offDiag := by
  intro t ht t' ht' hne
  rw [Function.onFun, disjoint_left]
  rintro ⟨x, y⟩ h h'
  rw [mem_offDiag] at h h'
  obtain ⟨s, -, hs⟩ := hB.pair x y h.2.2
  exact hne ((hs t ⟨ht, h.1, h.2.1⟩).trans (hs t' ⟨ht', h'.1, h'.2.1⟩).symm)

/-- `6|B| = v(v − 1)`. -/
theorem IsSTS.six_mul_card {B : Finset (Finset X)} (hB : IsSTS B) :
    6 * #B = Fintype.card X * (Fintype.card X - 1) := by
  have h := congrArg card hB.offDiag_eq_biUnion
  rw [card_biUnion hB.pairwiseDisjoint_offDiag, offDiag_card, card_univ,
    sum_const_nat (m := 6) (fun t ht => by rw [offDiag_card, hB.card_eq t ht])] at h
  rw [Nat.mul_sub_one, h, mul_comm]

/-- The monochromatic ordered pairs of distinct points of `s`. -/
def monoPairs {κ : Type*} [DecidableEq κ] (s : Finset X) (φ : X → κ) : Finset (X × X) :=
  s.offDiag.filter fun p => φ p.1 = φ p.2

theorem monoPairs_eq_biUnion {κ : Type*} [DecidableEq κ] (s : Finset X) (φ : X → κ) :
    monoPairs s φ = (s.image φ).biUnion fun k => (s.filter fun x => φ x = k).offDiag := by
  ext ⟨p, q⟩
  simp only [monoPairs, mem_filter, mem_offDiag, mem_biUnion, mem_image]
  constructor
  · rintro ⟨⟨hp, hq, hpq⟩, h⟩
    exact ⟨φ p, ⟨p, hp, rfl⟩, ⟨hp, rfl⟩, ⟨hq, h.symm⟩, hpq⟩
  · rintro ⟨k, -, ⟨hp, rfl⟩, ⟨hq, h⟩, hpq⟩
    exact ⟨⟨hp, hq, hpq⟩, h.symm⟩

/-- The number of monochromatic ordered pairs is `Σ_k m_k (m_k − 1)` over the colour
multiplicities. -/
theorem card_monoPairs {κ : Type*} [DecidableEq κ] (s : Finset X) (φ : X → κ) :
    #(monoPairs s φ) = ∑ k ∈ s.image φ,
      #(s.filter fun x => φ x = k) * (#(s.filter fun x => φ x = k) - 1) := by
  rw [monoPairs_eq_biUnion, card_biUnion]
  · exact sum_congr rfl fun k _ => by rw [offDiag_card, Nat.mul_sub_one]
  · intro k _ k' _ hkk'
    rw [Function.onFun, disjoint_left]
    rintro ⟨p, q⟩ h h'
    simp only [mem_offDiag, mem_filter] at h h'
    exact hkk' (h.1.2.symm.trans h'.1.2)

/-- A three-point set with exactly two colours has exactly two monochromatic ordered pairs. -/
theorem card_monoPairs_of_card_three {κ : Type*} [DecidableEq κ] {t : Finset X} {φ : X → κ}
    (ht : #t = 3) (h2 : #(t.image φ) = 2) : #(monoPairs t φ) = 2 := by
  rw [card_monoPairs]
  obtain ⟨k₁, k₂, hne, himg⟩ := card_eq_two.1 h2
  have hsum := card_eq_sum_card_image φ t
  rw [himg, sum_pair hne] at hsum ⊢
  have hpos : ∀ k ∈ t.image φ, 0 < #(t.filter fun x => φ x = k) := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hk
    exact card_pos.2 ⟨x, mem_filter.2 ⟨hx, rfl⟩⟩
  have h1 := hpos k₁ (by rw [himg]; exact mem_insert_self _ _)
  have h2' := hpos k₂ (by rw [himg]; exact mem_insert_of_mem (mem_singleton_self _))
  set m₁ := #(t.filter fun x => φ x = k₁)
  set m₂ := #(t.filter fun x => φ x = k₂)
  have hm : m₁ + m₂ = 3 := by rw [← ht, hsum]
  have : (m₁ = 1 ∧ m₂ = 2) ∨ (m₁ = 2 ∧ m₂ = 1) := by omega
  rcases this with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb]

/-- Each block covers exactly two monochromatic ordered pairs: `2|B| = Σ_k c_k (c_k − 1)`. -/
theorem IsSTS.two_mul_card {κ : Type*} [Fintype κ] [DecidableEq κ] {B : Finset (Finset X)}
    (hB : IsSTS B) {φ : X → κ} (hφ : IsBicolouring B φ) :
    2 * #B = ∑ k, #(colourClass φ k) * (#(colourClass φ k) - 1) := by
  have h : monoPairs univ φ = B.biUnion fun t => monoPairs t φ := by
    ext ⟨p, q⟩
    have := congrArg (fun s => (p, q) ∈ s) hB.offDiag_eq_biUnion
    simp only [monoPairs, mem_filter, mem_biUnion] at this ⊢
    rw [this]
    constructor
    · rintro ⟨⟨t, ht, hpq⟩, h⟩
      exact ⟨t, ht, hpq, h⟩
    · rintro ⟨t, ht, hpq, h⟩
      exact ⟨⟨t, ht, hpq⟩, h⟩
  have hc := congrArg card h
  rw [card_biUnion, sum_const_nat (m := 2)
    (fun t ht => card_monoPairs_of_card_three (hB.card_eq t ht) (hφ t ht))] at hc
  · rw [mul_comm, ← hc, card_monoPairs]
    refine (sum_subset (subset_univ _) fun k _ hk => ?_).trans ?_
    · have : #(univ.filter fun x => φ x = k) = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        exact fun x _ hx => hk (mem_image.2 ⟨x, mem_univ x, hx⟩)
      rw [this]
      rfl
    · rfl
  · intro t ht t' ht' hne
    rw [Function.onFun, disjoint_left]
    rintro ⟨p, q⟩ h h'
    simp only [monoPairs, mem_filter] at h h'
    exact disjoint_left.1 (hB.pairwiseDisjoint_offDiag ht ht' hne) h.1 h'.1

/-- **Divisibility (Colbourn–Dinitz–Rosa, Proposition 1.4 for STS; Dinitz–Stinson,
Proposition 1.2 (1)).** For a bicoloured STS on `v` points with colour classes of sizes `c_k`,
`3 Σ_k c_k (c_k − 1) = v (v − 1)`, that is `Σ_k C(c_k, 2) = C(v, 2)/3`. -/
theorem IsSTS.three_mul_sum {κ : Type*} [Fintype κ] [DecidableEq κ] {B : Finset (Finset X)}
    (hB : IsSTS B) {φ : X → κ} (hφ : IsBicolouring B φ) :
    3 * ∑ k, #(colourClass φ k) * (#(colourClass φ k) - 1) =
      Fintype.card X * (Fintype.card X - 1) := by
  rw [← hB.two_mul_card hφ, ← hB.six_mul_card]
  ring

end CDR
