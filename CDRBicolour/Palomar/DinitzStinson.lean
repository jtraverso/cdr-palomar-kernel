/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Basic
public import CDR.Necessary
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Dinitz–Stinson necessary conditions (Palomar)

Palomar entry PALOMAR-2026-11-04-000014 v1 (`jtraverso/cdr-bicolouring-sts` @ `a768a98`):
Colbourn–Dinitz–Rosa Theorem 2.4 and Dinitz–Stinson Proposition 1.2, with their own statement
layer (`CDR.IsSTS`, `CDR.IsBicolouring`, `CDR.Bicolourable3`).

* `realises_iff_bicolourable3`: our `Realises a b c` is exactly `CDR.Bicolourable3 (a+b+c) a b c`
  (an independent cross-check of the statement layer).
* `STS.even_card_sub_one`: the order of an STS is odd (the blocks through a point pair up the
  other points).
* `admissible_of_realises`: **necessity**. A realised profile with three nonempty classes is
  admissible: the pair-count identity (Dinitz–Stinson 1.2(1), `CDR.IsSTS.three_mul_sum`), no two
  classes of size `2` (Dinitz–Stinson 1.2(2), `CDR.not_two_classes_of_size_two`), and
  `n ≡ 1, 3 (mod 6)`.
-/

@[expose] public section

namespace CDRBicolour.Palomar

open Finset

/-- Our statement layer agrees with the Palomar entry's. -/
theorem realises_iff_bicolourable3 (a b c : ℕ) :
    Realises a b c ↔ CDR.Bicolourable3 (a + b + c) a b c := by
  constructor
  · rintro ⟨S, col, hcol, ha, hb, hc⟩
    exact ⟨S.blocks, col, ⟨S.card_eq_three, S.existsUnique_block⟩, hcol, ha, hb, hc⟩
  · rintro ⟨B, φ, hB, hφ, ha, hb, hc⟩
    exact ⟨⟨B, hB.card_eq, hB.pair⟩, φ, hφ, ha, hb, hc⟩

/-- The order of a Steiner triple system is odd: the blocks through `x` pair up the other
points. -/
theorem STS.even_card_sub_one {V : Type*} [Fintype V] [DecidableEq V] (S : STS V) (x : V) :
    Even (Fintype.card V - 1) := by
  have hU : univ.erase x = (S.blocks.filter (x ∈ ·)).biUnion (fun t => t.erase x) := by
    ext y
    simp only [mem_erase, mem_univ, and_true, mem_biUnion, mem_filter]
    constructor
    · intro hyx
      obtain ⟨t, ⟨ht, hxt, hyt⟩, -⟩ := S.existsUnique_block x y (Ne.symm hyx)
      exact ⟨t, ⟨ht, hxt⟩, hyx, hyt⟩
    · rintro ⟨t, -, hyx, -⟩
      exact hyx
  have hdisj : ∀ t ∈ S.blocks.filter (x ∈ ·), ∀ t' ∈ S.blocks.filter (x ∈ ·), t ≠ t' →
      Disjoint (t.erase x) (t'.erase x) := by
    intro t ht t' ht' hne
    rw [disjoint_left]
    intro y hy hy'
    rw [mem_filter] at ht ht'
    rw [mem_erase] at hy hy'
    obtain ⟨u, -, huniq⟩ := S.existsUnique_block x y (Ne.symm hy.1)
    exact hne ((huniq t ⟨ht.1, ht.2, hy.2⟩).trans (huniq t' ⟨ht'.1, ht'.2, hy'.2⟩).symm)
  have hcard := card_biUnion hdisj
  rw [← hU, card_erase_of_mem (mem_univ x), card_univ] at hcard
  have h2 : ∀ t ∈ S.blocks.filter (x ∈ ·), (t.erase x).card = 2 := by
    intro t ht
    rw [mem_filter] at ht
    rw [card_erase_of_mem ht.2, S.card_eq_three t ht.1]
  rw [hcard, sum_congr rfl h2, sum_const, smul_eq_mul]
  exact Nat.even_mul.2 (Or.inr even_two)

/-- **Necessity** (Dinitz–Stinson Proposition 1.2, via Palomar): a profile with three nonempty
classes that is realised is admissible. -/
theorem admissible_of_realises {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : Realises a b c) : AdmissibleProfile a b c := by
  obtain ⟨S, col, hcol, h0, h1, h2⟩ := h
  have hB : CDR.IsSTS S.blocks := ⟨S.card_eq_three, S.existsUnique_block⟩
  have h3 := hB.three_mul_sum (φ := col) hcol
  rw [Fin.sum_univ_three, Fintype.card_fin] at h3
  have e0 : #(CDR.colourClass col 0) = a := h0
  have e1 : #(CDR.colourClass col 1) = b := h1
  have e2 : #(CDR.colourClass col 2) = c := h2
  rw [e0, e1, e2] at h3
  have hodd := STS.even_card_sub_one S ⟨0, by omega⟩
  rw [Fintype.card_fin] at hodd
  have two : ∀ k l : Fin 3, k ≠ l → classSize col k = 2 → classSize col l = 2 → False :=
    fun k l hkl hk hl => CDR.not_two_classes_of_size_two hB hcol hkl hk hl
  refine ⟨ha, hb, hc, ?_, ?_, ?_, ?_, ?_⟩
  · -- `n` odd and `3 ∣ n (n - 1)`
    have h3d : 3 ∣ (a + b + c) * (a + b + c - 1) := ⟨_, h3.symm⟩
    obtain ⟨r, hr⟩ := hodd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3d with h | h <;> omega
  · zify [show 1 ≤ a by omega, show 1 ≤ b by omega, show 1 ≤ c by omega,
      show 1 ≤ a + b + c by omega] at h3
    have : (2 : ℤ) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c) = 2 * (a + b + c) := by
      linear_combination h3
    exact mul_left_cancel₀ two_ne_zero this
  · rintro ⟨rfl, rfl⟩; exact two 0 1 (by decide) h0 h1
  · rintro ⟨rfl, rfl⟩; exact two 0 2 (by decide) h0 h2
  · rintro ⟨rfl, rfl⟩; exact two 1 2 (by decide) h1 h2

/-- The same, in the Palomar entry's language. -/
theorem admissible_of_bicolourable3 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : CDR.Bicolourable3 (a + b + c) a b c) : AdmissibleProfile a b c :=
  admissible_of_realises ha hb hc ((realises_iff_bicolourable3 a b c).2 h)

end CDRBicolour.Palomar
