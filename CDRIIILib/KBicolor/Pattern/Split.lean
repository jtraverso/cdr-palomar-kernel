/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import BaranyaiLib.Rounding
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Equitable splitting of nonnegative integer matrices

`equitable_split`: a matrix `M : I → J → ℕ` whose row sums are `k * a i` and column sums are
`k * b j` (`0 < k`) contains a submatrix `X ≤ M` with row sums `a i` and column sums `b j`.
This is Baranyai's rounding lemma applied to `M / k`.

`decompose`: iterating, such an `M` is the sum of `k` matrices with row sums `a` and column
sums `b`.
-/

@[expose] public section

namespace CDRBicolour.KBicolor.Hilton

open Finset

variable {I J : Type*} [Fintype I] [Fintype J]

theorem equitable_split (M : I → J → ℕ) {k : ℕ} (hk : 0 < k) (a : I → ℕ) (b : J → ℕ)
    (hr : ∀ i, ∑ j, M i j = k * a i) (hc : ∀ j, ∑ i, M i j = k * b j) :
    ∃ X : I → J → ℕ, (∀ i j, X i j ≤ M i j) ∧ (∀ i, ∑ j, X i j = a i) ∧
      (∀ j, ∑ i, X i j = b j) := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨B, hB, hBr, hBc, -⟩ := Baranyai.rounding_fintype (fun i j => (M i j : ℝ) / k)
  -- the entries of `B` are between `0` and `M`
  have hB0 : ∀ i j, 0 ≤ B i j := by
    intro i j
    have h0 : (0 : ℝ) ≤ (M i j : ℝ) / k := div_nonneg (Nat.cast_nonneg _) hkR.le
    rcases hB i j with h | h <;> rw [h]
    · exact Int.floor_nonneg.mpr h0
    · exact (Int.floor_nonneg.mpr h0).trans (Int.floor_le_ceil _)
  have hBM : ∀ i j, B i j ≤ (M i j : ℤ) := by
    intro i j
    have hle : (M i j : ℝ) / k ≤ (M i j : ℝ) := by
      rw [div_le_iff₀ hkR]
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith [(Nat.cast_nonneg (M i j) : (0 : ℝ) ≤ M i j)]
    have hc' : ⌈(M i j : ℝ) / k⌉ ≤ (M i j : ℤ) := by
      rw [Int.ceil_le]; exact_mod_cast hle
    rcases hB i j with h | h <;> rw [h]
    · exact (Int.floor_le_ceil _).trans hc'
    · exact hc'
  -- row and column sums of `M / k` are the integers `a i`, `b j`
  have hAr : ∀ i, ∑ j, (M i j : ℝ) / k = (a i : ℤ) := by
    intro i
    rw [← Finset.sum_div, div_eq_iff hkR.ne']
    have := congrArg (fun m : ℕ => (m : ℝ)) (hr i)
    push_cast at this ⊢
    rw [this]; ring
  have hAc : ∀ j, ∑ i, (M i j : ℝ) / k = (b j : ℤ) := by
    intro j
    rw [← Finset.sum_div, div_eq_iff hkR.ne']
    have := congrArg (fun m : ℕ => (m : ℝ)) (hc j)
    push_cast at this ⊢
    rw [this]; ring
  have hBr' : ∀ i, ∑ j, B i j = (a i : ℤ) := by
    intro i
    rcases hBr i with h | h <;> rw [h, hAr i] <;> simp
  have hBc' : ∀ j, ∑ i, B i j = (b j : ℤ) := by
    intro j
    rcases hBc j with h | h <;> rw [h, hAc j] <;> simp
  refine ⟨fun i j => (B i j).toNat, ?_, ?_, ?_⟩
  · intro i j
    have := hBM i j
    dsimp only
    omega
  · intro i
    dsimp only
    have h := hBr' i
    have hcast : ((∑ j, (B i j).toNat : ℕ) : ℤ) = ∑ j, B i j := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => Int.toNat_of_nonneg (hB0 i j)
    omega
  · intro j
    dsimp only
    have h := hBc' j
    have hcast : ((∑ i, (B i j).toNat : ℕ) : ℤ) = ∑ i, B i j := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hB0 i j)
    omega

theorem decompose (k : ℕ) : ∀ (M : I → J → ℕ) (a : I → ℕ) (b : J → ℕ),
    (∀ i, ∑ j, M i j = k * a i) → (∀ j, ∑ i, M i j = k * b j) →
    ∃ F : Fin k → I → J → ℕ, (∀ t i, ∑ j, F t i j = a i) ∧ (∀ t j, ∑ i, F t i j = b j) ∧
      (∀ i j, ∑ t, F t i j = M i j) := by
  induction k with
  | zero =>
    intro M a b hr _
    refine ⟨fun t => Fin.elim0 t, fun t => Fin.elim0 t, fun t => Fin.elim0 t, ?_⟩
    intro i j
    have h0 : ∑ j, M i j = 0 := by simpa using hr i
    have := (Finset.sum_eq_zero_iff.mp h0) j (Finset.mem_univ _)
    simp [this]
  | succ k ih =>
    intro M a b hr hc
    obtain ⟨X, hXM, hXr, hXc⟩ := equitable_split M (Nat.succ_pos k) a b hr hc
    obtain ⟨F, hFr, hFc, hFs⟩ := ih (fun i j => M i j - X i j) a b
      (fun i => by
        rw [Finset.sum_tsub_distrib _ (fun j _ => hXM i j), hr i, hXr i]
        rw [Nat.succ_mul]; omega)
      (fun j => by
        rw [Finset.sum_tsub_distrib _ (fun i _ => hXM i j), hc j, hXc j]
        rw [Nat.succ_mul]; omega)
    refine ⟨Fin.cons X F, ?_, ?_, ?_⟩
    · intro t i
      refine Fin.cases ?_ (fun t => ?_) t
      · simpa using hXr i
      · simpa using hFr t i
    · intro t j
      refine Fin.cases ?_ (fun t => ?_) t
      · simpa using hXc j
      · simpa using hFc t j
    · intro i j
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hFs i j]
      have := hXM i j
      omega

end CDRBicolour.KBicolor.Hilton
