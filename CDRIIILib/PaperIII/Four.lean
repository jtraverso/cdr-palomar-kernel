/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.PaperIII.Bridge

/-!
# T6 for `k = 4`: CDR Conjecture 3.5 for all large orders, from `ThreeSquaresDense`

`ThreeSquaresDense` with `u = (1, 0, 0)` and `ε = 1/8` gives `CapRep v` for every large admissible
`v` (`N = v(v+8)/3` is an integer `≡ 3 (mod 8)`), and `conj35_of_capRep` concludes.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.PaperIII

open Finset CDRBicolour.KBicolor

/-- For admissible `v`, `v(v+8)` is divisible by `3` and `≡ 1 (mod 8)`. -/
theorem vv8_facts {v : ℕ} (hv : Admissible v) : v * (v + 8) % 3 = 0 ∧ v * (v + 8) % 8 = 1 := by
  have hodd : v % 2 = 1 := by rcases hv with h | h <;> omega
  obtain ⟨m, rfl⟩ : ∃ m, v = 2 * m + 1 := ⟨v / 2, by omega⟩
  have e : (2 * m + 1) * (2 * m + 1 + 8) = 4 * (m * (m + 1)) + 16 * m + 9 := by ring
  have hev : (m * (m + 1)) % 2 = 0 := Nat.even_iff.1 (Nat.even_mul_succ_self m)
  refine ⟨?_, ?_⟩
  · rcases hv with h | h
    · have : (2 * m + 1 + 8) % 3 = 0 := by omega
      rw [Nat.mul_mod, this]; simp
    · have : (2 * m + 1) % 3 = 0 := by omega
      rw [Nat.mul_mod, this]; simp
  · rw [e]; omega

/-- `ThreeSquaresDense` gives `CapRep` for all large admissible orders. -/
theorem capRep_eventually (hA : ThreeSquaresDense) :
    ∃ V₀ : ℕ, ∀ v, V₀ ≤ v → (v % 6 = 1 ∨ v % 6 = 3) → CapRep v := by
  obtain ⟨N₀, hN⟩ := hA ![1, 0, 0] (by simp [Fin.sum_univ_three]) (1 / 8) (by norm_num)
  refine ⟨N₀, fun v hv hadm => ?_⟩
  obtain ⟨h3, h8⟩ := vv8_facts hadm
  set N := v * (v + 8) / 3 with hNdef
  have hN3 : 3 * N = v * (v + 8) := by omega
  have hN8 : N % 8 = 3 := by omega
  have hNv : N₀ ≤ N := by
    have : v ≤ N := by nlinarith
    omega
  obtain ⟨x, hx, hxu⟩ := hN N hNv hN8
  have hs : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  have h0 := hxu 0; have h1 := hxu 1; have h2 := hxu 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, mul_one, mul_zero, sub_zero] at h0 h1 h2
  obtain ⟨h0a, h0b⟩ := abs_le.1 h0
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  refine ⟨x 0, x 1, x 2, ?_, ?_, ?_⟩
  · rw [Fin.sum_univ_three] at hx
    have : ((3 * N : ℕ) : ℤ) = ((v * (v + 8) : ℕ) : ℤ) := by rw [hN3]
    push_cast at this
    rw [← this, ← hx]
  · have hR : 7 * |((x 1 : ℤ) : ℝ)| ≤ ((x 0 : ℤ) : ℝ) := by linarith
    exact_mod_cast hR
  · have hR : 7 * |((x 2 : ℤ) : ℝ)| ≤ ((x 0 : ℤ) : ℝ) := by linarith
    exact_mod_cast hR

/-- **T6, `k = 4`: CDR Conjecture 3.5 for all large orders.** -/
theorem conj35_large (hA : ThreeSquaresDense) :
    ∃ v₀ : ℕ, ∀ v, v₀ ≤ v → Admissible v → Bicolourable v 4 := by
  obtain ⟨n₀, h⟩ := conj35_of_capRep (capRep_eventually hA)
  refine ⟨n₀, fun v hv hadm => ?_⟩
  obtain ⟨lab, hpos, D, hD⟩ := h v hv hadm
  exact bicolourable_of_decomposition lab hpos D hD

end CDRBicolour.PaperIII
