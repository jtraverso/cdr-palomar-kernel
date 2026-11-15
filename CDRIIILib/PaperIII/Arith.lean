/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRIIILib.PaperIII.Geom
public import CDRIIILib.PaperIII.Four
public import CDRIIILib.KBicolor.Five

/-!
# The arithmetic input for `k ≥ 5`: splits near a symmetric profile

Fix a profile `p` on `Fin k` (`k ≥ 5`) with `p 0 + p 2 = p 1 + p 3` and `p 2 < p 0`. For every
large admissible `v`:
* the classes `X ≥ 4` are taken even, `c X = 2 ⌊p X v / 2⌋`;
* with `w = v - Σ_{X≥4} c X` (odd) and `S₄ = v(v+2)/3 - Σ_{X≥4} c X²` (`≡ 1 mod 4`), the number
  `M = 4 S₄ - w²` is `≡ 3 (mod 8)` and `M = m v² + O(v)`;
* `ThreeSquaresDense` gives `M = a² + b² + c²` near the direction `u ∝ (u₀, 0, u₂)` of the profile
  (its middle coordinate vanishes by the symmetry); one of `(a, ±b, c)` makes the four classes
  `c_i = (w + f_i)/4` integral, with `f = (a+b+c, a-b-c, -a+b-c, -a-b+c)`;
* the four classes satisfy `Σ c_i = w`, `Σ c_i² = S₄`, exactly one of them is odd, and each is
  within `ρ v` of `p_i v`.
-/

@[expose] public section

noncomputable section

namespace CDRBicolour.PaperIII

open Finset

/-! ### Residues -/

theorem vv2_facts {v : ℕ} (hv : Admissible v) : v * (v + 2) % 3 = 0 ∧ v * (v + 2) % 4 = 3 := by
  have hodd : v % 2 = 1 := by rcases hv with h | h <;> omega
  obtain ⟨m, rfl⟩ : ∃ m, v = 2 * m + 1 := ⟨v / 2, by omega⟩
  have e : (2 * m + 1) * (2 * m + 1 + 2) = 4 * (m * m) + 8 * m + 3 := by ring
  refine ⟨?_, by rw [e]; omega⟩
  rcases hv with h | h
  · have : (2 * m + 1 + 2) % 3 = 0 := by omega
    rw [Nat.mul_mod, this]; simp
  · have : (2 * m + 1) % 3 = 0 := by omega
    rw [Nat.mul_mod, this]; simp

theorem int_odd_sq_mod8 (w : ℤ) (hw : w % 2 = 1) : w ^ 2 % 8 = 1 := by
  have := CDRBicolour.KBicolor.sq_mod_eight w
  omega

/-! ### Four classes from a sum of three squares -/

theorem four_split (a b c w : ℤ) (ha : a % 2 = 1) (hb : b % 2 = 1) (hc : c % 2 = 1)
    (hw : (w + (a + b + c)) % 4 = 0) :
    ∃ c0 c1 c2 c3 : ℤ, 4 * c0 = w + (a + b + c) ∧ 4 * c1 = w + (a - b - c) ∧
      4 * c2 = w + (-a + b - c) ∧ 4 * c3 = w + (-a - b + c) := by
  refine ⟨(w + (a + b + c)) / 4, (w + (a - b - c)) / 4, (w + (-a + b - c)) / 4,
    (w + (-a - b + c)) / 4, ?_, ?_, ?_, ?_⟩ <;> omega

theorem four_sums {a b c w c0 c1 c2 c3 : ℤ} (h0 : 4 * c0 = w + (a + b + c))
    (h1 : 4 * c1 = w + (a - b - c)) (h2 : 4 * c2 = w + (-a + b - c))
    (h3 : 4 * c3 = w + (-a - b + c)) :
    c0 + c1 + c2 + c3 = w ∧ 4 * (c0 ^ 2 + c1 ^ 2 + c2 ^ 2 + c3 ^ 2) = w ^ 2 + (a ^ 2 + b ^ 2 + c ^ 2) := by
  constructor
  · linarith
  · have e0 : (4 * c0) ^ 2 = (w + (a + b + c)) ^ 2 := by rw [h0]
    have e1 : (4 * c1) ^ 2 = (w + (a - b - c)) ^ 2 := by rw [h1]
    have e2 : (4 * c2) ^ 2 = (w + (-a + b - c)) ^ 2 := by rw [h2]
    have e3 : (4 * c3) ^ 2 = (w + (-a - b + c)) ^ 2 := by rw [h3]
    nlinarith

/-- With `Σ c_i² ≡ 1 (mod 4)`, at most one of four naturals is odd. -/
theorem four_parity (c0 c1 c2 c3 : ℕ) (h : (c0 ^ 2 + c1 ^ 2 + c2 ^ 2 + c3 ^ 2) % 4 = 1) :
    ¬ (c0 % 2 = 1 ∧ c1 % 2 = 1) ∧ ¬ (c0 % 2 = 1 ∧ c2 % 2 = 1) ∧ ¬ (c0 % 2 = 1 ∧ c3 % 2 = 1) ∧
      ¬ (c1 % 2 = 1 ∧ c2 % 2 = 1) ∧ ¬ (c1 % 2 = 1 ∧ c3 % 2 = 1) ∧
      ¬ (c2 % 2 = 1 ∧ c3 % 2 = 1) := by
  have s0 := CDRBicolour.KBicolor.nat_sq_mod_four c0
  have s1 := CDRBicolour.KBicolor.nat_sq_mod_four c1
  have s2 := CDRBicolour.KBicolor.nat_sq_mod_four c2
  have s3 := CDRBicolour.KBicolor.nat_sq_mod_four c3
  simp only [sq] at h
  generalize c0 * c0 = t0 at s0 h
  generalize c1 * c1 = t1 at s1 h
  generalize c2 * c2 = t2 at s2 h
  generalize c3 * c3 = t3 at s3 h
  omega

/-! ### A square-root estimate -/

theorem sqrt_ratio_close {N m v K : ℝ} (hm : 0 < m) (hv : 0 < v) (hN : 0 ≤ N)
    (h : |N - m * v ^ 2| ≤ K * v) :
    |Real.sqrt N / Real.sqrt m - v| ≤ K / m := by
  set s := Real.sqrt N with hs
  set t := Real.sqrt m with ht
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 < t := Real.sqrt_pos.2 hm
  have hss : s ^ 2 = N := Real.sq_sqrt hN
  have htt : t ^ 2 = m := Real.sq_sqrt hm.le
  have hden : 0 < s + v * t := by positivity
  have e : s - v * t = (N - m * v ^ 2) / (s + v * t) := by
    rw [eq_div_iff hden.ne', ← hss, ← htt]; ring
  have h1 : |s - v * t| ≤ K / t := by
    rw [e, abs_div, abs_of_pos hden, div_le_div_iff₀ hden ht0]
    have hK : 0 ≤ K := by
      have := abs_nonneg (N - m * v ^ 2); nlinarith
    calc |N - m * v ^ 2| * t ≤ K * v * t := mul_le_mul_of_nonneg_right h ht0.le
      _ ≤ K * (s + v * t) := by nlinarith
  have e2 : s / t - v = (s - v * t) / t := by field_simp
  rw [e2, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
  calc |s - v * t| ≤ K / t := h1
    _ = K / m * t := by rw [← htt]; field_simp

/-! ### Splitting sums over `Fin k` -/

theorem sum_split4 {k : ℕ} (hk : 4 ≤ k) {M : Type*} [AddCommMonoid M] (g : Fin k → M) :
    ∑ X, g X = g ⟨0, by omega⟩ + g ⟨1, by omega⟩ + g ⟨2, by omega⟩ + g ⟨3, by omega⟩ +
      ∑ X ∈ univ.filter (fun X : Fin k => 4 ≤ X.val), g X := by
  rw [← sum_filter_add_sum_filter_not univ (fun X : Fin k => 4 ≤ X.val), add_comm]
  congr 1
  have : univ.filter (fun X : Fin k => ¬ 4 ≤ X.val) =
      {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩} := by
    ext X
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff]
    omega
  rw [this, sum_insert (by simp [Fin.ext_iff]), sum_insert (by simp [Fin.ext_iff]),
    sum_insert (by simp [Fin.ext_iff]), sum_singleton]
  simp only [add_assoc]

end CDRBicolour.PaperIII
