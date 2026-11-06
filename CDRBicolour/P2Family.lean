/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Profile

/-!
# The last prime family `P2` (L181–L184): parameters and every arithmetic fact used

`y = 6k+3`, `a = y(y+1)/3 = 12k²+14k+4`, `b = a+2`, `c = a+y+2 = 12k²+20k+9`,
`n = y²+2y+4 = 36k²+48k+19`.  The construction works at `y ≥ 33`, i.e. `k ≥ 5`.

Derived quantities of L182–L184:
`N = c-1` (palette `C - w`), `K₀ = (a-y+1)/2`, `r = (y-1)/2`, `s = y-1` (degree of the root `w`).

Every identity/inequality quoted in the candidate proof is stated and proved here, so the
graph-theoretic layers only cite these lemmas.  All proofs are `ring`/`nlinarith`.
-/

@[expose] public section

namespace CDRBicolour.P2

/-- Parameters as integer polynomials in `k`. -/
def y (k : ℤ) : ℤ := 6 * k + 3
def a (k : ℤ) : ℤ := 12 * k ^ 2 + 14 * k + 4
def b (k : ℤ) : ℤ := a k + 2
def c (k : ℤ) : ℤ := 12 * k ^ 2 + 20 * k + 9
def n (k : ℤ) : ℤ := 36 * k ^ 2 + 48 * k + 19
def N (k : ℤ) : ℤ := c k - 1
def K₀ (k : ℤ) : ℤ := 6 * k ^ 2 + 4 * k + 1
def r (k : ℤ) : ℤ := 3 * k + 1
def s (k : ℤ) : ℤ := y k - 1

section Identities
variable (k : ℤ)

theorem three_mul_a : 3 * a k = y k * (y k + 1) := by unfold a y; ring
theorem c_eq : c k = a k + y k + 2 := by unfold c a y; ring
theorem n_eq_sum : n k = a k + b k + c k := by unfold n b a c; ring
theorem n_eq_y : n k = y k ^ 2 + 2 * y k + 4 := by unfold n y; ring

/-- The profile satisfies the quadratic CDR identity. -/
theorem quadratic_identity :
    a k ^ 2 + b k ^ 2 + c k ^ 2 - a k * b k - a k * c k - b k * c k = a k + b k + c k := by
  unfold b a c; ring

/-- `n ≡ 1 (mod 6)`. -/
theorem n_eq_six_mul_add_one : n k = 6 * (6 * k ^ 2 + 8 * k + 3) + 1 := by unfold n; ring

/-- `a` is even and `c` is odd. -/
theorem a_eq_two_mul : a k = 2 * (6 * k ^ 2 + 7 * k + 2) := by unfold a; ring
theorem c_eq_two_mul_add_one : c k = 2 * (6 * k ^ 2 + 10 * k + 4) + 1 := by unfold c; ring

/-- L182: the BBC graph has `(a²-a+2)/2 = N·K₀ - r` edges. -/
theorem bbc_edges : 2 * (N k * K₀ k - r k) = a k ^ 2 - a k + 2 := by
  unfold N K₀ r a c; ring

/-- L182: AAB/ABB counts, `Σ ν_j = 4a` with four rows `ν = 2` and `a-2` rows `ν = 4`. -/
theorem nu_sum : 4 * 2 + (a k - 2) * 4 = 4 * a k := by ring

/-- L183/L184: deficits at the root, `a - s = 2K₀`, and `s = 2r`. -/
theorem root_deficit : a k - s k = 2 * K₀ k := by unfold a s y K₀; ring
theorem s_eq_two_r : s k = 2 * r k := by unfold s y r; ring

/-- L182: the residual `F` has exactly `a(c-1)/2` edges (degree sum). -/
theorem residual_degree_sum : s k + (a k - 2) * r k + a k * (N k - r k) = a k * (c k - 1) := by
  unfold s y a r N c; ring

/-- L183: `e(H - v) - a(N-2)/2 = a - s - deg_H v`; with `deg_H v ≥ a - 3` this is `≤ 4 - y`. -/
theorem no_overfull_H_minus_v (d : ℤ) (hd : a k - 3 ≤ d) : a k - s k - d ≤ 4 - y k := by
  unfold s; linarith

end Identities

section Inequalities
variable {k : ℤ}

/-- L182 (Hall for the star partners): a `k'`-row set with `≤ k'-1` neighbours would give
`k' + y ≤ 5`. -/
theorem hall_star (k' : ℤ)
    (h : k' * (y k + 4) - 8 ≤ (k' - 1) * (y k + 3)) : k' + y k ≤ 5 := by
  nlinarith

/-- L182: `N - 6(y+3) = (y-17)(y+3)/3 ≥ 0` (hypothesis `N ≥ 6ρ` of L181, `ρ = y+3`). -/
theorem star_budget_identity (k : ℤ) : 3 * (N k - 6 * (y k + 3)) = (y k - 17) * (y k + 3) := by
  unfold N c y; ring

theorem star_budget (hk : 3 ≤ k) : 6 * (y k + 3) ≤ N k := by
  have h := star_budget_identity k
  have : 0 ≤ (y k - 17) * (y k + 3) := by unfold y; nlinarith
  linarith

/-- L183: Plantholt density, `10(a-2) - 9N = (y-29)(y+3)/3 ≥ 0`. -/
theorem plantholt_density_identity (k : ℤ) :
    3 * (10 * (a k - 2) - 9 * N k) = (y k - 29) * (y k + 3) := by
  unfold a N c y; ring

theorem plantholt_density (hk : 5 ≤ k) : 9 * N k ≤ 10 * (a k - 2) := by
  have h := plantholt_density_identity k
  have : 0 ≤ (y k - 29) * (y k + 3) := by unfold y; nlinarith
  linarith

/-- The square form of Plantholt's condition `δ+1 ≥ (√7/3)·N` for `δ+1 ≥ a-2`:
`7·N² ≤ 9·(a-2)²` (no real square roots needed). -/
theorem plantholt_sq (hk : 5 ≤ k) : 7 * N k ^ 2 ≤ 9 * (a k - 2) ^ 2 := by
  have h := plantholt_density hk
  have hN : 0 ≤ N k := by unfold N c; nlinarith
  nlinarith

/-- `δ(H) ≥ a - 3 > N/2` (hypothesis of Plantholt's structural Lemma 1.3). -/
theorem half_lt_min_degree (hk : 5 ≤ k) : N k < 2 * (a k - 3) := by
  have h := plantholt_density hk
  have ha : 5 ≤ a k := by unfold a; nlinarith
  linarith

/-- L183: CCJS margin, `4a - 7s - (3c - 17) = (y-2)(y-27)/3 ≥ 0`. -/
theorem ccjs_margin_identity (k : ℤ) :
    3 * (4 * a k - 7 * s k - (3 * c k - 17)) = (y k - 2) * (y k - 27) := by
  unfold a s c y; ring

theorem ccjs_margin (hk : 5 ≤ k) : 3 * c k - 17 ≤ 4 * a k - 7 * s k := by
  have h := ccjs_margin_identity k
  have : 0 ≤ (y k - 2) * (y k - 27) := by unfold y; nlinarith
  linarith

/-- `a ≥ y + 4`. -/
theorem y_add_four_le_a (hk : 1 ≤ k) : y k + 4 ≤ a k := by unfold y a; nlinarith

/-- L183: odd sets `U ∋ w` with `|U| > a`: the excess `t(2t+3-a)` is `≤ 0` when `2t ≤ y+1`. -/
theorem overfull_excess_nonpos (hk : 1 ≤ k) {t : ℤ} (ht0 : 0 ≤ t) (ht : 2 * t ≤ y k + 1) :
    t * (2 * t + 3 - a k) ≤ 0 := by
  have := y_add_four_le_a hk
  have h2 : 2 * t + 3 - a k ≤ 0 := by linarith
  nlinarith

/-- L183: complement bound used in the overfull exclusion,
`-a t + 2|X ∩ P| + e(F[X]) ≤ t(2t+3-a)` when `|X ∩ P| ≤ 2t` and `e(F[X]) ≤ t(2t-1)`. -/
theorem overfull_complement_bound (t p e : ℤ) (hp : p ≤ 2 * t) (he : e ≤ t * (2 * t - 1)) :
    -(a k) * t + 2 * p + e ≤ t * (2 * t + 3 - a k) := by
  nlinarith

end Inequalities

end CDRBicolour.P2
