/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Base.Cover
public import CDRBicolour.Master.L168

/-!
# The CDR theorem with the finite base reconstructed

`cdr_conjecture_of_branches`: the finite base is no longer a hypothesis.  It is
`base_below5059` (descent L165, uniform branches at their actual thresholds and 49 explicit
witnesses).  The branch statements above `5059` follow from the equitable master criterion
(`Master.eqMaster_realises`, no external hypothesis: Chetwynd–Hilton 1985, constant `6/7`) through bounds on
`⌊E/B⌋`, `E = A(A-1)/2` (`eqMasterHyp_of_bounds`):

* `branchL168_of`: `n ≥ 5059` forces `c - b ≥ 17` in the family `b - a = 4`, realised by
  `branchL168y_of` (roles `(a, c, b)`, vertex-distinguishing stage 2: BKLS + Rudašová–Soták);
* `branchL160_of`: gap `c - b ≥ 2` by the master criterion with roles `(a, b, c)`, with the
  cyclic stage 1 when `b = a + 1` (`branchL157x1_of`); gaps `1` and `0` by the master criterion;
* `bigSquares_of`: the squares `E(p)` by the gap-`0` case;
* `branchL161_of`: roles `(A, B, C) = (a, c, b)`.
-/

@[expose] public section

namespace CDRBicolour

open CDRBicolour.Base

theorem branchL168_of (h : BranchL168y) : BranchL168 := by
  intro a b c hadm hab hbc hc hb h5
  refine h a b c hadm hab hbc hc hb ?_
  have hg := order_gaps hadm hab hbc
  rw [show b - a = 4 by omega] at hg
  by_contra hlt; push_neg at hlt
  have hy : c - b ≤ 16 := by omega
  have : (c - b) ^ 2 ≤ 16 ^ 2 := Nat.pow_le_pow_left hy 2
  omega

theorem sq_mod_two (x : ℕ) : (x * x) % 2 = x % 2 := by
  rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> ring_nf <;> omega

/-- Bounds `k₁ ≤ ⌊E/B⌋ ≤ k₀` (`E = A(A-1)/2`) suffice for the equitable master hypotheses. -/
theorem eqMasterHyp_of_bounds {A B C k₀ k₁ : ℕ}
    (h1 : C % 2 = 0) (h2 : A < C) (h3 : A < B) (h4 : (B - A) % 2 = 1) (h5 : 3 ≤ B - A)
    (h6 : 6 * (C - A - 1) ≤ C) (h7 : 6 * C ≤ 7 * A)
    (hk₁ : 2 * k₁ * B ≤ A * (A - 1)) (hk₀ : A * (A - 1) < 2 * (k₀ + 1) * B)
    (hhi : 6 * (A - 2 * k₁) ≤ B) (hlo : B + 5 ≤ A - 2 * k₀ + C) : Master.EqMasterHyp A B C := by
  have hE2 : 2 * (A * (A - 1) / 2) = A * (A - 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self A)
  have hKB : A * (A - 1) / 2 / B * B ≤ A * (A - 1) / 2 := Nat.div_mul_le_self _ _
  have hKB' : A * (A - 1) / 2 < (A * (A - 1) / 2 / B + 1) * B := by
    have := Nat.div_add_mod (A * (A - 1) / 2) B
    have := Nat.mod_lt (A * (A - 1) / 2) (by omega : 0 < B)
    nlinarith
  unfold Master.EqMasterHyp
  generalize A * (A - 1) / 2 / B = K at hKB hKB' ⊢
  generalize A * (A - 1) / 2 = E at hKB hKB' hE2
  have hK1 : k₁ < K + 1 := Nat.lt_of_mul_lt_mul_right (a := B) (by nlinarith)
  have hK0 : K < k₀ + 1 := Nat.lt_of_mul_lt_mul_right (a := B) (by nlinarith)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, by omega, by omega⟩

/-- `2k(A+t) ≤ A(A-1)` when `A = t + δ + 2k`, `δ ≥ 1`. -/
theorem hk1_gen (t δ k : ℕ) (hδ : 1 ≤ δ) :
    2 * k * (t + δ + 2 * k + t) ≤ (t + δ + 2 * k) * (t + δ + 2 * k - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, δ = e + 1 := ⟨δ - 1, by omega⟩
  rw [show t + (e + 1) + 2 * k - 1 = t + e + 2 * k by omega]
  nlinarith

/-! ### L160 -/

/-- Gap `y = 1` of L160 via the equitable master criterion. -/
theorem master_y1 {a b c : ℕ}
    (hadm : AdmissibleProfile a b c) (hab : a ≤ b) (hc : c = b + 1) (hce : c % 2 = 0)
    (h5 : 5059 ≤ a + b + c) : Realises a b c := by
  have hg := order_gaps hadm hab (by omega)
  obtain ⟨x, hx⟩ : ∃ x, b = a + x := ⟨b - a, by omega⟩
  rw [show b - a = x by omega, show c - b = 1 by omega, sq, sq] at hg
  have h3a : 3 * a + x = x * x := by omega
  have hx71 : 71 ≤ x := by
    by_contra hlt; push Not at hlt
    have : x * x ≤ 70 * 70 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hxx := sq_mod_two x
  have hxx71 : 71 * x ≤ x * x := Nat.mul_le_mul_right x hx71
  have ha2 : a % 2 = 0 := by omega
  have hx2 : x % 2 = 1 := by omega
  obtain ⟨k, hk⟩ : ∃ k, a = x + 1 + 2 * k := ⟨(a - x - 1) / 2, by omega⟩
  have h6k : 6 * k + 4 * x + 3 = x * x := by omega
  refine Master.eqMaster_realises hadm (eqMasterHyp_of_bounds (k₁ := k) (k₀ := k + 1) hce
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_ (by omega) (by omega))
  · rw [hx, hk]; exact hk1_gen x 1 k le_rfl
  · rw [hx, hk, show x + 1 + 2 * k - 1 = x + 2 * k by omega]
    nlinarith

/-- Gap `y = 0` (squares) via the equitable master criterion. -/
theorem master_y0 {a b c : ℕ}
    (hadm : AdmissibleProfile a b c) (hab : a ≤ b) (hc : c = b) (hce : c % 2 = 0)
    (hx72 : 72 ≤ b - a) : Realises a b c := by
  have hg := order_gaps hadm hab (by omega)
  have hm := hadm.2.2.2.1
  obtain ⟨x, hx⟩ : ∃ x, b = a + x := ⟨b - a, by omega⟩
  rw [show b - a = x by omega, show c - b = 0 by omega, sq, sq] at hg
  have h3a : 3 * a + 2 * x = x * x := by omega
  have hxx := sq_mod_two x
  have hxx72 : 72 * x ≤ x * x := Nat.mul_le_mul_right x (by omega)
  have hx2 : x % 2 = 1 := by omega
  have ha2 : a % 2 = 1 := by omega
  obtain ⟨k, hk⟩ : ∃ k, a = x + 2 + 2 * k := ⟨(a - x - 2) / 2, by omega⟩
  have h6k : 6 * k + 5 * x + 6 = x * x := by omega
  refine Master.eqMaster_realises hadm (eqMasterHyp_of_bounds (k₁ := k) (k₀ := k + 2) hce
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_ (by omega) (by omega))
  · rw [hx, hk]; exact hk1_gen x 2 k (by norm_num)
  · rw [hx, hk, show x + 2 + 2 * k - 1 = x + 1 + 2 * k by omega]
    nlinarith

/-- L157 family, `a` even (`a = x + 1 + 2k`): `RHS − LHS = x² + x + 2xy + 2y² − 2y > 0`. -/
theorem l157_even (x y k : ℤ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : 6 * k + 5 * x + y + 3 = x * x + x * y + y * y) :
    (x + 1 + 2 * k) * (x + 2 * k) < 2 * (k + 2 + 1) * (x + 1 + 2 * k + x) := by
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ x by linarith) (show (0 : ℤ) ≤ y by linarith),
    mul_nonneg (show (0 : ℤ) ≤ y - 1 by linarith) (show (0 : ℤ) ≤ y by linarith)]

/-- L157 family, `a` odd (`a = x + 2 + 2k`): `3(RHS − LHS) = 2x² + 5xy + 5y² + 2x − 5y > 0`. -/
theorem l157_odd (x y k : ℤ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : 6 * k + 5 * x + y + 6 = x * x + x * y + y * y) :
    (x + 2 + 2 * k) * (x + 1 + 2 * k) < 2 * (k + 2 + 1) * (x + 2 + 2 * k + x) := by
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ x by linarith) (show (0 : ℤ) ≤ y by linarith),
    mul_nonneg (show (0 : ℤ) ≤ y - 1 by linarith) (show (0 : ℤ) ≤ y by linarith)]

theorem l161_big (x y a : ℕ) (h3 : 3 * a + 2 * x + y = x * x + x * y + y * y)
    (ht : 72 ≤ x + y) : 17 * (x + y) ≤ a := by
  have h4 : 3 * ((x + y) * (x + y)) ≤ 4 * (x * x + x * y + y * y) := by
    nlinarith [sq_nonneg ((x : ℤ) - y)]
  have ht2 : 72 * (x + y) ≤ (x + y) * (x + y) := Nat.mul_le_mul_right _ ht
  omega

/-- Even largest class, `c - b ≥ 2`, `b ≠ a + 1`, `n ≥ 5059`: the equitable master criterion
with roles `(A, B, C) = (a, b, c)` (`b - a` is odd since `c` is even). -/
theorem master_l157 {a b c : ℕ}
    (hadm : AdmissibleProfile a b c) (hab : a ≤ b) (hbc : b ≤ c) (hce : c % 2 = 0)
    (hy2 : b + 2 ≤ c) (hx1 : b ≠ a + 1) (h5 : 5059 ≤ a + b + c) : Realises a b c := by
  have hg := order_gaps hadm hab hbc
  have hm := hadm.2.2.2.1
  obtain ⟨x, hx⟩ : ∃ x, b = a + x := ⟨b - a, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y, c = b + y := ⟨c - b, by omega⟩
  rw [show b - a = x by omega, show c - b = y by omega, sq, sq] at hg
  have h3 : 3 * a + 2 * x + y = x * x + x * y + y * y := by omega
  have hx2 : x % 2 = 1 := by omega
  have ht72 : 72 ≤ x + y := by
    by_contra hlt; push Not at hlt
    have h1 : (x + y) * (x + y) ≤ 71 * 71 := Nat.mul_le_mul (by omega) (by omega)
    have h2 : x * x + x * y + y * y ≤ (x + y) * (x + y) := by nlinarith
    omega
  have hbig := l161_big x y a h3 ht72
  have h3z : (3 : ℤ) * a + 2 * x + y = x * x + x * y + y * y := by exact_mod_cast h3
  refine Master.eqMaster_realises hadm ?_
  rcases Nat.even_or_odd a with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨k, hk⟩ : ∃ k, a = x + 1 + 2 * k := ⟨(a - x - 1) / 2, by omega⟩
    refine eqMasterHyp_of_bounds (k₁ := k) (k₀ := k + 2) hce (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) ?_ ?_ (by omega) (by omega)
    · rw [hx, hk]; exact hk1_gen x 1 k le_rfl
    · rw [hx, hk, show x + 1 + 2 * k - 1 = x + 2 * k by omega]
      have hkz : (a : ℤ) = x + 1 + 2 * k := by exact_mod_cast hk
      have : ((x + 1 + 2 * k) * (x + 2 * k) : ℤ) < 2 * (k + 2 + 1) * (x + 1 + 2 * k + x) :=
        l157_even x y k (by exact_mod_cast (show 1 ≤ x by omega))
          (by exact_mod_cast (show 1 ≤ y by omega)) (by rw [hkz] at h3z; linarith)
      exact_mod_cast this
  · obtain ⟨k, hk⟩ : ∃ k, a = x + 2 + 2 * k := ⟨(a - x - 2) / 2, by omega⟩
    refine eqMasterHyp_of_bounds (k₁ := k) (k₀ := k + 2) hce (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) ?_ ?_ (by omega) (by omega)
    · rw [hx, hk]; exact hk1_gen x 2 k (by norm_num)
    · rw [hx, hk, show x + 2 + 2 * k - 1 = x + 1 + 2 * k by omega]
      have hkz : (a : ℤ) = x + 2 + 2 * k := by exact_mod_cast hk
      have : ((x + 2 + 2 * k) * (x + 1 + 2 * k) : ℤ) < 2 * (k + 2 + 1) * (x + 2 + 2 * k + x) :=
        l157_odd x y k (by exact_mod_cast (show 1 ≤ x by omega))
          (by exact_mod_cast (show 1 ≤ y by omega)) (by rw [hkz] at h3z; linarith)
      exact_mod_cast this

/-- **L160** at orders `≥ 5059` from L157 and the master criterion. -/
theorem branchL160_of (h157 : BranchL157x1) :
    BranchL160 := by
  intro a b c hadm hab hbc hce h5
  by_cases hy2 : b + 2 ≤ c
  · by_cases hx1 : b = a + 1
    · refine h157 a b c hadm hab hbc hce hx1 hy2 (by omega) ?_
      have hg := order_gaps hadm hab hbc
      obtain ⟨y, hy⟩ : ∃ y, c = b + y := ⟨c - b, by omega⟩
      rw [show b - a = 1 by omega, show c - b = y by omega, sq, sq] at hg
      have h3 : 3 * a + 2 + y = 1 + y + y * y := by omega
      have hy40 : 40 ≤ y := by
        by_contra hlt; push Not at hlt
        have : y * y ≤ 39 * 39 := Nat.mul_le_mul (by omega) (by omega)
        omega
      have hyy : 40 * y ≤ y * y := Nat.mul_le_mul_right y hy40
      omega
    · exact master_l157 hadm hab hbc hce hy2 hx1 h5
  rcases (show c = b + 1 ∨ c = b by omega) with hc | hc
  · exact master_y1 hadm hab hc hce h5
  · refine master_y0 hadm hab hc hce ?_
    have hg := order_gaps hadm hab hbc
    rw [show c - b = 0 by omega, sq] at hg
    by_contra hlt; push Not at hlt
    have : (b - a) * (b - a) ≤ 71 * 71 := Nat.mul_le_mul (by omega) (by omega)
    simp at hg; omega

/-- The large squares `E(p)` from the master criterion. -/
theorem bigSquares_of : BigSquares := by
  intro p hp hp5 hp3 hbig a b c ha hb hc
  rw [hc]
  have hp6 : p % 6 = 5 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · omega
  have hp72 : 72 ≤ p := by
    by_contra hlt; push Not at hlt
    have : p * p ≤ 71 * 71 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hsum : a + b + b = p * p := by omega
  have hbap : b = a + p := by omega
  have hadm : AdmissibleProfile a b b := by
    have hpp : 72 * p ≤ p * p := Nat.mul_le_mul_right p hp72
    refine ⟨by omega, by omega, by omega, ?_, ?_, by omega, by omega, by omega⟩
    · left; rw [hsum, Nat.mul_mod, hp6]
    · have e1 : (3 : ℤ) * a + 2 * p = p * p := by exact_mod_cast ha
      rw [show (b : ℤ) = a + p by omega]; push_cast; nlinarith
  have hb2 : b % 2 = 0 := by
    obtain ⟨j, hj⟩ : 6 ∣ p + 1 := by omega
    have : 3 * b = 3 * (2 * (p * j)) := by rw [hb, show p * p + p = p * (p + 1) by ring, hj]; ring
    omega
  exact master_y0 hadm (by omega) rfl hb2 (by omega)

/-! ### L161 -/

/-- The `x = 6` bound of L161: `3·(RHS − LHS) = t² − 19t + 120 > 0`. -/
theorem l161_x6 (t k : ℤ) (h : 6 * k + 10 * t + 9 = t * t + 36) :
    (t + 1 + 2 * k) * (t + 2 * k) < 2 * (k + 1 + 1) * (t + 1 + 2 * k + t) := by
  nlinarith [sq_nonneg (2 * t - 19)]

/-- The `x ≥ 8` bound of L161: `RHS − LHS = (t − x)² + x² − 2x + 3t > 0`. -/
theorem l161_x8 (t k x : ℤ) (hx : 8 ≤ x) (ht : 0 ≤ t)
    (h : 6 * k + 4 * t + 3 + x * t + x = t * t + x * x) :
    (t + 1 + 2 * k) * (t + 2 * k) < 2 * (k + 2 + 1) * (t + 1 + 2 * k + t) := by
  nlinarith [sq_nonneg (t - x), mul_le_mul_of_nonneg_right hx (show (0 : ℤ) ≤ x by linarith)]

/-- **L161** at orders `≥ 5059` from the master criterion (roles `A = a`, `B = c`, `C = b`). -/
theorem branchL161_of : BranchL161 := by
  intro a b c hadm hab hbc hco hx6 h5
  obtain ⟨ha2, hb2⟩ := even_of_odd hadm hco
  have hg := order_gaps hadm hab hbc
  have hadm' : AdmissibleProfile a c b :=
    admissible_swap (admissible_rotate (admissible_rotate hadm))
  obtain ⟨x, hx⟩ : ∃ x, b = a + x := ⟨b - a, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y, c = b + y := ⟨c - b, by omega⟩
  rw [show b - a = x by omega, show c - b = y by omega, sq, sq] at hg
  have h3 : 3 * a + 2 * x + y = x * x + x * y + y * y := by omega
  have ht72 : 72 ≤ x + y := by
    by_contra hlt; push Not at hlt
    have h1 : (x + y) * (x + y) ≤ 71 * 71 := Nat.mul_le_mul (by omega) (by omega)
    have h2 : x * x + x * y + y * y ≤ (x + y) * (x + y) := by nlinarith
    omega
  have hbig := l161_big x y a h3 ht72
  obtain ⟨t, ht⟩ : ∃ t, t = x + y := ⟨_, rfl⟩
  have hy2 : y % 2 = 1 := by omega
  obtain ⟨k, hk⟩ : ∃ k, a = t + 1 + 2 * k := ⟨(a - t - 1) / 2, by omega⟩
  -- `3a = t² - xt + x² - x - t`
  have hkz : (6 * k + 4 * t + 3 + x * t + x : ℤ) = t * t + x * x := by
    have h3z : (3 : ℤ) * a + 2 * x + y = x * x + x * y + y * y := by exact_mod_cast h3
    have haz : (a : ℤ) = t + 1 + 2 * k := by exact_mod_cast hk
    have hyz : (y : ℤ) = t - x := by push_cast [ht]; ring
    rw [haz, hyz] at h3z; linear_combination h3z
  have hk1 : 2 * k * c ≤ a * (a - 1) := by
    rw [show c = a + t by omega, hk]; exact hk1_gen t 1 k le_rfl
  refine realises_swap23 (Master.eqMaster_realises hadm' ?_)
  rcases (show x = 6 ∨ 8 ≤ x by omega) with rfl | hx8
  · refine eqMasterHyp_of_bounds (k₁ := k) (k₀ := k + 1) hb2 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hk1 ?_ (by omega) (by omega)
    rw [show c = a + t by omega, hk, show t + 1 + 2 * k - 1 = t + 2 * k by omega]
    have : ((t + 1 + 2 * k) * (t + 2 * k) : ℤ) < 2 * (k + 1 + 1) * (t + 1 + 2 * k + t) :=
      l161_x6 t k (by push_cast at hkz; linarith)
    exact_mod_cast this
  · refine eqMasterHyp_of_bounds (k₁ := k) (k₀ := k + 2) hb2 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hk1 ?_ (by omega) (by omega)
    rw [show c = a + t by omega, hk, show t + 1 + 2 * k - 1 = t + 2 * k by omega]
    have : ((t + 1 + 2 * k) * (t + 2 * k) : ℤ) < 2 * (k + 2 + 1) * (t + 1 + 2 * k + t) :=
      l161_x8 t k x (by exact_mod_cast hx8) (by positivity) hkz
    exact_mod_cast this

/-- **L157, family `b = a + 1`**: the master criterion with the cyclic stage 1. -/
theorem branchL157x1_of : BranchL157x1 := by
  intro a b c hadm hab hbc hce hb hy2 h5 h67
  have hg := order_gaps hadm hab hbc
  obtain ⟨y, hy⟩ : ∃ y, c = b + y := ⟨c - b, by omega⟩
  rw [show b - a = 1 by omega, show c - b = y by omega, sq, sq] at hg
  have h3 : 3 * a + 2 + y = 1 + y + y * y := by omega
  have hy19 : 19 ≤ y := by
    by_contra hlt; push Not at hlt
    have : y * y ≤ 18 * y := Nat.mul_le_mul_right y (by omega)
    omega
  have hyy : 19 * y ≤ y * y := Nat.mul_le_mul_right y hy19
  exact Master.x1_realises hadm hb hce (by omega) (by omega) (by omega) (by omega)

/-- **L168, family `b = a + 4`, odd largest class**: roles `(a, c, b)`, vertex-distinguishing
stage 2 (BKLS + Rudašová–Soták). -/
theorem branchL168y_of
    (hBK : Master.BKLS_Corollary_12.{0}) (hRS : Master.RS_Theorem_3_1.{0}) : BranchL168y := by
  intro a b c hadm hab hbc hco hb hy43
  obtain ⟨ha2, hb2⟩ := even_of_odd hadm hco
  have hg := order_gaps hadm hab hbc
  obtain ⟨y, hy⟩ : ∃ y, c = b + y := ⟨c - b, by omega⟩
  rw [show b - a = 4 by omega, show c - b = y by omega, sq, sq] at hg
  have h3 : 3 * a = y * y + 3 * y + 8 := by omega
  have hadm' : AdmissibleProfile a c b :=
    admissible_swap (admissible_rotate (admissible_rotate hadm))
  exact realises_swap23 (Master.x4_core hBK hRS hadm' hb hy h3 (by omega) (by omega))

/-- **The CDR conjecture along the route, finite base reconstructed.** -/
theorem cdr_conjecture_of_branches
    (hBK : Master.BKLS_Corollary_12.{0}) (hRS : Master.RS_Theorem_3_1.{0}) : CDRConjecture :=
  cdr_conjecture_of_route
    (base_below5059 branchL157x1_of (branchL168y_of hBK hRS) bigSquares_of)
    (branchL160_of branchL157x1_of) branchL161_of
    (branchL168_of (branchL168y_of hBK hRS))

end CDRBicolour
