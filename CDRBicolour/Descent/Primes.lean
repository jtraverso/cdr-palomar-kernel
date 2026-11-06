/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Descent.Eisenstein
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.LinearCombination

/-!
# Rational primes in `ℤ[ω]`, elementarily (L165)

* `split_three`: `3 ∣ N z` gives `z = (1 - ω) w`.
* `inert_dvd`: a prime `p ≡ 2 (mod 3)` dividing `N z` divides both coordinates.
* `split_one`: a prime `p ≡ 1 (mod 3)` dividing `N z` gives `z = π w` with `N π = p`.

The last uses a root `r` of `x² + x + 1` in `ZMod p` (Cauchy's theorem in `(ZMod p)ˣ`), a short
vector `π` of the lattice `s + t r ≡ 0` (Thue's pigeonhole lemma), and the two evaluations
`ω ↦ r, r²`.
-/

@[expose] public section

namespace CDRBicolour.Descent

open Finset

/-- Evaluation `ω ↦ r`. -/
def ev {p : ℕ} (r : ZMod p) (x : ℤ × ℤ) : ZMod p := (x.1 : ZMod p) + x.2 * r

theorem ev_mul {p : ℕ} {r : ZMod p} (hr : r ^ 2 + r + 1 = 0) (x y : ℤ × ℤ) :
    ev r (emul x y) = ev r x * ev r y := by
  simp only [ev, emul]; push_cast; linear_combination (-(x.2 : ZMod p) * y.2) * hr

theorem ev_conj {p : ℕ} {r : ZMod p} (hr : r ^ 2 + r + 1 = 0) (x : ℤ × ℤ) :
    ev r (econj x) = ev (r ^ 2) x := by
  simp only [ev, econj]; push_cast; linear_combination (-(x.2 : ZMod p)) * hr

theorem root_sq {p : ℕ} {r : ZMod p} (hr : r ^ 2 + r + 1 = 0) : (r ^ 2) ^ 2 + r ^ 2 + 1 = 0 := by
  linear_combination (r ^ 2 - r + 1) * hr

theorem ev_sq_sq {p : ℕ} {r : ZMod p} (hr : r ^ 2 + r + 1 = 0) (x : ℤ × ℤ) :
    ev ((r ^ 2) ^ 2) x = ev r x := by
  simp only [ev]; congr 1; congr 1; linear_combination (r ^ 2 - r) * hr

theorem ev_norm {p : ℕ} {r : ZMod p} (hr : r ^ 2 + r + 1 = 0) (x : ℤ × ℤ) :
    ((enorm x : ℤ) : ZMod p) = ev r x * ev (r ^ 2) x := by
  simp only [ev, enorm]; push_cast
  linear_combination (-(x.1 : ZMod p) * x.2 + (x.2 : ZMod p) ^ 2 - (x.2 : ZMod p) ^ 2 * r) * hr

/-! ### The prime `3` -/

theorem split_three (z : ℤ × ℤ) (h : (3 : ℤ) ∣ enorm z) :
    ∃ w : ℤ × ℤ, z = emul (1, -1) w := by
  obtain ⟨u, v⟩ := z
  have hsq : (3 : ℤ) ∣ (u + v) ^ 2 := by
    have : (u + v) ^ 2 = enorm (u, v) + 3 * (u * v) := by simp only [enorm]; ring
    rw [this]; exact dvd_add h (dvd_mul_right _ _)
  have h3 : (3 : ℤ) ∣ u + v := Int.prime_three.dvd_of_dvd_pow hsq
  obtain ⟨k, hk⟩ := h3
  refine ⟨(u - k, k), ?_⟩
  simp only [emul, Prod.mk.injEq]; constructor <;> linarith

/-! ### Inert primes -/

theorem inert_dvd {p : ℕ} [hp : Fact p.Prime] (hp3 : p % 3 = 2) (z : ℤ × ℤ)
    (h : (p : ℤ) ∣ enorm z) : (p : ℤ) ∣ z.1 ∧ (p : ℤ) ∣ z.2 := by
  obtain ⟨u, v⟩ := z
  have hN : ((enorm (u, v) : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
  simp only [enorm] at hN; push_cast at hN
  by_cases hv : (v : ZMod p) = 0
  · have hu : (u : ZMod p) ^ 2 = 0 := by rw [hv] at hN; simpa using hN
    have hu' : (u : ZMod p) = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hu
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hu', (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hv⟩
  · exfalso
    set r : ZMod p := -(u : ZMod p) / v
    have hr : r ^ 2 + r + 1 = 0 := by
      have : r ^ 2 + r + 1 = ((u : ZMod p) ^ 2 - u * v + v ^ 2) / v ^ 2 := by
        simp only [r]; field_simp; ring
      rw [this, hN, zero_div]
    have hr3 : r ^ 3 = 1 := by linear_combination (r - 1) * hr
    have hr0 : r ≠ 0 := by rintro h0; rw [h0] at hr3; simp at hr3
    have hr1 : r ≠ 1 := by
      rintro h1; rw [h1] at hr
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hr
      rw [ZMod.natCast_eq_zero_iff] at h3
      have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 h3
      omega
    let ru : (ZMod p)ˣ := Units.mk0 r hr0
    have hord : orderOf ru = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      apply orderOf_eq_prime
      · ext; simp [ru, hr3]
      · intro h1; apply hr1; have := congrArg Units.val h1; simpa [ru] using this
    have hdvd := ZMod.orderOf_units_dvd_card_sub_one ru
    rw [hord] at hdvd
    have hp2 := hp.out.two_le
    omega

/-! ### Split primes -/

/-- A root of `x² + x + 1` modulo a prime `p ≡ 1 (mod 3)` (Cauchy's theorem). -/
theorem exists_root {p : ℕ} [hp : Fact p.Prime] (hp3 : p % 3 = 1) :
    ∃ r : ZMod p, r ^ 2 + r + 1 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp.out]; omega
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hcard
  have hg3 : (g : ZMod p) ^ 3 = 1 := by
    have := pow_orderOf_eq_one g; rw [hg] at this
    have := congrArg Units.val this; simpa using this
  have hg1 : (g : ZMod p) ≠ 1 := by
    intro h; have : g = 1 := Units.ext (by simpa using h)
    rw [this, orderOf_one] at hg; omega
  refine ⟨g, ?_⟩
  have : ((g : ZMod p) - 1) * ((g : ZMod p) ^ 2 + g + 1) = 0 := by linear_combination hg3
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hg1
  · exact h

theorem parity_norm (s t : ℤ) (h : (2 : ℤ) ∣ enorm (s, t)) : (2 : ℤ) ∣ s ∧ (2 : ℤ) ∣ t := by
  have key : ∀ a b : ZMod 2, a ^ 2 - a * b + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide
  have hN : ((enorm (s, t) : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
  simp only [enorm] at hN; push_cast at hN
  obtain ⟨h1, h2⟩ := key _ _ hN
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2⟩

/-- **Thue.** A short vector of the lattice `s + t r ≡ 0 (mod p)` has norm `p`. -/
theorem thue {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {r : ZMod p} (hr : r ^ 2 + r + 1 = 0) :
    ∃ s t : ℤ, enorm (s, t) = p ∧ ev r (s, t) = 0 := by
  classical
  set k := Nat.sqrt p with hk
  have hk1 : p < (k + 1) * (k + 1) := Nat.lt_succ_sqrt p
  have hk2 : k * k ≤ p := Nat.sqrt_le p
  have hk3 : k * k < p := by
    rcases lt_or_eq_of_le hk2 with h | h
    · exact h
    · exfalso
      have hdvd : k ∣ p := ⟨k, h.symm⟩
      rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | h1
      · rw [h1] at h; omega
      · rw [h1] at h; nlinarith
  let f : Fin (k + 1) × Fin (k + 1) → ZMod p := fun ij => (ij.1 : ℕ) + ((ij.2 : ℕ) : ZMod p) * r
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin (k + 1) × Fin (k + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin]; exact hk1
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  obtain ⟨s, hs0⟩ : ∃ s : ℤ, s = ((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨t, ht0⟩ : ∃ t : ℤ, t = ((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ) := ⟨_, rfl⟩
  have hev : ev r (s, t) = 0 := by
    simp only [ev, f] at hf ⊢; rw [hs0, ht0]; push_cast; linear_combination hf
  have hx1 := x.1.2
  have hy1 := y.1.2
  have hx2 := x.2.2
  have hy2 := y.2.2
  have hsl : -(k : ℤ) ≤ s ∧ s ≤ k := by rw [hs0]; constructor <;> omega
  have htl : -(k : ℤ) ≤ t ∧ t ≤ k := by rw [ht0]; constructor <;> omega
  have hs : s ^ 2 ≤ (k : ℤ) ^ 2 := by nlinarith
  have ht : t ^ 2 ≤ (k : ℤ) ^ 2 := by nlinarith
  have hne : s ≠ 0 ∨ t ≠ 0 := by
    by_contra h; push_neg at h
    obtain ⟨h1, h2⟩ := h
    apply hxy
    have e1 : ((x.1 : ℕ) : ℤ) = ((y.1 : ℕ) : ℤ) := by omega
    have e2 : ((x.2 : ℕ) : ℤ) = ((y.2 : ℕ) : ℤ) := by omega
    exact Prod.ext (Fin.ext (by exact_mod_cast e1)) (Fin.ext (by exact_mod_cast e2))
  have hpos : 0 < enorm (s, t) := by
    simp only [enorm]
    rcases hne with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (s - 2 * t), sq_nonneg t]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (2 * s - t), sq_nonneg s]
  have hle : enorm (s, t) < 3 * p := by
    simp only [enorm]
    have : (k : ℤ) ^ 2 < p := by exact_mod_cast (show k ^ 2 < p by rw [sq]; exact hk3)
    nlinarith [sq_nonneg (s + t)]
  have hdvd : (p : ℤ) ∣ enorm (s, t) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ev_norm hr, hev, zero_mul]
  obtain ⟨q, hq⟩ := hdvd
  have hq1 : 0 < q := by
    have : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    nlinarith
  have hq2 : q < 3 := by
    have : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    nlinarith
  refine ⟨s, t, ?_, hev⟩
  rcases (show q = 1 ∨ q = 2 by omega) with rfl | rfl
  · rw [hq, mul_one]
  · exfalso
    obtain ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ := parity_norm s t ⟨p, by rw [hq]; ring⟩
    have h4 : enorm (s, t) = 4 * enorm (s', t') := by
      simp only [enorm, hs', ht']; ring
    rw [hq] at h4
    have : (2 : ℤ) ∣ p := ⟨enorm (s', t'), by linarith⟩
    have h2 : (2 : ℕ) ∣ p := by exact_mod_cast this
    rcases (Nat.dvd_prime hp.out).1 h2 with h | h <;> omega

/-- Division by a norm-`p` element vanishing at the same root. -/
theorem div_of_ev {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3) {r : ZMod p}
    (hr : r ^ 2 + r + 1 = 0) {π z : ℤ × ℤ} (hπ : enorm π = p) (hπr : ev r π = 0)
    (hzr : ev r z = 0) : ∃ w, z = emul π w := by
  set q := emul z (econj π) with hq
  have hrr : r ≠ r ^ 2 := by
    intro h
    have h1 : r * (1 - r) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h1 with h0 | h0
    · rw [h0] at hr; simp at hr
    · have : r = 1 := (sub_eq_zero.1 h0).symm
      rw [this] at hr
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination hr
      rw [ZMod.natCast_eq_zero_iff] at h3
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 h3)
  have h1 : ev r q = 0 := by rw [hq, ev_mul hr, hzr, zero_mul]
  have h2 : ev (r ^ 2) q = 0 := by
    rw [hq, ev_mul (root_sq hr), ev_conj (root_sq hr), ev_sq_sq hr, hπr, mul_zero]
  have hB : (q.2 : ZMod p) = 0 := by
    simp only [ev] at h1 h2
    have : (q.2 : ZMod p) * (r - r ^ 2) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hrr
  have hA : (q.1 : ZMod p) = 0 := by simp only [ev] at h1; rw [hB, zero_mul, add_zero] at h1; exact h1
  obtain ⟨A, hA'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hA
  obtain ⟨B, hB'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hB
  refine ⟨(A, B), ?_⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have key : emul π q = ((p : ℤ) * z.1, (p : ℤ) * z.2) := by
    rw [hq, emul_comm z, ← emul_assoc, emul_conj_self, hπ]
    simp only [emul]; ext <;> simp only <;> ring
  have key2 : emul π q = ((p : ℤ) * (emul π (A, B)).1, (p : ℤ) * (emul π (A, B)).2) := by
    have hq' : q = ((p : ℤ) * A, (p : ℤ) * B) := Prod.ext hA' hB'
    rw [hq']; simp only [emul]; ext <;> simp only <;> ring
  rw [key] at key2
  simp only [Prod.mk.injEq] at key2
  exact Prod.ext (mul_left_cancel₀ hp0 key2.1) (mul_left_cancel₀ hp0 key2.2)

/-- **Split primes.** -/
theorem split_one {p : ℕ} [hp : Fact p.Prime] (hp3 : p % 3 = 1) (z : ℤ × ℤ)
    (h : (p : ℤ) ∣ enorm z) : ∃ π w : ℤ × ℤ, enorm π = p ∧ z = emul π w := by
  have hp5 : 5 ≤ p := by
    have := hp.out.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
    · omega
    · omega
    · exact absurd hp.out (by rw [h]; decide)
    · exact h
  have hpne3 : p ≠ 3 := by omega
  obtain ⟨u, v⟩ := z
  have hN : ((enorm (u, v) : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
  by_cases hv : (v : ZMod p) = 0
  · -- `p` divides both coordinates
    simp only [enorm] at hN; push_cast at hN
    have hu : (u : ZMod p) = 0 := by
      rw [hv] at hN; exact pow_eq_zero_iff two_ne_zero |>.1 (by simpa using hN)
    obtain ⟨u', hu'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hu
    obtain ⟨v', hv'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hv
    obtain ⟨r, hr⟩ := exists_root hp3
    obtain ⟨s, t, hst, -⟩ := thue hp5 hr
    refine ⟨(s, t), emul (econj (s, t)) (u', v'), hst, ?_⟩
    rw [← emul_assoc, emul_conj_self, hst, hu', hv']
    simp only [emul]; ext <;> simp only <;> ring
  · set r : ZMod p := -(u : ZMod p) / v
    have hr : r ^ 2 + r + 1 = 0 := by
      simp only [enorm] at hN; push_cast at hN
      have : r ^ 2 + r + 1 = ((u : ZMod p) ^ 2 - u * v + v ^ 2) / v ^ 2 := by
        simp only [r]; field_simp; ring
      rw [this, hN, zero_div]
    have hzr : ev r (u, v) = 0 := by
      simp only [ev, r]; field_simp; ring
    obtain ⟨s, t, hst, hev⟩ := thue hp5 hr
    obtain ⟨w, hw⟩ := div_of_ev hpne3 hr hst hev hzr
    exact ⟨(s, t), w, hst, hw⟩

/-- The residue of a product. -/
theorem res_mul (x y : ℤ × ℤ) :
    ((emul x y).1 + (emul x y).2) % 3 = ((x.1 + x.2) * (y.1 + y.2)) % 3 := by
  simp only [emul]
  have : x.1 * y.1 - x.2 * y.2 + (x.1 * y.2 + x.2 * y.1 - x.2 * y.2) =
      (x.1 + x.2) * (y.1 + y.2) - 3 * (x.2 * y.2) := by ring
  rw [this]; omega

/-- The residue squared is the norm modulo `3`. -/
theorem res_sq (x : ℤ × ℤ) : ((x.1 + x.2) ^ 2 - enorm x) % 3 = 0 := by
  have : (x.1 + x.2) ^ 2 - enorm x = 3 * (x.1 * x.2) := by simp only [enorm]; ring
  rw [this]; omega

/-- A sign makes the residue equal to the norm modulo `3`. -/
theorem res_sign (x : ℤ × ℤ) :
    (x.1 + x.2 - enorm x) % 3 = 0 ∨ (-x.1 + -x.2 - enorm x) % 3 = 0 := by
  have h := res_sq x
  have hm : ((x.1 + x.2) ^ 2) % 3 = (((x.1 + x.2) % 3) * ((x.1 + x.2) % 3)) % 3 := by
    rw [sq, Int.mul_emod]
  have h3 : (x.1 + x.2) % 3 = 0 ∨ (x.1 + x.2) % 3 = 1 ∨ (x.1 + x.2) % 3 = 2 := by omega
  rcases h3 with h3 | h3 | h3 <;> rw [h3] at hm <;> norm_num at hm <;> omega

end CDRBicolour.Descent
