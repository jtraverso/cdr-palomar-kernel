/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Lift
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.IntervalCases

/-!
# Eisenstein encoding of profiles (L165)

`ℤ[ω]` (`ω² + ω + 1 = 0`) is modelled by pairs `(u, v) ↦ u + v ω` with the explicit product
`emul`, conjugation `econj` and norm `enorm (u, v) = u² - u v + v²`.

* `enc a b c = (a - c, b - c)`; for an admissible profile `enorm (enc a b c) = a + b + c`.
* `enc_product`: the CDR product (`realises_product`) has encoding `enc inner * conj (enc outer)`.
* `decode`: a pair of norm `m ≥ 3` with `u + v ≡ m (mod 3)` is the encoding of a unique
  nonnegative profile of order `m` (positive if `m ≥ 7`, balanced if `m ≥ 13`).
* `realises_of_factor`: if `z = zi · conj zo` with realised factor profiles (`zi` balanced),
  the profile of `z` is realised.
-/

@[expose] public section

namespace CDRBicolour.Descent

/-- Multiplication in `ℤ[ω]`. -/
def emul (p q : ℤ × ℤ) : ℤ × ℤ := (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1 - p.2 * q.2)

/-- Complex conjugation `ω ↦ ω² = -1 - ω`. -/
def econj (p : ℤ × ℤ) : ℤ × ℤ := (p.1 - p.2, -p.2)

/-- The norm `u² - u v + v²`. -/
def enorm (p : ℤ × ℤ) : ℤ := p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2

/-- Encoding of a profile. -/
def enc (a b c : ℕ) : ℤ × ℤ := ((a : ℤ) - c, (b : ℤ) - c)

theorem enorm_mul (p q : ℤ × ℤ) : enorm (emul p q) = enorm p * enorm q := by
  simp only [enorm, emul]; ring

theorem enorm_conj (p : ℤ × ℤ) : enorm (econj p) = enorm p := by
  simp only [enorm, econj]; ring

theorem emul_comm (p q : ℤ × ℤ) : emul p q = emul q p := by
  simp only [emul]; ext <;> simp only <;> ring

theorem emul_assoc (p q r : ℤ × ℤ) : emul (emul p q) r = emul p (emul q r) := by
  simp only [emul]; ext <;> simp only <;> ring

theorem econj_mul (p q : ℤ × ℤ) : econj (emul p q) = emul (econj p) (econj q) := by
  simp only [emul, econj]; ext <;> simp only <;> ring

theorem econj_econj (p : ℤ × ℤ) : econj (econj p) = p := by
  simp only [econj]; ext <;> simp only <;> ring

theorem emul_neg_neg (p q : ℤ × ℤ) : emul (-p.1, -p.2) (-q.1, -q.2) = emul p q := by
  simp only [emul]; ext <;> simp only <;> ring

theorem econj_neg (p : ℤ × ℤ) : econj (-p.1, -p.2) = (-(econj p).1, -(econj p).2) := by
  simp only [econj]; ext <;> simp only <;> ring

theorem emul_conj_self (p : ℤ × ℤ) : emul p (econj p) = (enorm p, 0) := by
  simp only [emul, econj, enorm]; ext <;> simp only <;> ring

theorem enorm_nonneg (p : ℤ × ℤ) : 0 ≤ enorm p := by
  simp only [enorm]; nlinarith [sq_nonneg (p.1 - p.2), sq_nonneg p.1, sq_nonneg p.2]

theorem enorm_enc (a b c : ℕ) :
    enorm (enc a b c) = (a : ℤ) ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c := by
  simp only [enorm, enc]; ring

/-- The product of profiles in encoding: `enc (product) = enc inner * conj (enc outer)`. -/
theorem enc_product (a b c x y z : ℕ) :
    enc (x * a + y * b + z * c) (x * b + y * c + z * a) (x * c + y * a + z * b) =
      emul (enc a b c) (econj (enc x y z)) := by
  simp only [enc, emul, econj]; push_cast; ext <;> simp only <;> ring

/-- A profile is determined by its encoding and its order. -/
theorem enc_inj {a b c a' b' c' : ℕ} (h : enc a b c = enc a' b' c')
    (hs : a + b + c = a' + b' + c') : a = a' ∧ b = b' ∧ c = c' := by
  simp only [enc, Prod.mk.injEq] at h
  omega

/-- Two coordinates bounded through the norm. -/
theorem sq_le_of_enorm (p : ℤ × ℤ) :
    (p.1 + p.2) ^ 2 ≤ 4 * enorm p ∧ (2 * p.1 - p.2) ^ 2 ≤ 4 * enorm p ∧
      (2 * p.2 - p.1) ^ 2 ≤ 4 * enorm p := by
  simp only [enorm]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (p.1 - p.2), sq_nonneg p.1, sq_nonneg p.2]

/-- **Decoding.** -/
theorem decode (p : ℤ × ℤ) (m : ℕ) (hm : enorm p = m) (hm3 : 3 ≤ m)
    (hres : ((p.1 + p.2 : ℤ) - m) % 3 = 0) :
    ∃ a b c : ℕ, a + b + c = m ∧ enc a b c = p ∧
      ((7 ≤ m) → 0 < a ∧ 0 < b ∧ 0 < c) ∧
      ((13 ≤ m) → 2 * a ≤ m ∧ 2 * b ≤ m ∧ 2 * c ≤ m) := by
  obtain ⟨u, v⟩ := p
  simp only at hres
  obtain ⟨h1, h2, h3⟩ := sq_le_of_enorm (u, v)
  simp only at h1 h2 h3
  rw [hm] at h1 h2 h3
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (m : ℤ) - u - v = 3 * k := ⟨((m : ℤ) - u - v) / 3, by omega⟩
  -- the three coordinates are `k + u`, `k + v`, `k`; all are nonnegative
  have hmz : (3 : ℤ) ≤ m := by exact_mod_cast hm3
  have hx1 : u + v ≤ m := by nlinarith
  have hx2 : v - 2 * u ≤ m := by nlinarith
  have hx3 : u - 2 * v ≤ m := by nlinarith
  have hk0 : 0 ≤ k := by omega
  have hku : 0 ≤ k + u := by omega
  have hkv : 0 ≤ k + v := by omega
  refine ⟨(k + u).toNat, (k + v).toNat, k.toNat, ?_, ?_, ?_, ?_⟩
  · omega
  · simp only [enc, Prod.mk.injEq]; omega
  · intro h7
    have h7' : (7 : ℤ) ≤ m := by exact_mod_cast h7
    have : u + v < m := by nlinarith
    have : v - 2 * u < m := by nlinarith
    have : u - 2 * v < m := by nlinarith
    omega
  · intro h13
    have h13' : (13 : ℤ) ≤ m := by exact_mod_cast h13
    -- `2 c ≤ m` iff `-2 (u + v) ≤ m`, etc.
    have key : ∀ x : ℤ, x ^ 2 ≤ 4 * m → (x - m) % 3 = 0 → -2 * x ≤ m := by
      intro x hx hx3
      by_contra hneg
      push_neg at hneg
      by_cases h16 : (16 : ℤ) ≤ m
      · nlinarith
      · have hxu : x ≤ -7 := by omega
        have hxl : -7 ≤ x := by nlinarith
        have hx7 : x = -7 := le_antisymm hxu hxl
        subst hx7
        omega
    have e1 := key (u + v) h1 (by omega)
    have e2 := key (v - 2 * u) (by nlinarith) (by omega)
    have e3 := key (u - 2 * v) (by nlinarith) (by omega)
    omega

/-- The residue of an encoded profile matches its order. -/
theorem enc_res (a b c : ℕ) : ((enc a b c).1 + (enc a b c).2 - ((a + b + c : ℕ) : ℤ)) % 3 = 0 := by
  simp only [enc]; push_cast; omega

/-- Norm-3 profiles are permutations of `(0, 1, 2)`. -/
theorem realises_norm3 {x y z : ℕ} (hs : x + y + z = 3)
    (hq : (x : ℤ) ^ 2 + y ^ 2 + z ^ 2 - x * y - x * z - y * z = 3) : Realises x y z := by
  have hx : x ≤ 3 := by omega
  have hy : y ≤ 3 := by omega
  have hz : z = 3 - x - y := by omega
  subst hz
  interval_cases x <;> interval_cases y <;>
    first
    | (exfalso; norm_num at hq; done)
    | exact realises_012
    | exact realises_rotate realises_012
    | exact realises_rotate (realises_rotate realises_012)
    | exact realises_swap realises_012
    | exact realises_swap (realises_rotate realises_012)
    | exact realises_swap (realises_rotate (realises_rotate realises_012))

/-- **Realisation of a factorisation.** If `z = zi * conj zo` where `zi` encodes a realised
balanced profile and `zo` a realised profile, the profile encoded by `z` is realised. -/
theorem realises_of_factor {a b c a₁ b₁ c₁ x y z : ℕ}
    (hz : enc a b c = emul (enc a₁ b₁ c₁) (econj (enc x y z)))
    (hn : a + b + c = (a₁ + b₁ + c₁) * (x + y + z))
    (h₁ : Realises a₁ b₁ c₁)
    (hbal : 2 * a₁ ≤ a₁ + b₁ + c₁ ∧ 2 * b₁ ≤ a₁ + b₁ + c₁ ∧ 2 * c₁ ≤ a₁ + b₁ + c₁)
    (h₂ : Realises x y z) : Realises a b c := by
  have hp := realises_product h₁ hbal h₂
  rw [← enc_product] at hz
  obtain ⟨ea, eb, ec⟩ := enc_inj hz (by rw [hn]; ring)
  rw [ea, eb, ec]; exact hp

end CDRBicolour.Descent
