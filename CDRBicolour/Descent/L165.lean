/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Descent.Primes
public import CDRBicolour.Profile

/-!
# L165: the composite-order descent

`descent_composite`: let `n > 49` be composite and assume every admissible profile of smaller
order is realised.  Then every admissible profile of order `n` is realised, given the
balanced square profiles `E(p) = (p(p-2)/3, p(p+1)/3, p(p+1)/3)` for primes `p ≡ 2 (mod 3)`
(these have even largest class and are realised by L160).

The profile is encoded as `z ∈ ℤ[ω]` with `N z = n` and factored `z = α β` with
* (i) `3 ∣ n`: `β = 1 - ω` (norm `3`, outer profile a permutation of `(0, 1, 2)`);
* (ii) an inert prime `p ≡ 2 (mod 3)` divides `n`: `α = p` (inner `E(p)`);
* (iii) a prime `p ≥ 13`, `p ≡ 1 (mod 3)` divides `n`: `N α = p`;
* (iv) otherwise `n = 7^k`, `k ≥ 3`: `N α = 49`.

The inner factor is balanced (order `≥ 13`), the outer one is realised by induction, and the CDR
product (`realises_of_factor`) realises the profile.
-/

@[expose] public section

namespace CDRBicolour.Descent

open Finset

/-- Residues modulo `3` in `ZMod 3`. -/
theorem mod3_iff (x : ℤ) : x % 3 = 0 ↔ ((x : ZMod 3) = 0) := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]; norm_num

/-- Residue `ρ(x) = x₁ + x₂` in `ZMod 3`. -/
def R3 (x : ℤ × ℤ) : ZMod 3 := ((x.1 + x.2 : ℤ) : ZMod 3)

theorem R3_mul (x y : ℤ × ℤ) : R3 (emul x y) = R3 x * R3 y := by
  simp only [R3, emul]; push_cast
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination (-(x.2 : ZMod 3) * y.2) * h3

theorem R3_conj (x : ℤ × ℤ) : R3 (econj x) = R3 x := by
  simp only [R3, econj]; push_cast
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination (-(x.2 : ZMod 3)) * h3

theorem R3_neg (x : ℤ × ℤ) : R3 (-x.1, -x.2) = -R3 x := by
  simp only [R3]; push_cast; ring

theorem R3_sq (x : ℤ × ℤ) : R3 x ^ 2 = ((enorm x : ℤ) : ZMod 3) := by
  simp only [R3, enorm]; push_cast
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination ((x.1 : ZMod 3) * x.2) * h3

theorem enorm_mod3 (x : ℤ × ℤ) : enorm x % 3 ≠ 2 := by
  intro h
  have h1 : ((enorm x : ℤ) : ZMod 3) = 2 := by
    have : enorm x = 3 * (enorm x / 3) + 2 := by omega
    rw [this]; push_cast
    have h3 : (3 : ZMod 3) = 0 := by decide
    rw [h3]; ring
  rw [← R3_sq] at h1
  have key : ∀ a : ZMod 3, a ^ 2 ≠ 2 := by decide
  exact key _ h1

theorem res_iff (x : ℤ × ℤ) (m : ℕ) : (x.1 + x.2 - m) % 3 = 0 ↔ R3 x = (m : ZMod 3) := by
  rw [mod3_iff, R3]; push_cast; rw [sub_eq_zero]

/-- Choice of signs so that both factors are encodings. -/
theorem factor_signs {z α β : ℤ × ℤ} {n m₁ m₂ : ℕ} (hz : z = emul α β)
    (hzres : (z.1 + z.2 - n) % 3 = 0) (hα : enorm α = m₁) (hβ : enorm β = m₂)
    (hn : n = m₁ * m₂) (hcase : m₁ % 3 = 1 ∨ m₂ % 3 = 0) :
    ∃ zi zo : ℤ × ℤ, z = emul zi (econj zo) ∧ enorm zi = m₁ ∧ enorm zo = m₂ ∧
      (zi.1 + zi.2 - m₁) % 3 = 0 ∧ (zo.1 + zo.2 - m₂) % 3 = 0 := by
  -- choose the sign of `α`
  obtain ⟨ε, hε, hzε, hαε⟩ : ∃ ε : ℤ × ℤ → ℤ × ℤ, (∀ x, enorm (ε x) = enorm x) ∧
      (emul (ε α) (ε β) = emul α β) ∧ (((ε α).1 + (ε α).2 - m₁) % 3 = 0) := by
    rcases res_sign α with h | h
    · exact ⟨id, fun _ => rfl, rfl, by rw [← hα]; exact h⟩
    · refine ⟨fun x => (-x.1, -x.2), fun x => by simp only [enorm]; ring,
        emul_neg_neg α β, by rw [← hα]; exact h⟩
  refine ⟨ε α, econj (ε β), by rw [econj_econj, hzε, hz], by rw [hε, hα],
    by rw [enorm_conj, hε, hβ], hαε, ?_⟩
  rw [res_iff, R3_conj]
  rw [res_iff] at hαε hzres
  have hprod : R3 z = R3 (ε α) * R3 (ε β) := by rw [hz, ← hzε, R3_mul]
  rcases hcase with h1 | h0
  · have hm1 : (m₁ : ZMod 3) = 1 := by
      have : m₁ = 3 * (m₁ / 3) + 1 := by omega
      rw [this]; push_cast
      have h3 : (3 : ZMod 3) = 0 := by decide
      rw [h3]; ring
    rw [hzres, hαε, hm1, one_mul, hn] at hprod
    rw [← hprod]; push_cast; rw [hm1, one_mul]
  · have hm2 : (m₂ : ZMod 3) = 0 := by
      have : m₂ = 3 * (m₂ / 3) := by omega
      rw [this]; push_cast
      have h3 : (3 : ZMod 3) = 0 := by decide
      rw [h3]; ring
    have hsq : R3 (ε β) ^ 2 = 0 := by
      rw [R3_sq, hε, hβ]; exact_mod_cast hm2
    have key : ∀ a : ZMod 3, a ^ 2 = 0 → a = 0 := by decide
    rw [key _ hsq, hm2]

/-- An encoded profile of admissible order is admissible. -/
theorem admissible_of_decoded {a b c m : ℕ} (hs : a + b + c = m)
    (hpos : 0 < a ∧ 0 < b ∧ 0 < c) (hq : enorm (enc a b c) = m) (hodd : m % 2 = 1)
    (h3 : m % 3 ≠ 2) (h9 : m ≠ 9) : AdmissibleProfile a b c := by
  rw [enorm_enc] at hq
  have hq' : (a : ℤ) ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c = a + b + c := by
    rw [hq]; exact_mod_cast hs.symm
  refine ⟨hpos.1, hpos.2.1, hpos.2.2, by omega, hq', ?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩
    have := two_two_forces_five (c := (c : ℤ)) (by exact_mod_cast hpos.2.2) (by push_cast at hq'; linarith)
    omega
  · rintro ⟨rfl, rfl⟩
    have := two_two_forces_five (c := (b : ℤ)) (by exact_mod_cast hpos.2.1) (by push_cast at hq'; linarith)
    omega
  · rintro ⟨rfl, rfl⟩
    have := two_two_forces_five (c := (a : ℤ)) (by exact_mod_cast hpos.1) (by push_cast at hq'; linarith)
    omega

/-- The induction hypothesis of the descent. -/
def SmallerRealised (n : ℕ) : Prop :=
  ∀ a b c, AdmissibleProfile a b c → a + b + c < n → Realises a b c

/-- **Realisation from a factorisation `z = α β`.** -/
theorem realise_from_factors {n : ℕ} (hIH : SmallerRealised n) {a b c : ℕ} (hn : a + b + c = n)
    {α β : ℤ × ℤ} (hz : enc a b c = emul α β) {m₁ m₂ : ℕ} (hα : enorm α = m₁)
    (hβ : enorm β = m₂) (hmn : n = m₁ * m₂) (hcase : m₁ % 3 = 1 ∨ m₂ % 3 = 0)
    (h₁ : 13 ≤ m₁) (h₁n : m₁ < n) (h₁odd : m₁ % 2 = 1) (h₁9 : m₁ ≠ 9)
    (h₂ : 7 ≤ m₂ ∨ m₂ = 3) (h₂n : m₂ < n) (h₂odd : m₂ % 2 = 1) (h₂9 : m₂ ≠ 9) :
    Realises a b c := by
  have hzres : ((enc a b c).1 + (enc a b c).2 - n) % 3 = 0 := by
    have := enc_res a b c; rw [hn] at this; exact this
  obtain ⟨zi, zo, hzz, hzi, hzo, hri, hro⟩ := factor_signs hz hzres hα hβ hmn hcase
  have hm₁3 : m₁ % 3 ≠ 2 := by have := enorm_mod3 zi; rw [hzi] at this; omega
  have hm₂3 : m₂ % 3 ≠ 2 := by have := enorm_mod3 zo; rw [hzo] at this; omega
  obtain ⟨a₁, b₁, c₁, hs₁, he₁, hp₁, hb₁⟩ := decode zi m₁ hzi (by omega) hri
  have hpos₁ := hp₁ (by omega)
  have hbal₁ := hb₁ h₁
  have hR₁ : Realises a₁ b₁ c₁ := hIH a₁ b₁ c₁
    (admissible_of_decoded hs₁ hpos₁ (by rw [he₁, hzi]) h₁odd hm₁3 h₁9) (by omega)
  obtain ⟨x, y, w, hs₂, he₂, hp₂, -⟩ := decode zo m₂ hzo (by omega) hro
  have hR₂ : Realises x y w := by
    rcases h₂ with h7 | h3
    · exact hIH x y w (admissible_of_decoded hs₂ (hp₂ h7) (by rw [he₂, hzo]) h₂odd hm₂3 h₂9)
        (by omega)
    · have hq := enorm_enc x y w
      rw [he₂, hzo, h3] at hq
      exact realises_norm3 (by omega) (by push_cast at hq ⊢; linarith)
  refine realises_of_factor (a₁ := a₁) (b₁ := b₁) (c₁ := c₁) (x := x) (y := y) (z := w) ?_ ?_ hR₁
    (by rw [hs₁]; exact hbal₁) hR₂
  · rw [he₁, he₂]; exact hzz
  · rw [hn, hs₁, hs₂, hmn]

/-- The squares `E(p)`, `p ≡ 2 (mod 3)` prime, described by their equations. -/
def SquaresRealised : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → p % 3 = 2 → ∀ a b c : ℕ, 3 * a + 2 * p = p * p → 3 * b = p * p + p →
    c = b → Realises a b c

theorem enorm_eq_one {w : ℤ × ℤ} (h : enorm w = 1) :
    w = (1, 0) ∨ w = (-1, 0) ∨ w = (0, 1) ∨ w = (0, -1) ∨ w = (1, 1) ∨ w = (-1, -1) := by
  obtain ⟨u, v⟩ := w
  obtain ⟨h1, h2, h3⟩ := sq_le_of_enorm (u, v)
  rw [h] at h1 h2 h3
  simp only at h1 h2 h3
  have hv : -1 ≤ v ∧ v ≤ 1 := by constructor <;> nlinarith
  have hu : -1 ≤ u ∧ u ≤ 1 := by constructor <;> nlinarith
  simp only [enorm] at h
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hu1, hu2⟩ := hu
  interval_cases u <;> interval_cases v <;> simp_all

theorem mod3_one_of {l : ℕ} (h1 : (l : ℤ) % 3 ≠ 2) (h2 : ¬ 3 ∣ l) : l % 3 = 1 := by omega

theorem seven_le_of {l : ℕ} (h1 : l ≠ 1) (h3 : l % 3 = 1) (h2 : l % 2 = 1) : 7 ≤ l := by omega

theorem lt_49_mul {l : ℕ} (h : 1 ≤ l) : l < 7 * (7 * l) := by omega

/-- **L165: the composite-order step.** -/
theorem descent_composite {n : ℕ} (hIH : SmallerRealised n) (hE : SquaresRealised)
    {a b c : ℕ} (hadm : AdmissibleProfile a b c) (hn : a + b + c = n) (h49 : 49 < n)
    (hcomp : ¬ n.Prime) : Realises a b c := by
  obtain ⟨ha, hb, hc, hmod, hq, -, -, -⟩ := hadm
  set z := enc a b c with hzdef
  have hzn : enorm z = n := by rw [hzdef, enorm_enc, hq]; exact_mod_cast hn
  have hzres : (z.1 + z.2 - n) % 3 = 0 := by
    have := enc_res a b c; rw [hn] at this; exact this
  have hodd : n % 2 = 1 := by omega
  have hn3 : n % 3 ≠ 2 := by omega
  by_cases h3 : 3 ∣ n
  · -- (i) the ramified prime
    obtain ⟨w, hw⟩ := split_three z (by rw [hzn]; exact_mod_cast h3)
    obtain ⟨k, hk⟩ := h3
    have hwn : enorm w = k := by
      have := enorm_mul (1, -1) w
      rw [← hw, hzn] at this
      have h3' : enorm ((1 : ℤ), (-1 : ℤ)) = 3 := by simp [enorm]
      rw [h3'] at this; push_cast [hk] at this; linarith
    refine realise_from_factors hIH hn (α := w) (β := (1, -1)) (by rw [← hzdef, hw, emul_comm])
      hwn (by simp [enorm]) (m₁ := k) (m₂ := 3) (by rw [hk]; ring) (Or.inr rfl)
      (by omega) (by omega) (by omega) (by omega) (Or.inr rfl) (by omega) rfl (by omega)
  · by_cases hin : ∃ p, p.Prime ∧ p ∣ n ∧ p % 3 = 2
    · -- (ii) an inert prime
      obtain ⟨p, hp, hpn, hp3⟩ := hin
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ := inert_dvd hp3 z (by rw [hzn]; exact_mod_cast hpn)
      set w : ℤ × ℤ := (u', v')
      have hzw : z = emul ((p : ℤ), 0) w := by
        simp only [emul, w]; ext <;> simp only [hu', hv'] <;> ring
      have hpodd : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h | h
        · subst h; omega
        · exact h
      have hp5 : 5 ≤ p := by
        have := hp.two_le; rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
        · omega
        · omega
        · omega
        · exact h
      have hnorm : enorm z = p * p * enorm w := by
        rw [hzw, enorm_mul]; simp only [enorm]; ring
      obtain ⟨m, hm⟩ : ∃ m : ℕ, enorm w = m :=
        ⟨(enorm w).toNat, (Int.toNat_of_nonneg (enorm_nonneg w)).symm⟩
      have hnm : n = p * p * m := by rw [hzn, hm] at hnorm; exact_mod_cast hnorm
      have hpp : (p * p) % 3 = 1 := by rw [Nat.mul_mod, hp3]
      have h1 : (a : ℤ) - c = p * u' := by rw [← hu', hzdef]; rfl
      have h2 : (b : ℤ) - c = p * v' := by rw [← hv', hzdef]; rfl
      have hres' : ((a : ℤ) - c + (b - c) - n) % 3 = 0 := by
        have := hzres; rw [hzdef] at this; exact this
      by_cases hm1 : m = 1
      · -- `z = p · unit`: the profile is a rotation of `E(p)`
        have hnp : n = p * p := by rw [hnm, hm1, mul_one]
        have hw1 : enorm w = 1 := by rw [hm, hm1]; rfl
        rcases enorm_eq_one hw1 with e | e | e | e | e | e <;>
          simp only [w, Prod.mk.injEq] at e <;> obtain ⟨rfl, rfl⟩ := e
        · exfalso; rw [h1, h2] at hres'; push_cast at hres'; omega
        · exact hE p hp hp5 hp3 a b c (by omega) (by omega) (by omega)
        · exfalso; rw [h1, h2] at hres'; push_cast at hres'; omega
        · exact realises_swap (hE p hp hp5 hp3 b a c (by omega) (by omega) (by omega))
        · exact realises_rotate (hE p hp hp5 hp3 c a b (by omega) (by omega) (by omega))
        · exfalso; rw [h1, h2] at hres'; push_cast at hres'; omega
      · have hm3 : m % 3 = 1 := by
          have := enorm_mod3 w; rw [hm] at this
          have : ¬ 3 ∣ m := fun h => h3 (by rw [hnm]; exact Dvd.dvd.mul_left h _)
          omega
        have hmodd : m % 2 = 1 := by
          have ho : Odd n := Nat.odd_iff.2 hodd
          rw [hnm] at ho
          exact Nat.odd_iff.1 (Nat.odd_mul.1 ho).2
        have hm7 : 7 ≤ m := by omega
        have hpp25 : 25 ≤ p * p := Nat.mul_le_mul hp5 hp5
        have hlt1 : p * p < n := by
          rw [hnm]; exact lt_mul_of_one_lt_right (by omega) (by omega)
        have hlt2 : m < n := by
          rw [hnm]; exact lt_mul_of_one_lt_left (by omega) (by omega)
        refine realise_from_factors hIH hn (α := ((p : ℤ), 0)) (β := w) hzw
          (by simp [enorm]; ring) hm (m₁ := p * p) (m₂ := m) hnm (Or.inl hpp) (by omega)
          hlt1 (by rw [Nat.mul_mod, hpodd]) (by omega) (Or.inl hm7) hlt2 hmodd (by omega)
    · by_cases hbig : ∃ p, p.Prime ∧ p ∣ n ∧ 13 ≤ p
      · -- (iii) a split prime `p ≥ 13`
        obtain ⟨p, hp, hpn, hp13⟩ := hbig
        haveI : Fact p.Prime := ⟨hp⟩
        have hp3 : p % 3 = 1 := by
          have h1 : p % 3 ≠ 2 := fun h => hin ⟨p, hp, hpn, h⟩
          have h0 : p % 3 ≠ 0 := by
            intro h
            have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
            rcases (Nat.dvd_prime hp).1 this with h' | h'
            · omega
            · exact h3 (h' ▸ hpn)
          omega
        obtain ⟨π, w, hπ, hzw⟩ := split_one hp3 z (by rw [hzn]; exact_mod_cast hpn)
        obtain ⟨m, hm⟩ : ∃ m : ℕ, enorm w = m :=
          ⟨(enorm w).toNat, (Int.toNat_of_nonneg (enorm_nonneg w)).symm⟩
        have hnm : n = p * m := by
          have := enorm_mul π w; rw [← hzw, hzn, hπ, hm] at this; exact_mod_cast this
        have hm1 : m ≠ 1 := by intro h; rw [h, mul_one] at hnm; exact hcomp (hnm ▸ hp)
        have hm3 : m % 3 = 1 := by
          have := enorm_mod3 w; rw [hm] at this
          have : ¬ 3 ∣ m := fun h => h3 (by rw [hnm]; exact Dvd.dvd.mul_left h _)
          omega
        have hmodd : m % 2 = 1 := by
          have ho : Odd n := Nat.odd_iff.2 hodd
          rw [hnm] at ho
          exact Nat.odd_iff.1 (Nat.odd_mul.1 ho).2
        have hpodd : p % 2 = 1 := by
          rcases hp.eq_two_or_odd with h | h
          · omega
          · exact h
        have hlt1 : p < n := by
          rw [hnm]; exact lt_mul_of_one_lt_right (by omega) (by omega)
        have hlt2 : m < n := by
          rw [hnm]; exact lt_mul_of_one_lt_left (by omega) (by omega)
        refine realise_from_factors hIH hn (α := π) (β := w) hzw hπ hm (m₁ := p) (m₂ := m) hnm
          (Or.inl hp3) hp13 hlt1 hpodd (by omega) (Or.inl (by omega)) hlt2 hmodd (by omega)
      · -- (iv) only the prime `7`
        have hseven : ∀ q, q.Prime → q ∣ n → q = 7 := by
          intro q hq hqn
          have hq13 : q < 13 := by by_contra h; exact hbig ⟨q, hq, hqn, by omega⟩
          have hq2 : q % 3 ≠ 2 := fun h => hin ⟨q, hq, hqn, h⟩
          have hq3 : q ≠ 3 := fun h => h3 (h ▸ hqn)
          have hqodd : q ≠ 2 := by rintro rfl; omega
          interval_cases q <;> first | rfl | omega | exact absurd hq (by decide)
        obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
        have h7n : 7 ∣ n := hseven q hq hqn ▸ hqn
        haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
        obtain ⟨π₁, w₁, hπ₁, hzw₁⟩ := split_one (p := 7) (by decide) z
          (by rw [hzn]; exact_mod_cast h7n)
        obtain ⟨k, hk⟩ := h7n
        have hw₁ : enorm w₁ = k := by
          have := enorm_mul π₁ w₁; rw [← hzw₁, hzn, hπ₁] at this
          push_cast [hk] at this; linarith
        have h7k : 7 ∣ k := by
          obtain ⟨q', hq', hq'k⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
          have := hseven q' hq' (hk ▸ Dvd.dvd.mul_left hq'k 7)
          exact this ▸ hq'k
        obtain ⟨π₂, w₂, hπ₂, hw₁w₂⟩ := split_one (p := 7) (by decide) w₁
          (by rw [hw₁]; exact_mod_cast h7k)
        obtain ⟨l, hl⟩ := h7k
        have hw₂ : enorm w₂ = l := by
          have := enorm_mul π₂ w₂; rw [← hw₁w₂, hw₁, hπ₂] at this
          push_cast [hl] at this; linarith
        have hl1 : l ≠ 1 := by intro h; rw [hk, hl, h] at h49; omega
        have hl3 : l % 3 = 1 := by
          have e1 := enorm_mod3 w₂
          rw [hw₂] at e1
          refine mod3_one_of e1 ?_
          intro h; apply h3; rw [hk, hl]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h _) _
        have hlodd : l % 2 = 1 := by
          have ho : Odd n := Nat.odd_iff.2 hodd
          rw [hk, hl] at ho
          exact Nat.odd_iff.1 (Nat.odd_mul.1 (Nat.odd_mul.1 ho).2).2
        refine realise_from_factors hIH hn (α := emul π₁ π₂) (β := w₂)
          (by rw [← hzdef, hzw₁, hw₁w₂, emul_assoc]) (by rw [enorm_mul, hπ₁, hπ₂]; norm_num)
          hw₂ (m₁ := 49) (m₂ := l) (by rw [hk, hl]; ring) (Or.inl rfl) (by norm_num)
          h49 rfl (by norm_num) (Or.inl (seven_le_of hl1 hl3 hlodd))
          (by rw [hk, hl]; exact lt_49_mul (Nat.pos_of_ne_zero (by rintro rfl; simp at hlodd)))
          hlodd (by intro h; rw [h] at hl3; norm_num at hl3)

end CDRBicolour.Descent
