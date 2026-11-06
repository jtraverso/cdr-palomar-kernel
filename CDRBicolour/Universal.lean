/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Descent.L165
public import CDRBicolour.P2RouteClosed

/-!
# The full CDR theorem along the candidate route

`cdr_conjecture_of_route`: the Colbourn–Dinitz–Rosa conjecture (`CDRConjecture`) follows from

* the external, published input `CH1985_OneFactor` (Chetwynd–Hilton 1985), stated literally (L183;
  CCJS 1.2 and Plantholt 2004 Theorem 1.2 are proved via their Palomar formalizations);
* the registered finite base `BaseBelow5059` (historical inventory, witnesses not bundled);
* the earlier branches of the route, stated exactly as in the ledger for orders `n ≥ 5059`:
  `BranchL160` (largest class even), `BranchL161` (largest odd, `b - a ≥ 6`),
  `BranchL168` (largest odd, `b - a = 4`).

Everything else is proved here: strong induction on the order; sorting (invariance under
permutations); parity (`c` odd forces `a, b` even); composite orders by the descent L165
(with the squares `E(p)` from L160 or the base); prime orders with `b - a = 2` are exactly the
family `P2(k)`, closed by L181–L184 (`P2_realises'`); `b - a = 0` gives a square order.
-/

@[expose] public section

namespace CDRBicolour

open CDRBicolour.Descent CDRBicolour.Prefix

/-- The registered finite base: every admissible profile of order `< 5059` is realised. -/
def BaseBelow5059 : Prop :=
  ∀ a b c, AdmissibleProfile a b c → a + b + c < 5059 → Realises a b c

/-- L160 (ledger): sorted admissible profiles with even largest class, `n ≥ 5059`. -/
def BranchL160 : Prop :=
  ∀ a b c, AdmissibleProfile a b c → a ≤ b → b ≤ c → c % 2 = 0 → 5059 ≤ a + b + c →
    Realises a b c

/-- L161 (ledger): largest class odd and `b - a ≥ 6`, `n ≥ 5059`. -/
def BranchL161 : Prop :=
  ∀ a b c, AdmissibleProfile a b c → a ≤ b → b ≤ c → c % 2 = 1 → a + 6 ≤ b →
    5059 ≤ a + b + c → Realises a b c

/-- L168 (ledger): largest class odd and `b - a = 4`, `n ≥ 5059`. -/
def BranchL168 : Prop :=
  ∀ a b c, AdmissibleProfile a b c → a ≤ b → b ≤ c → c % 2 = 1 → b = a + 4 →
    5059 ≤ a + b + c → Realises a b c

theorem admissible_rotate {a b c : ℕ} (h : AdmissibleProfile a b c) : AdmissibleProfile b c a := by
  obtain ⟨ha, hb, hc, hm, hq, e1, e2, e3⟩ := h
  refine ⟨hb, hc, ha, by omega, by push_cast; linear_combination hq, e3, ?_, ?_⟩
  · rintro ⟨h1, h2⟩; exact e1 ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact e2 ⟨h2, h1⟩

theorem admissible_swap {a b c : ℕ} (h : AdmissibleProfile a b c) : AdmissibleProfile b a c := by
  obtain ⟨ha, hb, hc, hm, hq, e1, e2, e3⟩ := h
  refine ⟨hb, ha, hc, by omega, by push_cast; linear_combination hq, ?_, e3, e2⟩
  rintro ⟨h1, h2⟩; exact e1 ⟨h2, h1⟩

theorem realises_swap23 {a b c : ℕ} (h : Realises a b c) : Realises a c b :=
  realises_rotate (realises_swap h)

/-- Sorting (the order is carried along). -/
theorem realises_of_sorted {n : ℕ}
    (H : ∀ a b c, AdmissibleProfile a b c → a ≤ b → b ≤ c → a + b + c = n → Realises a b c) :
    ∀ a b c, AdmissibleProfile a b c → a + b + c = n → Realises a b c := by
  intro a b c h hn
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac
  · exact H a b c h hab hbc hn
  · exact H a b c h hab hbc hn
  · exact realises_swap23 (H a c b (admissible_swap (admissible_rotate
      (admissible_rotate h))) hac hbc (by omega))
  · exact realises_rotate (H c a b (admissible_rotate (admissible_rotate h)) hac hab (by omega))
  · exact realises_swap (H b a c (admissible_swap h) hab hac (by omega))
  · exact realises_rotate (realises_rotate (H b c a (admissible_rotate h) hbc hac (by omega)))
  · exact realises_swap (H b a c (admissible_swap h) hab hac (by omega))
  · exact realises_rotate (realises_rotate (realises_swap (H c b a
      (admissible_swap (admissible_rotate h)) hbc hab (by omega))))

/-- Parity: an odd largest class forces the other two classes even. -/
theorem even_of_odd {a b c : ℕ} (h : AdmissibleProfile a b c) (hc : c % 2 = 1) :
    a % 2 = 0 ∧ b % 2 = 0 := by
  obtain ⟨-, -, -, -, hq, -⟩ := h
  have h2 := congrArg (fun x : ℤ => (x : ZMod 2)) hq
  push_cast at h2
  have hc' : ((c : ℕ) : ZMod 2) = 1 := by
    rw [show c = 2 * (c / 2) + 1 by omega]; push_cast
    rw [show (2 : ZMod 2) = 0 from rfl]; ring
  rw [hc'] at h2
  have key : ∀ x y : ZMod 2, x ^ 2 + y ^ 2 + 1 ^ 2 - x * y - x * 1 - y * 1 = x + y + 1 →
      x = 0 ∧ y = 0 := by decide
  obtain ⟨h1, h2'⟩ := key _ _ h2
  have e1 := (ZMod.natCast_eq_zero_iff a 2).1 h1
  have e2 := (ZMod.natCast_eq_zero_iff b 2).1 h2'
  omega

/-- For a sorted profile, `n = x² + x y + y²` with the two gaps. -/
theorem order_gaps {a b c : ℕ} (h : AdmissibleProfile a b c) (hab : a ≤ b) (hbc : b ≤ c) :
    a + b + c = (b - a) ^ 2 + (b - a) * (c - b) + (c - b) ^ 2 := by
  obtain ⟨-, -, -, -, hq, -⟩ := h
  zify [hab, hbc]
  linear_combination -hq

/-- A prime order with `b - a = 2` and odd `c` is a term of `P2`. -/
theorem p2_of_prime {a b c : ℕ} (h : AdmissibleProfile a b c) (hab : b = a + 2) (hbc : b ≤ c)
    (hc : c % 2 = 1) (hp : (a + b + c).Prime) (h5 : 5059 ≤ a + b + c) :
    ∃ k, 5 ≤ k ∧ a = pa k ∧ b = pb k ∧ c = pc k := by
  have hn := order_gaps h (by omega) hbc
  obtain ⟨y, hy⟩ : ∃ y, c = b + y := ⟨c - b, by omega⟩
  rw [show b - a = 2 by omega, show c - b = y by omega] at hn
  have hsum : a + b + c = 3 * a + 4 + y := by omega
  have h3a : 3 * a = y * (y + 1) := by
    have : y * (y + 1) = y ^ 2 + y := by ring
    nlinarith
  have hn3 : ¬ 3 ∣ a + b + c := by
    intro h3
    have := Nat.Prime.eq_one_or_self_of_dvd hp 3 h3; omega
  have hy3 : 3 ∣ y := by
    have : 3 ∣ y * (y + 1) := ⟨a, by omega⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 this with h | h
    · exact h
    · exfalso; apply hn3
      obtain ⟨j, hj⟩ := h
      have hsq : (y + 1) * (y + 1) = (3 * j) * (3 * j) := by rw [hj]
      exact ⟨3 * j * j + 1, by rw [hn]; nlinarith⟩
  have hyodd : y % 2 = 1 := by
    have := even_of_odd h hc; omega
  obtain ⟨k, hk⟩ : ∃ k, y = 6 * k + 3 := ⟨y / 6, by omega⟩
  subst hk
  refine ⟨k, ?_, ?_, ?_, ?_⟩
  · by_contra hlt; push_neg at hlt
    have hk4 : k ≤ 4 := by omega
    have : a + b + c ≤ 2 ^ 2 + 2 * (6 * 4 + 3) + (6 * 4 + 3) ^ 2 := by
      rw [hn]; gcongr
    omega
  · simp only [pa]; nlinarith
  · simp only [pb]; nlinarith
  · simp only [pc]; nlinarith

/-- The squares `E(p)` from L160 or the base. -/
theorem squaresRealised (hBase : BaseBelow5059) (hL160 : BranchL160) : SquaresRealised := by
  intro p hp hp5 hp3 a b c ha hb hc
  rw [hc]
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hp6 : p % 6 = 5 := by omega
  have ha5 : 5 ≤ a := by nlinarith
  have hsum : a + b + b = p * p := by omega
  have hadm : AdmissibleProfile a b b := by
    refine ⟨by omega, by omega, by omega, ?_, ?_, by omega, by omega, by omega⟩
    · left; rw [hsum, Nat.mul_mod, hp6]
    · have e1 : (3 : ℤ) * a + 2 * p = p * p := by exact_mod_cast ha
      have e2 : (3 : ℤ) * b = p * p + p := by exact_mod_cast hb
      have hba : (b : ℤ) = a + p := by linarith
      rw [hba]; push_cast; nlinarith
  have hb2 : b % 2 = 0 := by
    obtain ⟨j, hj⟩ : 6 ∣ p + 1 := by omega
    have : 3 * b = 3 * (2 * (p * j)) := by rw [hb]; nlinarith
    omega
  by_cases hsmall : a + b + b < 5059
  · exact hBase a b b hadm hsmall
  · exact hL160 a b b hadm (by omega) le_rfl hb2 (by omega)

theorem not_prime_sq {y : ℕ} (h : 4 ≤ y * y) : ¬ (y * y).Prime := by
  intro hp
  rcases Nat.Prime.eq_one_or_self_of_dvd hp y (dvd_mul_right y y) with h1 | h1
  · subst h1; omega
  · have : y * 1 = y * y := by rw [mul_one]; exact h1
    have hy : 0 < y := by rcases Nat.eq_zero_or_pos y with h0 | h0 <;> [simp [h0] at h; exact h0]
    have := Nat.eq_of_mul_eq_mul_left hy this
    subst this; omega

/-- **The CDR conjecture along the candidate route.** -/
theorem cdr_conjecture_of_route (hBase : BaseBelow5059) (hL160 : BranchL160)
    (hL161 : BranchL161) (hL168 : BranchL168)
    : CDRConjecture := by
  have hE := squaresRealised hBase hL160
  suffices H : ∀ n, ∀ a b c, AdmissibleProfile a b c → a + b + c = n → Realises a b c by
    intro a b c h; exact H _ a b c h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hIH : SmallerRealised n := fun a' b' c' h' hlt => ih _ hlt a' b' c' h' rfl
  refine realises_of_sorted fun a b c h hab hbc hn => ?_
  by_cases hsmall : a + b + c < 5059
  · exact hBase a b c h hsmall
  push_neg at hsmall
  by_cases hce : c % 2 = 0
  · exact hL160 a b c h hab hbc hce hsmall
  have hco : c % 2 = 1 := by omega
  obtain ⟨ha2, hb2⟩ := even_of_odd h hco
  by_cases h6 : a + 6 ≤ b
  · exact hL161 a b c h hab hbc hco h6 hsmall
  by_cases h4 : b = a + 4
  · exact hL168 a b c h hab hbc hco h4 hsmall
  have hx : b = a ∨ b = a + 2 := by omega
  by_cases hprime : n.Prime
  · rcases hx with hx | hx
    · exfalso
      have hg := order_gaps h hab hbc
      rw [show b - a = 0 by omega] at hg
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, zero_add] at hg
      rw [← hn, hg, sq] at hprime
      exact not_prime_sq (by nlinarith) hprime
    · obtain ⟨k, hk5, rfl, rfl, rfl⟩ := p2_of_prime h hx hbc hco (hn ▸ hprime) hsmall
      exact P2_realises' k (by omega)
  · exact descent_composite hIH hE h hn (by omega) hprime

end CDRBicolour
