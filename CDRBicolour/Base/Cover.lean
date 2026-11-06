/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CDRBicolour.Base.Witnesses
public import CDRBicolour.Universal
public meta import CDRBicolour.Base.Witnesses
public import CDRBicolour.Master.Equitable
public meta import CDRBicolour.Master.Equitable
public import CDRBicolour.Master.Cyclic

/-!
# The finite base `n < 5059`, reconstructed

`base_below5059`: every admissible profile of order `< 5059` is realised, given the uniform
branches of the route at their actual thresholds (Chetwynd–Hilton 1985, 6/7 (Palomar), for the equitable master criterion L159,
`BranchL157x1` = even largest class, `b = a + 1`, gap `c - b ≥ 2`, from order `508`, `BranchL168y` =
`b - a = 4` from `c - b ≥ 17`), the P2 route (CCJS, Plantholt 2004 with `c = 6/7`, `k ≥ 4`) and the large squares
`E(p)`.  Composite orders `> 49` are handled by the descent L165 inside the base; the 49 profiles
left are realised by kernel-checked Steiner-quasigroup witnesses (`Base/Data`).

The coverage of every sorted admissible profile `n < 5059` is a finite check over the gaps
`x = b - a`, `y = c - b < 72` (`gridOK`, checked by `decide +kernel`).
-/

@[expose] public section

namespace CDRBicolour.Base

open CDRBicolour.Prefix CDRBicolour.Descent

/-- `n = p²` for a prime `p ≡ 2 (mod 3)`. -/
def isEsq (n : ℕ) : Bool := Nat.sqrt n * Nat.sqrt n == n && decide (Nat.sqrt n).Prime &&
  Nat.sqrt n % 3 == 2

/-- The equitable master criterion of L159 (`Master.EqMasterHyp`) as a boolean, for the class
roles `(A, B, C)`. -/
def eqMasterB (A B C : ℕ) : Bool := decide (Master.EqMasterHyp A B C)

/-- **L157 + Chetwynd–Hilton** (ledger), only the family it is still needed for: even largest
class, `b = a + 1`, `c - b ≥ 2`, `n ≥ 508` (all other even-largest-class profiles with `c - b ≥ 2`
are covered by the equitable master criterion). -/
def BranchL157x1 : Prop :=
  ∀ a b c, AdmissibleProfile a b c → a ≤ b → b ≤ c → c % 2 = 0 → b = a + 1 → b + 2 ≤ c →
    508 ≤ a + b + c → 6 * c ≤ 7 * a → Realises a b c

/-- **L168** (ledger): odd largest class, `b - a = 4`, `c - b ≥ 43`. -/
def BranchL168y : Prop :=
  ∀ a b c, AdmissibleProfile a b c → a ≤ b → b ≤ c → c % 2 = 1 → b = a + 4 → b + 17 ≤ c →
    Realises a b c

/-- The squares `E(p)` of order `≥ 5059` (L160, gap `y = 0`). -/
def BigSquares : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → p % 3 = 2 → 5059 ≤ p * p → ∀ a b c : ℕ,
    3 * a + 2 * p = p * p → 3 * b = p * p + p → c = b → Realises a b c

/-- Coverage of a sorted profile. -/
def coverOK (a b c : ℕ) : Bool :=
  (decide (49 < a + b + c) && !decide (a + b + c).Prime && !isEsq (a + b + c)) ||
  (eqMasterB a b c || eqMasterB a c b || eqMasterB b a c || eqMasterB b c a ||
    eqMasterB c a b || eqMasterB c b a) ||
  (c % 2 == 0 && b == a + 1 && decide (b + 2 ≤ c) && decide (508 ≤ a + b + c) &&
    decide (6 * c ≤ 7 * a)) ||
  (c % 2 == 1 && b == a + 4 && decide (b + 17 ≤ c)) ||
  (c % 2 == 1 && b == a + 2 && (c - b) % 6 == 3 && decide (b + 27 ≤ c)) ||
  witnessList.contains (a, b, c)

/-! ### A kernel-reducible version of the coverage check

`Nat.Prime` and `Nat.sqrt` are defined by well-founded recursion and do not reduce in the kernel.
For orders `< 72²` primality is decided by trial division up to `71` (`primeB`), and the squares
`p²` by a search over `p < 72` (`isEsqB`); both are sound for the use made of them
(`primeB_of_prime`, `isEsqB_of_isEsq`), so the kernel check `gridOKK` implies the coverage. -/

/-- Trial division by the integers below `72`. -/
def primeB (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range 72).all fun m => decide (m < 2) || decide (n < m * m) || n % m != 0

/-- `n = p²` with `p < 72` prime, `p ≡ 2 (mod 3)`. -/
def isEsqB (n : ℕ) : Bool := (List.range 72).any fun p => p * p == n && primeB p && p % 3 == 2

theorem primeB_of_prime {n : ℕ} (hp : n.Prime) : primeB n = true := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨hp.two_le, fun m _ => ?_⟩
  by_cases h1 : m < 2
  · exact Or.inl (Or.inl h1)
  by_cases h2 : n < m * m
  · exact Or.inl (Or.inr h2)
  right
  intro h0
  rcases hp.eq_one_or_self_of_dvd m (Nat.dvd_of_mod_eq_zero h0) with h | h
  · omega
  · subst h
    have : 2 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
    omega

theorem isEsqB_of_isEsq {n : ℕ} (hn : n < 5059) (h : isEsq n = true) : isEsqB n = true := by
  simp only [isEsq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [isEsqB, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  refine ⟨Nat.sqrt n, ?_, ⟨⟨h1, primeB_of_prime h2⟩, h3⟩⟩
  by_contra hc
  push Not at hc
  have : 72 * 72 ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul hc hc
  omega

/-- The coverage with a given first (descent) disjunct. -/
def coverWith (d : Bool) (a b c : ℕ) : Bool :=
  d ||
  (eqMasterB a b c || eqMasterB a c b || eqMasterB b a c || eqMasterB b c a ||
    eqMasterB c a b || eqMasterB c b a) ||
  (c % 2 == 0 && b == a + 1 && decide (b + 2 ≤ c) && decide (508 ≤ a + b + c) &&
    decide (6 * c ≤ 7 * a)) ||
  (c % 2 == 1 && b == a + 4 && decide (b + 17 ≤ c)) ||
  (c % 2 == 1 && b == a + 2 && (c - b) % 6 == 3 && decide (b + 27 ≤ c)) ||
  witnessList.contains (a, b, c)

theorem coverOK_eq (a b c : ℕ) : coverOK a b c =
    coverWith (decide (49 < a + b + c) && !decide (a + b + c).Prime && !isEsq (a + b + c)) a b c :=
  rfl

theorem coverWith_mono {d₁ d₂ : Bool} {a b c : ℕ} (h : d₁ = true → d₂ = true)
    (h₁ : coverWith d₁ a b c = true) : coverWith d₂ a b c = true := by
  cases d₂ with
  | true => simp [coverWith]
  | false =>
    cases d₁ with
    | true => exact absurd (h rfl) (by simp)
    | false => exact h₁

/-- Coverage, kernel-reducible. -/
def coverOKK (a b c : ℕ) : Bool :=
  coverWith (decide (49 < a + b + c) && !primeB (a + b + c) && !isEsqB (a + b + c)) a b c

theorem coverOK_of_K {a b c : ℕ} (hn : a + b + c < 5059) (h : coverOKK a b c = true) :
    coverOK a b c = true := by
  rw [coverOK_eq]
  refine coverWith_mono (fun hd => ?_) h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hd ⊢
  refine ⟨⟨hd.1.1, ?_⟩, ?_⟩
  · rcases hpb : decide (a + b + c).Prime with _ | _
    · rfl
    · exact absurd (primeB_of_prime (of_decide_eq_true hpb)) (by rw [hd.1.2]; simp)
  · rcases hq : isEsq (a + b + c) with _ | _
    · rfl
    · exact absurd (isEsqB_of_isEsq hn hq) (by rw [hd.2]; simp)

/-- The finite coverage check over the gaps (kernel-reducible). -/
def gridOK : Bool :=
  (List.range 72).all fun x => (List.range 72).all fun y =>
    let n := x * x + x * y + y * y
    if n < 5059 && decide (2 * x + y < n) && (n - 2 * x - y) % 3 == 0 &&
        (n % 6 == 1 || n % 6 == 3) && !(x == 0 && y == 3 && n == 9) then
      coverOKK ((n - 2 * x - y) / 3) ((n - 2 * x - y) / 3 + x) ((n - 2 * x - y) / 3 + x + y)
    else true

theorem gridOK_eq : gridOK = true := by decide +kernel

theorem cover_of_sorted {a b c : ℕ} (h : AdmissibleProfile a b c) (hab : a ≤ b) (hbc : b ≤ c)
    (hn : a + b + c < 5059) : coverOK a b c = true := by
  have hg := order_gaps h hab hbc
  obtain ⟨ha, -, -, hm, -, e1, -⟩ := h
  set x := b - a with hx
  set y := c - b with hy
  have hx72 : x < 72 := by
    by_contra hc; push_neg at hc
    have : 72 * 72 ≤ x ^ 2 := by rw [sq]; exact Nat.mul_le_mul hc hc
    omega
  have hy72 : y < 72 := by
    by_contra hc; push_neg at hc
    have : 72 * 72 ≤ y ^ 2 := by rw [sq]; exact Nat.mul_le_mul hc hc
    omega
  have hall := List.all_eq_true.1 (List.all_eq_true.1 gridOK_eq x (List.mem_range.2 hx72)) y
    (List.mem_range.2 hy72)
  have hn' : x * x + x * y + y * y = a + b + c := by rw [hg]; ring
  simp only [hn'] at hall
  have ha' : (a + b + c - 2 * x - y) / 3 = a := by omega
  have hex : (x == 0 && y == 3 && a + b + c == 9) = false := by
    rcases h0 : (x == 0 && y == 3 && a + b + c == 9) with _ | _
    · rfl
    · exfalso
      simp only [Bool.and_eq_true, beq_iff_eq] at h0
      exact e1 ⟨by omega, by omega⟩
  have hcond : (decide (a + b + c < 5059) && decide (2 * x + y < a + b + c) &&
      (a + b + c - 2 * x - y) % 3 == 0 && ((a + b + c) % 6 == 1 || (a + b + c) % 6 == 3) &&
      !(x == 0 && y == 3 && a + b + c == 9)) = true := by
    rw [hex]
    simp only [Bool.not_false, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.or_eq_true]
    exact ⟨⟨⟨hn, by omega⟩, by omega⟩, hm⟩
  rw [if_pos hcond, ha', show a + x = b by omega, show b + y = c by omega] at hall
  exact coverOK_of_K hn hall

/-- `y ≡ 3 (mod 6)` with `b - a = 2` gives a term of `P2`. -/
theorem p2_of_gaps {a b c : ℕ} (h : AdmissibleProfile a b c) (hab : b = a + 2) (hbc : b ≤ c)
    (hy : (c - b) % 6 = 3) (hy33 : b + 27 ≤ c) :
    ∃ k, 4 ≤ k ∧ a = pa k ∧ b = pb k ∧ c = pc k := by
  have hn := order_gaps h (by omega) hbc
  obtain ⟨y, hyc⟩ : ∃ y, c = b + y := ⟨c - b, by omega⟩
  rw [show b - a = 2 by omega, show c - b = y by omega] at hn
  have h3a : 3 * a = y * (y + 1) := by
    have : y * (y + 1) = y ^ 2 + y := by ring
    nlinarith
  obtain ⟨k, hk⟩ : ∃ k, y = 6 * k + 3 := ⟨y / 6, by omega⟩
  subst hk
  refine ⟨k, by omega, ?_, ?_, ?_⟩
  · simp only [pa]; nlinarith
  · simp only [pb]; nlinarith
  · simp only [pc]; nlinarith

section Dispatch

variable (h157 : BranchL157x1) (h168 : BranchL168y)
include h157 h168

/-- Every covering reason except the descent realises the profile directly. -/
theorem dispatch {a b c : ℕ} (h : AdmissibleProfile a b c) (hab : a ≤ b) (hbc : b ≤ c)
    (hcov : coverOK a b c = true)
    (hnd : ¬ (49 < a + b + c ∧ ¬ (a + b + c).Prime ∧ isEsq (a + b + c) = false)) :
    Realises a b c := by
  simp only [coverOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, beq_iff_eq] at hcov
  rcases hcov with ((((hL | hm) | h57) | h68) | hp2) | hw
  · exact absurd ⟨hL.1.1, hL.1.2, hL.2⟩ hnd
  · rcases hm with ((((m1 | m2) | m3) | m4) | m5) | m6
    · exact Master.eqMaster_realises h (of_decide_eq_true m1)
    · exact realises_swap23 (Master.eqMaster_realises (admissible_swap (admissible_rotate
        (admissible_rotate h))) (of_decide_eq_true m2))
    · exact realises_swap (Master.eqMaster_realises (admissible_swap h) (of_decide_eq_true m3))
    · exact realises_rotate (realises_rotate (Master.eqMaster_realises (admissible_rotate h) (of_decide_eq_true m4)))
    · exact realises_rotate (Master.eqMaster_realises (admissible_rotate (admissible_rotate h)) (of_decide_eq_true m5))
    · exact realises_rotate (realises_rotate (realises_swap (Master.eqMaster_realises
        (admissible_swap (admissible_rotate h)) (of_decide_eq_true m6))))
  · exact h157 a b c h hab hbc h57.1.1.1.1 h57.1.1.1.2 h57.1.1.2 h57.1.2 h57.2
  · exact h168 a b c h hab hbc h68.1.1 h68.1.2 h68.2
  · obtain ⟨k, hk5, rfl, rfl, rfl⟩ := p2_of_gaps h hp2.1.1.2 hbc hp2.1.2 hp2.2
    exact P2_realises' k hk5
  · exact witness_realises _ (List.contains_iff_mem.1 hw)

/-- The squares `E(p)`, small ones from the base coverage, large ones from `BigSquares`. -/
theorem squares_of (hBig : BigSquares) : SquaresRealised := by
  intro p hp hp5 hp3 a b c ha hb hc
  by_cases hbig : 5059 ≤ p * p
  · exact hBig p hp hp5 hp3 hbig a b c ha hb hc
  rw [hc]
  have hp6 : p % 6 = 5 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · omega
  have hsum : a + b + b = p * p := by omega
  have hadm : AdmissibleProfile a b b := by
    have ha5 : 5 ≤ a := by nlinarith
    refine ⟨by omega, by omega, by omega, ?_, ?_, by omega, by omega, by omega⟩
    · left; rw [hsum, Nat.mul_mod, hp6]
    · have e1 : (3 : ℤ) * a + 2 * p = p * p := by exact_mod_cast ha
      have e2 : (3 : ℤ) * b = p * p + p := by exact_mod_cast hb
      have hba : (b : ℤ) = a + p := by linarith
      rw [hba]; push_cast; nlinarith
  have hcov := cover_of_sorted hadm (by omega) le_rfl (by omega)
  refine dispatch h157 h168 hadm (by omega) le_rfl hcov ?_
  rintro ⟨-, -, hE⟩
  have : isEsq (a + b + b) = true := by
    rw [hsum]
    simp only [isEsq, Nat.sqrt_eq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨trivial, hp⟩, hp3⟩
  rw [this] at hE; exact Bool.noConfusion hE

/-- **The finite base, reconstructed.** -/
theorem base_below5059 (hBig : BigSquares) : BaseBelow5059 := by
  have hE := squares_of h157 h168 hBig
  suffices H : ∀ n, n < 5059 → ∀ a b c, AdmissibleProfile a b c → a + b + c = n →
      Realises a b c by
    intro a b c h hn; exact H _ hn a b c h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  have hIH : SmallerRealised n := fun a' b' c' h' hlt => ih _ hlt (by omega) a' b' c' h' rfl
  refine realises_of_sorted fun a b c h hab hbc hsum => ?_
  have hcov := cover_of_sorted h hab hbc (by omega)
  by_cases hd : 49 < a + b + c ∧ ¬ (a + b + c).Prime ∧ isEsq (a + b + c) = false
  · exact descent_composite hIH hE h hsum (by omega) (hsum ▸ hd.2.1)
  · exact dispatch h157 h168 h hab hbc hcov hd

end Dispatch

end CDRBicolour.Base
